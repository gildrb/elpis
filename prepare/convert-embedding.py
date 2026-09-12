import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import torch
from safetensors import safe_open
from safetensors.torch import save_file
from compressed_tensors.compressors import PackedQuantizationCompressor
from compressed_tensors.quantization import QuantizationScheme

source = Path('/source')
destination = Path('/work/artifact')
destination.mkdir(mode=0o700, exist_ok=False)
torch.set_num_threads(4)
if list(Path('/dev').glob('nvidia*')):
    raise RuntimeError('NVIDIA device exposed')

def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            value.update(block)
    return value.hexdigest()

def tensor_digest(tensor: torch.Tensor) -> str:
    return hashlib.sha256(tensor.contiguous().view(torch.uint8).numpy().tobytes()).hexdigest()

config = json.loads((source / 'config.json').read_text())
quant = json.loads((source / 'quantization_config.json').read_text())
index = json.loads((source / 'model.safetensors.index.json').read_text())
original_index = copy.deepcopy(index)
prefix = 'model.language_model.embed_tokens.'
keys = {prefix + suffix for suffix in ('weight_packed', 'weight_scale', 'weight_shape')}
if {key for key in index['weight_map'] if 'embed_tokens' in key} != keys:
    raise ValueError('Unexpected embedding keys')
if config['tie_word_embeddings'] is not False or config['text_config']['tie_word_embeddings'] is not False:
    raise ValueError('Tied embeddings unsupported')
groups = config['quantization_config']['config_groups']
if groups['group_2']['targets'] != ['re:.*embed_tokens$']:
    raise ValueError('Unexpected embedding group')
scheme = QuantizationScheme.model_validate(groups['group_2'])
w = scheme.weights
if w is None or w.num_bits != 8 or w.group_size != 128 or w.symmetric is not True or w.dynamic is not False or w.strategy != 'group' or w.type != 'int' or w.actorder is not None:
    raise ValueError('Unexpected embedding scheme')
shards = {index['weight_map'][key] for key in keys}
if len(shards) != 1:
    raise ValueError('Embedding spans shards')
shard = next(iter(shards))
files = sorted(source.iterdir())
if not all(path.is_file() and not path.is_symlink() for path in files):
    raise ValueError('Unexpected source entry')
manifest = {'source': str(source), 'source_hashes': {}, 'output_hashes': {}, 'unchanged_tensors': {}, 'native_version': 'compressed-tensors 0.18.0'}
for path in files:
    manifest['source_hashes'][path.name] = digest(path)
print('Source hashes complete', flush=True)
actual = {}
total = 0
for name in sorted(set(index['weight_map'].values())):
    if Path(name).name != name:
        raise ValueError('Unsafe shard path')
    with safe_open(source / name, framework='pt', device='cpu') as handle:
        for key in handle.keys():
            if key in actual:
                raise ValueError('Duplicate tensor')
            actual[key] = name
            t = handle.get_tensor(key)
            total += t.numel() * t.element_size()
if actual != index['weight_map']:
    raise ValueError('Index tensor mapping mismatch')
manifest['source_actual_tensor_bytes'] = total
manifest['source_declared_size_stale'] = total != index['metadata']['total_size']
print(f'Inventory validated: {total} actual bytes; source declared {index["metadata"]["total_size"]}', flush=True)
with safe_open(source / shard, framework='pt', device='cpu') as handle:
    metadata = handle.metadata()
    tensors = {key: handle.get_tensor(key) for key in handle.keys()}
packed = tensors[prefix + 'weight_packed']
scale = tensors[prefix + 'weight_scale']
shape = tensors[prefix + 'weight_shape']
rows = config['text_config']['vocab_size']
cols = config['text_config']['hidden_size']
if type(rows) is not int or type(cols) is not int or rows <= 0 or cols <= 0 or cols % 128 != 0:
    raise ValueError('Invalid configuration shape')
if shape.dtype != torch.int64 or tuple(shape.shape) != (2,) or shape.tolist() != [rows, cols]:
    raise ValueError('Invalid weight_shape')
if packed.dtype != torch.int32 or tuple(packed.shape) != (rows, cols // 4):
    raise ValueError('Invalid packed tensor')
if scale.dtype != torch.bfloat16 or tuple(scale.shape) != (rows, cols // 128) or not torch.isfinite(scale).all().item() or not (scale > 0).all().item():
    raise ValueError('Invalid scales')
dense = torch.empty((rows, cols), dtype=torch.bfloat16)
for start in range(0, rows, 256):
    stop = min(start + 256, rows)
    p = packed[start:stop]
    s = scale[start:stop]
    result = PackedQuantizationCompressor.decompress({'weight_packed': p, 'weight_scale': s, 'weight_shape': torch.tensor([stop-start, cols], dtype=torch.int64)}, scheme)['weight']
    reference = torch.empty((stop-start, cols), dtype=torch.float32)
    for offset in range(4):
        reference[:, offset::4] = ((p >> (offset * 8)) & 255).to(torch.float32) - 128
    reference = (reference.reshape(stop-start, cols//128, 128) * s.float().unsqueeze(-1)).reshape(stop-start, cols).to(torch.bfloat16)
    if result.dtype != torch.bfloat16 or not torch.equal(result.view(torch.int16), reference.view(torch.int16)) or not torch.isfinite(result).all().item():
        raise ValueError(f'Native/reference mismatch at row {start}')
    dense[start:stop] = result
print('All rows exact reference match', flush=True)
old_bytes = sum(tensors[key].numel() * tensors[key].element_size() for key in keys)
for key in keys:
    del tensors[key]
    del index['weight_map'][key]
newkey = prefix + 'weight'
tensors[newkey] = dense
index['weight_map'][newkey] = shard
index['metadata']['total_size'] = total + dense.numel()*2 - old_bytes
for key, tensor in tensors.items():
    if key != newkey:
        manifest['unchanged_tensors'][key] = tensor_digest(tensor)
if set(quant['config_groups']) != {'group_0'} or quant['config_groups']['group_0']['targets'] != ['Linear']:
    raise ValueError('Unexpected standalone quantization config')
manifest['standalone_quantization_config'] = 'Original generic Linear-only metadata preserved byte-for-byte; no embedding group exists there'
del config['quantization_config']['config_groups']['group_2']
changed = {'config.json', 'model.safetensors.index.json', shard}
for path in files:
    if path.name not in changed:
        with path.open('rb') as incoming, (destination/path.name).open('xb') as outgoing:
            shutil.copyfileobj(incoming, outgoing, 8*1024*1024)
for name, document in [('config.json', config), ('model.safetensors.index.json', index)]:
    with (destination/name).open('x') as stream:
        json.dump(document, stream, indent=2)
# Reserve the filename exclusively before the native writer touches our own inode.
with (destination/shard).open('xb'):
    pass
save_file(tensors, str(destination/shard), metadata=metadata)
with safe_open(destination/shard, framework='pt', device='cpu') as handle:
    if set(handle.keys()) != set(tensors):
        raise ValueError('Output shard key mismatch')
    for key in handle.keys():
        if tensor_digest(handle.get_tensor(key)) != tensor_digest(tensors[key]):
            raise ValueError('Output tensor bytes differ')
for path in files:
    if digest(path) != manifest['source_hashes'][path.name]:
        raise ValueError('Source changed during conversion')
    output = destination/path.name
    result_hash = digest(output)
    manifest['output_hashes'][path.name] = result_hash
    if path.name not in changed and result_hash != manifest['source_hashes'][path.name]:
        raise ValueError('Unrelated file changed')
    output.chmod(0o444)
manifest.update({'rows_checked': rows, 'values_checked': rows*cols, 'reference': 'byte extraction, minus128, FP32 scale product, BF16 cast; bit-exact all rows', 'dense_embedding_sha256': tensor_digest(dense), 'dense_bytes': rows*cols*2, 'original_embedding_bytes': old_bytes, 'additional_weight_bytes': rows*cols*2-old_bytes, 'index_total_size': index['metadata']['total_size'], 'source_index_total_size': original_index['metadata']['total_size']})
with Path('/work/validation.json').open('x') as stream:
    json.dump(manifest, stream, indent=2)
destination.chmod(0o555)
print(json.dumps({k:v for k,v in manifest.items() if k not in ('source_hashes','output_hashes','unchanged_tensors')}), flush=True)
