import hashlib, json, time
from pathlib import Path
import torch
torch.set_default_dtype(torch.bfloat16)
from safetensors import safe_open
from sglang.srt.layers.packed_w8_embedding import PackedW8Embedding

packed_root = Path("/packed"); dense_root = Path("/dense"); out = Path("/out/result.json")
CHUNK = 512

def index_map(root):
    idx = json.loads((root/"model.safetensors.index.json").read_text())
    return idx["weight_map"], idx["metadata"]["total_size"]

pmap, ptotal = index_map(packed_root)
dmap, dtotal = index_map(dense_root)
pk = {n: pmap["model.language_model.embed_tokens." + n] for n in ("weight_packed", "weight_scale", "weight_shape")}
dd = dmap["model.language_model.embed_tokens.weight"]
print("packed shards:", pk, "dense shard:", dd, flush=True)

mod = PackedW8Embedding()
for n, shard in pk.items():
    with safe_open(str(packed_root/shard), framework="pt", device="cpu") as f:
        mod.load_tensor(n, f.get_tensor("model.language_model.embed_tokens." + n))
mod.finish_loading()

bad = 0; rows = 0; t0 = time.time()
dense_sha = hashlib.sha256(); packed_sha = hashlib.sha256()
for start in range(0, mod.num_embeddings, CHUNK):
    ids = torch.arange(start, min(start+CHUNK, mod.num_embeddings), dtype=torch.int64)
    got = mod.forward(ids)
    with safe_open(str(dense_root/dd), framework="pt", device="cpu") as f:
        sl = f.get_slice("model.language_model.embed_tokens.weight")
        ref = sl[start:start+ids.numel(), :]
        ref = ref.get_tensor() if hasattr(ref, "get_tensor") else torch.tensor(ref)
    if got.dtype != ref.dtype or got.shape != ref.shape:
        bad += 1; break
    g = got.view(torch.int16).reshape(-1); r = ref.view(torch.int16).reshape(-1)
    packed_sha.update(g.contiguous().numpy().tobytes()); dense_sha.update(r.contiguous().numpy().tobytes())
    if not torch.equal(g, r):
        bad += 1
    rows += ids.numel()
res = {
    "schema_version": 1,
    "status": "completed" if bad == 0 and rows == mod.num_embeddings else "mismatch",
    "rows_compared": rows, "mismatched_chunks": bad,
    "bit_exact_int16": bad == 0,
    "packed_flow_sha256": packed_sha.hexdigest(),
    "dense_reference_sha256": dense_sha.hexdigest(),
    "packed_index_total_size": ptotal, "dense_index_total_size": dtotal,
    "chunk_rows": CHUNK, "seconds": round(time.time()-t0, 3),
    "scope": "CPU module forward vs dense artifact rows; no GPU/no model serving",
}
out.write_text(json.dumps(res, indent=2))
print(json.dumps(res), flush=True)
