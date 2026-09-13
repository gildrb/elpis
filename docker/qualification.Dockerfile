# Build-only source qualification artifact. Never selected by serving Compose.
FROM lmsysorg/sglang@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9
COPY patches/ /opt/qwen-qualification/patches/
# Authenticate the actual stock source before an overlay can hide it.
RUN /opt/sglang/bin/python3 /opt/qwen-qualification/patches/chain.py \
      --bundle /opt/qwen-qualification/patches \
      --manifest-sha256 b8bb8e83b57dbdb01acf121bf640b2447c9cd3bf13849198d02b8aef443396a2 \
      --image lmsysorg/sglang@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9 \
      --mode original --root /sgl-workspace/sglang/python/sglang
# The verifier creates a new owned output tree; it never patches user roots.
RUN /opt/sglang/bin/python3 /opt/qwen-qualification/patches/chain.py \
      --bundle /opt/qwen-qualification/patches \
      --manifest-sha256 b8bb8e83b57dbdb01acf121bf640b2447c9cd3bf13849198d02b8aef443396a2 \
      --image lmsysorg/sglang@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9 \
      --exclusive-build-tree --mode overlay --root /opt/qwen-qualification/source
# Installation is restricted to this exclusively owned disposable image layer.
RUN cp -r /opt/qwen-qualification/source/. /sgl-workspace/sglang/python/sglang/ && \
    /opt/sglang/bin/python3 /opt/qwen-qualification/patches/chain.py \
      --bundle /opt/qwen-qualification/patches \
      --manifest-sha256 b8bb8e83b57dbdb01acf121bf640b2447c9cd3bf13849198d02b8aef443396a2 \
      --image lmsysorg/sglang@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9 \
      --mode final --root /sgl-workspace/sglang/python/sglang
# This image cannot launch serving through its default command.
ENTRYPOINT ["/opt/sglang/bin/python3", "/opt/qwen-qualification/patches/chain.py", "--bundle", "/opt/qwen-qualification/patches", "--manifest-sha256", "b8bb8e83b57dbdb01acf121bf640b2447c9cd3bf13849198d02b8aef443396a2", "--image", "lmsysorg/sglang@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9", "--mode", "final", "--root", "/sgl-workspace/sglang/python/sglang"]
CMD []
