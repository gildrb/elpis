# Digest-pinned runtime plus the Qwen packed-embedding/KVarN experimental series.
# Native262144 with full verify and commit graphs remains an unqualified candidate.
# Bend 2.0.20 only. The original release checker/compiler is a build dependency;
# the serving layer receives the proved program and its reproducible evidence.
FROM lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9 AS bend-toolchain
ENV BEND_NO_TELEMETRY=1
RUN apt-get update && \
    apt-get install -y --no-install-recommends clang-19 util-linux patch && \
    rm -rf /var/lib/apt/lists/*
COPY bend/build_toolchain.py /tmp/bend-toolchain/
COPY patches/bend2-stack-safe-2.0.20.patch /tmp/bend-toolchain/
RUN curl --proto '=https' --tlsv1.2 -fsSL \
      https://github.com/bendlang/bend/releases/download/v2.0.20/bend-2.0.20-linux-x64.tar.gz \
      -o /tmp/bend.tar.gz && \
    curl --proto '=https' --tlsv1.2 -fsSL \
      https://codeload.github.com/bendlang/bend/tar.gz/a5269a6b2c5ccd6752b66df4bc6f60678b4f49bc \
      -o /tmp/bend-source.tar.gz && \
    python3 /tmp/bend-toolchain/build_toolchain.py build \
      /tmp/bend.tar.gz \
      /tmp/bend-source.tar.gz \
      /tmp/bend-toolchain/bend2-stack-safe-2.0.20.patch \
      /opt/bend-tools /opt/bend-toolchain.json && \
    rm -rf /tmp/bend.tar.gz /tmp/bend-source.tar.gz /tmp/bend-toolchain

# Compile the experimental INT8-activation backend without allocating a GPU.
# The existing sgl-kernel W4A16 implementation remains the control.
FROM lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9 AS marlin-build
COPY patches/marlin-int8/ /opt/qwen/marlin-source/
RUN MAX_JOBS=4 python3 -m pip --disable-pip-version-check wheel \
      --no-build-isolation --no-deps --wheel-dir /opt/qwen/marlin-wheels \
      /opt/qwen/marlin-source

# Diagnostic-only: retain the exact source and wheel for gated synthetic runs.
# This target does not qualify serving or replace the final image's proof gate.
FROM marlin-build AS marlin-diagnostic
RUN python3 -m pip --disable-pip-version-check install --no-index --no-deps \
      /opt/qwen/marlin-wheels/*.whl

FROM bend-toolchain AS bend-build
COPY bend/ /opt/qwen/source/bend/
COPY LAWS.bend PROOF.bend /opt/qwen/source/
RUN python3 /opt/qwen/source/bend/adapter.py generate \
      --output /opt/qwen/bend --bend /opt/bend-tools/bin/bend && \
    python3 /opt/qwen/source/bend/adapter.py compile --directory /opt/qwen/bend --cc /usr/bin/clang-19 && \
    python3 /opt/qwen/source/bend/adapter.py verify --directory /opt/qwen/bend && \
    PYTHONPATH=/opt/qwen/source python3 -m bend.native_build \
      --directory /opt/qwen/bend --cc /usr/bin/clang-19 \
      --nvrtc /usr/local/cuda/lib64/libnvrtc.so
COPY bend/adapter.py bend/native.py bend/native_build.py bend/native.cu /opt/qwen/bend/

FROM lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9
COPY --from=bend-build /opt/qwen/bend/ /opt/qwen/bend/
COPY --from=bend-build /opt/bend-toolchain.json /opt/qwen/bend-toolchain.json
COPY --from=marlin-build /opt/qwen/marlin-wheels/ /opt/qwen/marlin-wheels/
RUN python3 -m pip --disable-pip-version-check install --no-index --no-deps \
      /opt/qwen/marlin-wheels/*.whl && \
    rm -rf /opt/qwen/marlin-wheels

COPY patches/ /opt/qwen/patches/
COPY docker/build-patches.sh docker/entrypoint.sh /opt/qwen/docker/
COPY serve/ /opt/qwen/serve/
COPY prepare/verify-models.py prepare/manifest.json prepare/artifact.sha256 prepare/source.sha256 prepare/draft.sha256 prepare/embedding-validation.json /model-preparation/
ARG QWEN_PATCH_SERIES=experimental
RUN bash /opt/qwen/docker/build-patches.sh "$QWEN_PATCH_SERIES" && \
    printf '%s\n' "$QWEN_PATCH_SERIES" > /opt/qwen/patch-series && \
    find /sgl-workspace/sglang/python -name __pycache__ -type d -prune -exec rm -rf {} + && \
    { find /opt/sglang/lib/python3.12/site-packages/sglang -name __pycache__ -type d -prune -exec rm -rf {} + 2>/dev/null || true; }

ENV HOME=/cache PYTHONDONTWRITEBYTECODE=1 PYTHONUNBUFFERED=1     HF_HUB_OFFLINE=1 TRANSFORMERS_OFFLINE=1     HF_HUB_DISABLE_TELEMETRY=1 DO_NOT_TRACK=1     SGLANG_HEALTH_CHECK_TIMEOUT=300
WORKDIR /opt/qwen
EXPOSE 18020
ENTRYPOINT ["bash", "/opt/qwen/docker/entrypoint.sh"]
