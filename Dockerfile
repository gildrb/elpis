# Digest-pinned stock runtime plus the ordinary ordered Git patch series.
# The 262144-token launch candidate is unqualified; no experimental series by default.
FROM lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9

COPY patches/ /opt/qwen/patches/
COPY docker/ /opt/qwen/docker/
COPY serve/ /opt/qwen/serve/
COPY prepare/verify-models.py prepare/manifest.json prepare/artifact.sha256 prepare/source.sha256 prepare/draft.sha256 prepare/embedding-validation.json /model-preparation/
ARG QWEN_PATCH_SERIES=baseline
RUN bash /opt/qwen/docker/build-patches.sh "$QWEN_PATCH_SERIES" && \
    printf '%s\n' "$QWEN_PATCH_SERIES" > /opt/qwen/patch-series

ENV HOME=/cache PYTHONDONTWRITEBYTECODE=1 PYTHONUNBUFFERED=1     HF_HUB_OFFLINE=1 TRANSFORMERS_OFFLINE=1     HF_HUB_DISABLE_TELEMETRY=1 DO_NOT_TRACK=1     SGLANG_HEALTH_CHECK_TIMEOUT=300
WORKDIR /opt/qwen
EXPOSE 18020
ENTRYPOINT ["bash", "/opt/qwen/docker/entrypoint.sh"]
