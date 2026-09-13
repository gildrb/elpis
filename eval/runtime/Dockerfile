# Native Verifiers programs and uv locks, not a model-serving image.
FROM ghcr.io/astral-sh/uv:0.12.1@sha256:f6edac8c6d516a01a5387a8655c97481e0db46dd0a62ab62f41e5b2294376f6e AS uv
FROM python:3.12-slim@sha256:2fe5997d249a808b8eeea52c58a1dbffbba28754dc11699ef5c029f2d818ce79
COPY --from=uv /uv /uvx /usr/local/bin/
COPY .cache/runtime/ /tmp/vf-scripts/
ENV UV_LOCKED=true UV_PYTHON_DOWNLOADS=never UV_PYTHON=3.12
RUN set -eu; for script in /tmp/vf-scripts/*.py; do uv sync --locked --script "$script"; done
WORKDIR /workspace
