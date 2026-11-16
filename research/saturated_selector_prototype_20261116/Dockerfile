# Build recipe only: no image built or executed in this phase.
FROM docker.io/sagemath/sagemath@sha256:fb96c7fb10d672f3be0d088399db3aeac52650416d1bb71f74f26429ea35778f
USER root
RUN mkdir -p /opt/selector /work && chown 1000:1000 /work
COPY research/saturated_selector_prototype_20261116/ /opt/selector/
ARG SOURCE_REVISION
LABEL org.opencontainers.image.revision=$SOURCE_REVISION
USER 1000:1000
WORKDIR /work
ENTRYPOINT ["sage", "--python", "/opt/selector/pilot.py"]
