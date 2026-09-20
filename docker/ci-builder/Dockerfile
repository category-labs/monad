# CI Builder Dockerfile - Reliable base
# This replicates docker/Dockerfile base stage with reliability improvements

# syntax=docker/dockerfile:1-labs
FROM ubuntu:25.04

# Set environment variables
ENV DEBIAN_FRONTEND=noninteractive
ENV TZ=UTC

# Keep original Ubuntu repositories for reliability with development releases

# Replicate base stage with retry logic
RUN for i in {1..5}; do \
        (apt update && apt upgrade -y) && break || \
        (echo "Base update attempt $i failed, retrying in 30s..." && sleep 30); \
    done

RUN for i in {1..3}; do \
        (apt update && apt install -y apt-utils) && break || sleep 30; \
    done

RUN for i in {1..3}; do \
        (apt update && apt install -y dialog) && break || sleep 30; \
    done

RUN for i in {1..3}; do \
        (apt update && apt install -y \
          ca-certificates \
          curl \
          gnupg \
          software-properties-common \
          wget) && break || sleep 30; \
    done

# Copy and run existing build scripts
COPY scripts/ubuntu-build/ /opt

RUN for i in {1..3}; do \
        (apt update && apt install -y \
          clang-19 \
          gcc-15 \
          g++-15) && break || sleep 30; \
    done

# Run dependency scripts with retry logic
RUN for i in {1..3}; do \
        /opt/install-boost.sh && break || sleep 30; \
    done

RUN for i in {1..3}; do \
        /opt/install-tools.sh && break || sleep 30; \
    done

RUN for i in {1..3}; do \
        /opt/install-deps.sh && break || sleep 30; \
    done

RUN for i in {1..3}; do \
        (apt update && apt install -y \
          libarchive-dev \
          libbrotli-dev \
          libcap-dev \
          libcli11-dev \
          libgmp-dev \
          libtbb-dev \
          libzstd-dev) && break || sleep 30; \
    done

# Clean up apt cache to reduce image size
RUN apt-get clean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/* && \
    rm -rf /var/tmp/*
