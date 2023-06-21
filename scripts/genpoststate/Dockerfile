FROM --platform=linux/amd64 fedora:38

ENV TESTDIR=ethtest
ARG GAT_VERSION="1.12.0-e501b3b0"

RUN mkdir $TESTDIR
WORKDIR $TESTDIR

RUN dnf -y install jq \
    && dnf -y clean all \
    && rm -rf /var/cache/yum

RUN curl -O https://gethstore.blob.core.windows.net/builds/geth-alltools-linux-amd64-${GAT_VERSION}.tar.gz
RUN curl -O https://gethstore.blob.core.windows.net/builds/geth-alltools-linux-amd64-${GAT_VERSION}.tar.gz.asc

RUN gpg --recv-keys F9585DE6 C2FF8BBF 9BA28146 7B9E2481 D2A67EAC && gpg --verify geth-alltools-linux-amd64-${GAT_VERSION}.tar.gz.asc

RUN tar -xvf geth-alltools-linux-amd64-${GAT_VERSION}.tar.gz \
    && mv geth-alltools-linux-amd64-${GAT_VERSION}/evm evm \
    && rm -rf geth-alltools-linux-amd64-${GAT_VERSION}.tar.gz geth-alltools-linux-amd64-${GAT_VERSION}.tar.gz.asc geth-alltools-linux-amd64-${GAT_VERSION}

COPY gps.sh /ethtest/gps.sh

ENTRYPOINT ["/ethtest/gps.sh"]
