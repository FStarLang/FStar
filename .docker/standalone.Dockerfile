# This Dockerfile should be run from the root FStar directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-ocaml-$ocaml_version

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
RUN opam depext conf-gmp z3.4.8.5 conf-m4

ADD --chown=opam:opam ./ $HOME/FStar/

RUN opam install --deps-only $HOME/FStar/fstar.opam

# CI dependencies (including Mono for F# and other packages for karamel, EverParse)
RUN opam install \
    hex \
    visitors \
    ulex \
    fix \
    wasm \
    && \
    sudo apt install gnupg ca-certificates && \
    wget https://packages.microsoft.com/config/ubuntu/21.04/packages-microsoft-prod.deb -O packages-microsoft-prod.deb && \
    sudo dpkg -i packages-microsoft-prod.deb && \
    rm packages-microsoft-prod.deb && \
    sudo apt-get update && \
    sudo apt-get install -y apt-transport-https && \
    sudo apt update && \
    sudo apt-get --yes install --no-install-recommends \
    dotnet-sdk-6.0 \
    python \
    python3 \
    wget \
    jq


WORKDIR $HOME/FStar

ARG CI_TARGET=uregressions
ARG CI_THREADS=24
ARG CI_BRANCH=master
RUN --mount=type=secret,id=DZOMO_GITHUB_TOKEN eval $(opam env) && DZOMO_GITHUB_TOKEN=$(sudo cat /run/secrets/DZOMO_GITHUB_TOKEN) .docker/build/build-standalone.sh $CI_TARGET $CI_THREADS $CI_BRANCH

WORKDIR $HOME
ENV FSTAR_HOME $HOME/FStar
