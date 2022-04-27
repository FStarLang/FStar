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
    sudo apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys 3FA7E0328081BFF6A14DA29AA6A19B38D3D831EF && \
    { echo "deb https://download.mono-project.com/repo/ubuntu stable-focal main" | sudo tee /etc/apt/sources.list.d/mono-official-stable.list ; } && \
    sudo apt update && \
    sudo apt-get --yes install --no-install-recommends \
    fsharp \
    python3 \
    wget \
    jq


WORKDIR $HOME/FStar

ARG CI_TARGET=uregressions
ARG CI_THREADS=24
ARG CI_BRANCH=master
RUN eval $(opam env) && .docker/build/build-standalone.sh $CI_TARGET $CI_THREADS $CI_BRANCH

WORKDIR $HOME
ENV FSTAR_HOME $HOME/FStar
