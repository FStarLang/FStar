# This Dockerfile should be run from the root Pulse directory

ARG ocaml_version=4.14
FROM ocaml/opam:ubuntu-22.04-ocaml-$ocaml_version

RUN sudo apt-get install -y wget coreutils

# Install the Z3 versions we want to use in CI (4.8.5, 4.13.3). Note: we
# currently also have 4.8.5 in the opam switch, as it is a dependency of
# in fstar.opam, but that should be removed.

USER root
RUN wget -nv https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-ubuntu-16.04.zip \
 && unzip z3-4.8.5-x64-ubuntu-16.04.zip \
 && cp z3-4.8.5-x64-ubuntu-16.04/bin/z3 /usr/local/bin/z3-4.8.5 \
 && rm -r z3-4.8.5-*

RUN wget -nv https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-glibc-2.35.zip \
 && unzip z3-4.13.3-x64-glibc-2.35 \
 && cp z3-4.13.3-x64-glibc-2.35/bin/z3 /usr/local/bin/z3-4.13.3 \
 && rm -r z3-4.13.3-*
USER opam

# CI dependencies for the Wasm11 test: node.js
RUN curl -fsSL https://deb.nodesource.com/setup_16.x | sudo -E bash -
RUN sudo apt-get update && sudo apt-get install -y --no-install-recommends nodejs libgmp-dev pkg-config

# install rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends llvm-dev libclang-dev clang libgmp-dev pkg-config
RUN . "$HOME/.cargo/env" && rustup component add rustfmt && cargo install bindgen-cli

ARG opamthreads=24

# Install F* and Karamel from the Karamel CI install script
# FIXME: the `opam depext` command should be unnecessary with opam 2.1
ADD --chown=opam:opam ci/config.json pulse/ci/config.json
ENV FSTAR_HOME=$HOME/FStar
ENV KRML_HOME=$HOME/karamel
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends \
    wget \
    jq \
    && \
    git clone --branch $(jq -c -r '.RepoVersions.fstar' pulse/ci/config.json || echo master) https://github.com/FStarLang/FStar $FSTAR_HOME && \
    eval $(opam env) && \
    opam depext conf-gmp z3.4.8.5-1 conf-m4 && \
    opam install --deps-only $FSTAR_HOME/fstar.opam && \
    env OTHERFLAGS='--admit_smt_queries true' make -C $FSTAR_HOME -j $opamthreads && \
    git clone --branch $(jq -c -r '.RepoVersions.karamel' pulse/ci/config.json || echo master) https://github.com/FStarLang/karamel $KRML_HOME && \
    eval $(opam env) && $KRML_HOME/.docker/build/install-other-deps.sh && \
    env OTHERFLAGS='--admit_smt_queries true' make -C $KRML_HOME -j $opamthreads

# FIXME: The recent changes to MLish and bootstrapping mean that we must
# not try to check prims.fst or the rest of ulib in --MLish mode, since
# some files fail to do so. This will happen when trying to extract the
# files in src/syntax_extension, as there are no checked files for them.
# So, call the F* makefile to bootstrap F* and generate the files. This
# is probably only a bandaid... but I'm not sure what the best thing to
# do is.
RUN eval $(opam env) && \
    env OTHERFLAGS='--admit_smt_queries true' make -C $FSTAR_HOME -j $opamthreads bootstrap

# Pulse CI proper
ADD --chown=opam:opam ./ pulse/
ARG OTHERFLAGS
RUN eval $(opam env) && . $HOME/.cargo/env && make -k -j $opamthreads -C pulse ci

ENV PULSE_HOME $HOME/pulse
