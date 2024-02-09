# This Dockerfile should be run from the root Pulse directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-22.04-ocaml-$ocaml_version

ARG opamthreads=24

# CI dependencies for the Wasm11 test: node.js
# The sed call is a workaround for these upstream issues... sigh.
# https://github.com/nodesource/distributions/issues/1576
# https://github.com/nodesource/distributions/issues/1593
# Remove when they are solved
RUN curl -fsSL https://deb.nodesource.com/setup_16.x | sed 's,https://deb.nodesource.com,http://deb.nodesource.com,' | sudo -E bash -
RUN sudo apt-get install -y --no-install-recommends nodejs

# install rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
RUN . "$HOME/.cargo/env"

ADD --chown=opam:opam ./ pulse/

# Install F* and Karamel from the Karamel CI install script
# FIXME: the `opam depext` command should be unnecessary with opam 2.1
ENV KRML_HOME=$HOME/karamel
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends \
    jq \
    && \
    git clone --branch $(jq -c -r '.RepoVersions.fstar' pulse/src/ci/config.json || echo master) https://github.com/FStarLang/FStar $HOME/FStar && \
    eval $(opam env) && \
    opam depext conf-gmp z3.4.8.5-1 conf-m4 && \
    opam install --deps-only $HOME/FStar/fstar.opam && \
    env OTHERFLAGS='--admit_smt_queries true' make -C $HOME/FStar -j $opamthreads && \
    git clone --branch $(jq -c -r '.RepoVersions.karamel' pulse/src/ci/config.json || echo master) https://github.com/FStarLang/karamel $KRML_HOME && \
    eval $(opam env) && $KRML_HOME/.docker/build/install-other-deps.sh && \
    env FSTAR_HOME=$HOME/FStar OTHERFLAGS='--admit_smt_queries true' make -C $KRML_HOME -j $opamthreads

ENV PATH=$HOME/FStar/bin:$PATH

# Pulse CI proper
ARG PULSE_NIGHTLY_CI
ARG OTHERFLAGS=--use_hints
RUN eval $(opam env) && env PULSE_NIGHTLY_CI="$PULSE_NIGHTLY_CI" make -k -j $opamthreads -C pulse test
