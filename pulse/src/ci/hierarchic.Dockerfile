# This Dockerfile should be run from the root Pulse directory

ARG FSTAR_BRANCH=master
FROM fstar:local-branch-$FSTAR_BRANCH

# CI dependencies for the Wasm11 test: node.js
RUN curl -fsSL https://deb.nodesource.com/setup_16.x | sudo -E bash -
RUN sudo apt-get update && sudo apt-get install -y --no-install-recommends nodejs

# install rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends llvm-dev libclang-dev clang
RUN . "$HOME/.cargo/env" && rustup component add rustfmt && cargo install bindgen-cli

ADD --chown=opam:opam ./ $HOME/pulse
WORKDIR $HOME/pulse

ARG opamthreads=24

# Install Karamel
ENV KRML_HOME $HOME/pulse_tools/karamel
RUN mkdir -p $HOME/pulse_tools && \
    git clone --branch $(jq -c -r '.RepoVersions.karamel' $HOME/pulse/src/ci/config.json || echo master) https://github.com/FStarLang/karamel $KRML_HOME && \
    eval $(opam env) && $KRML_HOME/.docker/build/install-other-deps.sh && \
    env OTHERFLAGS='--admit_smt_queries true' make -C $KRML_HOME -j $opamthreads

# Pulse CI proper
ARG PULSE_NIGHTLY_CI
ARG OTHERFLAGS
RUN eval $(opam env) && . "$HOME/.cargo/env" && env PULSE_NIGHTLY_CI="$PULSE_NIGHTLY_CI" make -k -j $opamthreads -C $HOME/pulse/src ci

ENV PULSE_HOME $HOME/pulse
