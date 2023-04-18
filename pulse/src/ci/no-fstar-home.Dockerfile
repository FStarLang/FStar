# This Dockerfile should be run from the root Steel directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-ocaml-$ocaml_version

ARG opamthreads=24

ADD --chown=opam:opam ./ steel/

# Install F* and Karamel from the Karamel CI install script
# FIXME: the `opam depext` command should be unnecessary with opam 2.1
ENV KRML_HOME=$HOME/karamel
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends \
    jq \
    && git clone --branch taramana_no_steel https://github.com/FStarLang/karamel $KRML_HOME && \
    eval $(opam env) && env FSTAR_HOME=$HOME/FStar $KRML_HOME/.docker/build/install-deps.sh && \
    env FSTAR_HOME=$HOME/FStar OTHERFLAGS='--admit_smt_queries true' make -C $KRML_HOME -j $opamthreads

ENV PATH=$HOME/FStar/bin:$PATH

# CI dependencies for the Wasm11 test: node.js
RUN curl -fsSL https://deb.nodesource.com/setup_16.x | sudo -E bash -
RUN sudo apt-get install -y --no-install-recommends nodejs

# Steel CI proper
ARG STEEL_NIGHTLY_CI
RUN eval $(opam env) && env STEEL_NIGHTLY_CI="$STEEL_NIGHTLY_CI" make -k -j $opamthreads -C steel test
