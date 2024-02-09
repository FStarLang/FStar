# This Dockerfile should be run from the root Pulse directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-22.04-ocaml-$ocaml_version

ARG opamthreads=24

ADD --chown=opam:opam ./ pulse/

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
RUN sudo apt-get update && \
    sudo apt-get install --yes --no-install-recommends jq && \
    opam depext conf-gmp z3.4.8.5-1 conf-m4 && \
    git clone --branch $(jq -c -r '.RepoVersions.fstar' pulse/src/ci/config.json || echo master) https://github.com/FStarLang/FStar FStar && \
    opam install -j $opamthreads -v -v -v FStar/fstar.opam && \
    rm -rf FStar

RUN eval $(opam env) && \
    opam install -j $opamthreads -v -v -v pulse/pulse.opam

ARG OTHERFLAGS=--use_hints

RUN cp -p -r pulse/share/pulse /tmp/pulse-share && \
    rm -rf pulse /tmp/pulse-share/Makefile.include && \
    eval $(opam env) && \
    env PULSE_HOME=$(opam config var prefix) make -j $opamthreads -k -C /tmp/pulse-share

RUN eval $(opam env) && \
    opam uninstall pulse
