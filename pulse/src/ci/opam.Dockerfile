# This Dockerfile should be run from the root Steel directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-ocaml-$ocaml_version

ARG opamthreads=24

ADD --chown=opam:opam ./ steel/

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
RUN opam depext conf-gmp z3.4.8.5 conf-m4 && \
    git clone --branch taramana_no_steel https://github.com/FStarLang/FStar FStar && \
    opam install -j $opamthreads -v -v -v FStar/fstar.opam && \
    rm -rf FStar

RUN opam install -j $opamthreads -v -v -v steel/steel.opam

RUN cp -p -r steel/share/steel /tmp/steel-share && \
    rm -rf steel /tmp/steel-share/Makefile.include && \
    eval $(opam env) && \
    env STEEL_HOME=$(opam config var prefix) make -j $opamthreads -k -C /tmp/steel-share
