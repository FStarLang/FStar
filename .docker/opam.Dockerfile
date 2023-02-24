# This Dockerfile should be run from the root FStar directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-ocaml-$ocaml_version

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
RUN opam depext conf-gmp z3.4.8.5 conf-m4

ADD --chown=opam:opam ./fstar.opam fstar.opam
RUN opam install --deps-only ./fstar.opam
RUN rm fstar.opam

ADD --chown=opam:opam ./ FStar/

ARG opamthreads=24
RUN opam install -j $opamthreads -v -v -v FStar/fstar.opam
RUN rm -rf FStar
# NOTE: I need to copy examples and tutorial from share/ because
# opam uninstall will balk at removing files created there during the test
RUN cp -p -r $(opam config var fstar:share)/examples $HOME/examples
RUN cp -p -r $(opam config var fstar:share)/doc $HOME/doc
RUN eval $(opam env) && make -C $HOME/examples -j $opamthreads
RUN eval $(opam env) && make -C $HOME/doc/tutorial -j $opamthreads regressions
RUN opam uninstall -v -v -v fstar
