# This Dockerfile should be run from the root FStar directory
# It is a potential alternative to .scripts/process_build.sh

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-ocaml-$ocaml_version

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
RUN opam depext conf-gmp z3.4.8.5 conf-m4

ADD --chown=opam:opam ./ FStar/

# Install opam dependencies only
RUN opam install --deps-only FStar/fstar.opam
ARG opamthreads=24

# Build the package, 
RUN eval $(opam env) && env OTHERFLAGS='--admit_smt_queries true' make PACKAGE_DOCS=0 -C FStar -j $opamthreads package_unknown_platform

# Create a separate image to test the package
# Reinstall deps

FROM ocaml/opam:ubuntu-ocaml-$ocaml_version
ENV fstar_opam_deps="ocamlfind batteries stdint zarith ppx_deriving_yojson pprint ppxlib ocaml-compiler-libs"
RUN opam depext $fstar_opam_deps
RUN opam install $fstar_opam_deps

# Copy the F* binary package
COPY --from=0 /home/opam/FStar/src/ocaml-output/fstar.tar.gz /home/opam/fstar.tar.gz
RUN tar xzf fstar.tar.gz

# Test the F* binary package
ENV FSTAR_HOME /home/opam/fstar
ENV PATH="${FSTAR_HOME}/bin:${PATH}"
RUN eval $(opam env) && make -C $FSTAR_HOME/examples -j $opamthreads
RUN eval $(opam env) && make -C $FSTAR_HOME/doc/tutorial -j $opamthreads regressions
