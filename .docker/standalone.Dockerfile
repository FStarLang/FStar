# This Dockerfile should be run from the root FStar directory

FROM fstar_ci_base

# Copy repo into image.
ADD --chown=opam:opam ./ $HOME/FStar/

# Make sure opam dependencies are installed, the base image
# may be stale.
RUN opam install --confirm-level=unsafe-yes --deps-only ./fstar.opam

# Run CI proper
WORKDIR $HOME/FStar
ARG CI_TARGET=uregressions
ARG CI_THREADS=24
ARG CI_BRANCH=master
ARG CI_NO_KARAMEL=
RUN eval $(opam env) && Z3_LICENSE="$(opam config expand '%{prefix}%')/.opam-switch/sources/z3.4.8.5/LICENSE.txt" CI_NO_KARAMEL=$CI_NO_KARAMEL .docker/build/build-standalone.sh $CI_TARGET $CI_THREADS $CI_BRANCH

WORKDIR $HOME
ENV FSTAR_HOME $HOME/FStar
