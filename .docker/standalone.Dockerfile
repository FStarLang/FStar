# This Dockerfile should be run from the root FStar directory
# It builds on top of the fstar_ci_base container

# See fstar_ci_base.Dockerfile
FROM fstar_ci_base_z3master

# F* dependencies

# Copy fstar.opam file into container. We do not copy the full repo
# (yet) to make better use of the build cache.
COPY --chown=opam:opam ./fstar.opam $HOME/FStar/fstar.opam

# If CI_TEST_MIN_OPAM_DEPS is set, then for each package except ocaml,
# when a lower bound constraint for its version number exists, replace
# this constraint with an equality to install that lower version
ARG CI_TEST_MIN_OPAM_DEPS=
RUN if [[ -n "$CI_TEST_MIN_OPAM_DEPS" ]] ; then \
  sed -i 's!>=!=!g' $HOME/FStar/fstar.opam && \
  sed -i 's!"ocaml" {=!"ocaml" {>=!' $HOME/FStar/fstar.opam ; \
fi


# F* dependencies
RUN opam install --confirm-level=unsafe-yes menhir # needed to bootstrap
RUN opam install --confirm-level=unsafe-yes --deps-only $HOME/FStar/fstar.opam

# Configure the git user for hint refresh
RUN git config --global user.name "Dzomo, the Everest Yak" && \
    git config --global user.email "everbld@microsoft.com"

# HACK
RUN rm $(which z3)

WORKDIR $HOME/FStar

# Now copy full repo into container
COPY --chown=opam:opam ./ $HOME/FStar/

# Run CI proper
ARG CI_TARGET=uregressions
ARG CI_THREADS=24
ARG CI_BRANCH=master
ARG CI_NO_KARAMEL=
RUN --mount=type=secret,id=DZOMO_GITHUB_TOKEN eval $(opam env) && Z3_LICENSE="$(opam config expand '%{prefix}%')/.opam-switch/sources/z3.4.8.5/LICENSE.txt" CI_NO_KARAMEL=$CI_NO_KARAMEL DZOMO_GITHUB_TOKEN=$(sudo cat /run/secrets/DZOMO_GITHUB_TOKEN) .docker/build/build-standalone.sh $CI_TARGET $CI_THREADS $CI_BRANCH |& tee LOG

WORKDIR $HOME
ENV FSTAR_HOME $HOME/FStar
