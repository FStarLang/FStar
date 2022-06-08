# This Dockerfile should be run from the root FStar directory

FROM ubuntu:22.04

# Base dependencies: opam
# CI dependencies: jq (to identify F* branch)
# python3 (for interactive tests)
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      jq \
      ca-certificates \
      curl \
      wget \
      git \
      gnupg \
      sudo \
      python3 \
      python-is-python3 \
      opam

# CI dependencies: .NET Core
# Dotnet feed should be kept in sync with Ubuntu version
# see https://docs.microsoft.com/en-us/dotnet/core/install/linux-ubuntu
RUN apt install -y gnupg ca-certificates wget && \
    wget https://packages.microsoft.com/config/ubuntu/22.04/packages-microsoft-prod.deb -O packages-microsoft-prod.deb && \
    dpkg -i packages-microsoft-prod.deb && \
    rm packages-microsoft-prod.deb && \
    apt-get update && \
    apt-get --yes install --no-install-recommends \
    apt-transport-https \
    dotnet-sdk-6.0

# Create a new user and give them sudo rights
# NOTE: we give them the name "opam" to keep compatibility with
# derived hierarchical CI
RUN useradd -d /home/opam opam
RUN echo 'opam ALL=NOPASSWD: ALL' >> /etc/sudoers
RUN mkdir /home/opam
RUN chown opam:opam /home/opam
USER opam
ENV HOME /home/opam
WORKDIR $HOME
SHELL ["/bin/bash", "--login", "-c"]

# Install OCaml
ARG OCAML_VERSION=4.12.0
RUN opam init --compiler=$OCAML_VERSION --disable-sandboxing 
RUN opam env --set-switch | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile
RUN opam option depext-run-installs=true
ENV OPAMYES=1

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
# RUN opam depext conf-gmp z3.4.8.5 conf-m4

ADD --chown=opam:opam ./ $HOME/FStar/

# F* dependencies
RUN opam install --confirm-level=unsafe-yes --deps-only $HOME/FStar/fstar.opam

WORKDIR $HOME/FStar

# Run CI proper
ARG CI_TARGET=uregressions
ARG CI_THREADS=24
ARG CI_BRANCH=master
RUN --mount=type=secret,id=DZOMO_GITHUB_TOKEN eval $(opam env) && DZOMO_GITHUB_TOKEN=$(sudo cat /run/secrets/DZOMO_GITHUB_TOKEN) .docker/build/build-standalone.sh $CI_TARGET $CI_THREADS $CI_BRANCH

WORKDIR $HOME
ENV FSTAR_HOME $HOME/FStar
