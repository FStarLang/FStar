# This Dockerfile should be run from the root FStar directory

# Build the package
ARG ocaml_version=4.12
ARG CI_THREADS=24

FROM ocaml/opam:ubuntu-20.04-ocaml-$ocaml_version AS fstarbuild

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
RUN opam depext conf-gmp conf-m4

ADD --chown=opam:opam ./fstar.opam fstar.opam

# Install opam dependencies only, but not z3
RUN grep -v z3 < fstar.opam > fstar-no-z3.opam && \
    rm fstar.opam && \
    opam install --deps-only ./fstar-no-z3.opam && \
    rm fstar-no-z3.opam

# Install GitHub CLI
# From https://github.com/cli/cli/blob/trunk/docs/install_linux.md#debian-ubuntu-linux-raspberry-pi-os-apt
RUN { type -p curl >/dev/null || sudo apt-get install curl -y ; } \
    && curl -fsSL https://cli.github.com/packages/githubcli-archive-keyring.gpg | sudo dd of=/usr/share/keyrings/githubcli-archive-keyring.gpg \
    && sudo chmod go+r /usr/share/keyrings/githubcli-archive-keyring.gpg \
    && echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/githubcli-archive-keyring.gpg] https://cli.github.com/packages stable main" | sudo tee /etc/apt/sources.list.d/github-cli.list > /dev/null \
    && sudo apt-get update \
    && sudo apt-get install gh -y

# Install .NET
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends \
  libicu66

# (for .NET, cf. https://aka.ms/dotnet-missing-libicu )
# CI dependencies: .NET Core
# Repository install may incur some (transient?) failures (see for instance https://github.com/dotnet/sdk/issues/27082 )
# So, we use manual install instead, from https://docs.microsoft.com/en-us/dotnet/core/install/linux-scripted-manual#manual-install
ENV DOTNET_ROOT /home/opam/dotnet
RUN sudo apt-get install --yes --no-install-recommends \
    wget \
    && \
    wget https://download.visualstudio.microsoft.com/download/pr/cd0d0a4d-2a6a-4d0d-b42e-dfd3b880e222/008a93f83aba6d1acf75ded3d2cfba24/dotnet-sdk-6.0.400-linux-x64.tar.gz && \
    mkdir -p $DOTNET_ROOT && \
    tar xf dotnet-sdk-6.0.400-linux-x64.tar.gz -C $DOTNET_ROOT

ENV PATH=${PATH}:$DOTNET_ROOT:$DOTNET_ROOT/tools

# Configure the git user
RUN git config --global user.name "Dzomo, the Everest Yak" && \
    git config --global user.email "everbld@microsoft.com"

# Download and extract z3, but do not add it in the PATH
# We download a z3 that does not depend on libgomp
ADD --chown=opam:opam https://github.com/tahina-pro/z3/releases/download/z3-4.8.5-linux-clang/z3-4.8.5-linux-clang-x86_64.tar.gz z3.tar.gz
RUN tar xf z3.tar.gz

ADD --chown=opam:opam ./ FStar/

# Build the package with our Z3
RUN eval $(opam env) && env OTHERFLAGS='--admit_smt_queries true' PATH=$HOME/z3:$PATH make -j $CI_THREADS -C FStar package

# Test the package with its Z3, without OCaml or any other dependency
FROM ubuntu:20.04 AS fstarnoocaml

# Install some dependencies
RUN apt-get update && \
    apt-get install --yes --no-install-recommends \
      make

# Create a new user and give them sudo rights
RUN useradd -d /home/test test
RUN echo 'test ALL=NOPASSWD: ALL' >> /etc/sudoers
RUN mkdir /home/test
RUN chown test:test /home/test
USER test
ENV HOME /home/test
WORKDIR $HOME
SHELL ["/bin/bash", "--login", "-c"]

# Copy the package and the test script
COPY --from=fstarbuild /home/opam/FStar/src/ocaml-output/fstar.tar.gz /home/test/FStar/src/ocaml-output/fstar.tar.gz
COPY --from=fstarbuild /home/opam/FStar/.scripts/test_package.sh /home/test/FStar/.scripts/test_package.sh

# Test the package
ARG CI_THREADS
RUN env CI_THREADS=$CI_THREADS /home/test/FStar/.scripts/test_package.sh

# Test the package with its Z3, with OCaml
FROM fstarbuild
ARG CI_THREADS
# Copy a dummy file to introduce an artificial dependence to the fstarnoocaml stage
# to force buildx to build that stage as well
COPY --from=fstarnoocaml /home/test/FStar/.scripts/test_package.sh /tmp/dummy
RUN eval $(opam env) && env CI_THREADS=$CI_THREADS ./FStar/.scripts/test_package.sh
