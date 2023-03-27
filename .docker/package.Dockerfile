# This Dockerfile should be run from the root FStar directory
# It builds and tests a binary package for F*.
# It is a potential alternative to .scripts/process_build.sh

# Build the package
ARG ocaml_version=4.12
ARG opamthreads=24

FROM ocaml/opam:ubuntu-20.04-ocaml-$ocaml_version AS fstarbuild

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
RUN opam depext conf-gmp z3.4.8.5 conf-m4

ADD --chown=opam:opam ./fstar.opam fstar.opam

# Install opam dependencies only
RUN opam install --deps-only ./fstar.opam

# Install .NET
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends \
  libicu66

# (for .NET, cf. https://aka.ms/dotnet-missing-libicu )
# CI dependencies: .NET Core
# Repository install may incur some (transient?) failures (see for instance https://github.com/dotnet/sdk/issues/27082 )
# So, we use manual install instead, from https://docs.microsoft.com/en-us/dotnet/core/install/linux-scripted-manual#manual-install
ENV DOTNET_ROOT /home/opam/dotnet
RUN sudo apt-get install --yes --no-install-recommends \
    wget

RUN wget https://download.visualstudio.microsoft.com/download/pr/cd0d0a4d-2a6a-4d0d-b42e-dfd3b880e222/008a93f83aba6d1acf75ded3d2cfba24/dotnet-sdk-6.0.400-linux-x64.tar.gz && \
    mkdir -p $DOTNET_ROOT && \
    tar xf dotnet-sdk-6.0.400-linux-x64.tar.gz -C $DOTNET_ROOT

ENV PATH=${PATH}:$DOTNET_ROOT:$DOTNET_ROOT/tools

ADD --chown=opam:opam ./ FStar/

# Build the package, 
RUN eval $(opam env) && env Z3_LICENSE="$(opam config expand '%{prefix}%')/.opam-switch/sources/z3.4.8.5/LICENSE.txt" OTHERFLAGS='--admit_smt_queries true' make -C FStar -j $opamthreads package

# Create a separate image to test the package

# Test the F* binary package

# Test the fresh package without OCaml
FROM ubuntu:20.04 AS fstarnoocaml
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update
RUN apt-get --yes install --no-install-recommends make sudo libgomp1

# Create a new user and give them sudo rights
RUN useradd -d /home/test test
RUN echo 'test ALL=NOPASSWD: ALL' >> /etc/sudoers
RUN mkdir /home/test
RUN chown test:test /home/test
USER test
ENV HOME /home/test
WORKDIR $HOME
SHELL ["/bin/bash", "--login", "-c"]

# Copy the package
COPY --from=fstarbuild /home/opam/FStar/src/ocaml-output/fstar.tar.gz /home/test/fstar.tar.gz
RUN tar xzf fstar.tar.gz

# Copy tests, examples and docs
ADD --chown=test:test examples/ fstar_examples/
ADD --chown=test:test doc/ fstar_doc/

# Case 3: test F* package without OCaml

# Test the package with FSTAR_HOME defined
# Move z3 elsewhere
# FROM fstarnoocaml
# ENV FSTAR_HOME=$HOME/fstar
# RUN mkdir -p $HOME/bin && ln -s $FSTAR_HOME/bin/z3 $HOME/bin/
# ENV PATH="${HOME}/bin:${PATH}"
# RUN make -C fstar_examples -j $opamthreads
# RUN make -C fstar_doc/tutorial -j $opamthreads regressions

# Test the package with F* in the PATH instead
FROM fstarnoocaml
ENV PATH="/home/test/fstar/bin:${PATH}"
RUN make -C fstar_examples -j $opamthreads
RUN make -C fstar_doc/tutorial -j $opamthreads regressions

FROM fstarnoocaml
# This is the last image. So we can also copy the file that contains
# the desired filename for the package, to be extracted via
# `docker cp`
COPY --from=fstarbuild /home/opam/FStar/src/ocaml-output/version_platform.txt /home/test/version_platform.txt
