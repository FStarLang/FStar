# This Dockerfile should be run from the root Pulse directory

ARG ocaml_version=4.14
FROM ocaml/opam:ubuntu-20.04-ocaml-$ocaml_version

# CI dependencies for the Wasm11 test: node.js
RUN curl -fsSL https://deb.nodesource.com/setup_16.x | sudo -E bash -
RUN sudo apt-get install -y --no-install-recommends nodejs

# install rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

ARG opamthreads=24

# (for .NET, cf. https://aka.ms/dotnet-missing-libicu )
# CI dependencies: .NET Core
# Repository install may incur some (transient?) failures (see for instance https://github.com/dotnet/sdk/issues/27082 )
# So, we use manual install instead, from https://docs.microsoft.com/en-us/dotnet/core/install/linux-scripted-manual#manual-install
ENV DOTNET_ROOT /home/opam/dotnet
RUN sudo apt-get install --yes --no-install-recommends \
    libicu-dev \
    wget \
    && \
    wget https://download.visualstudio.microsoft.com/download/pr/cd0d0a4d-2a6a-4d0d-b42e-dfd3b880e222/008a93f83aba6d1acf75ded3d2cfba24/dotnet-sdk-6.0.400-linux-x64.tar.gz && \
    mkdir -p $DOTNET_ROOT && \
    tar xf dotnet-sdk-6.0.400-linux-x64.tar.gz -C $DOTNET_ROOT

ENV PATH=${PATH}:$DOTNET_ROOT:$DOTNET_ROOT/tools

ADD --chown=opam:opam ./ pulse/

# Install F* and Karamel from the Karamel CI install script
# FIXME: the `opam depext` command should be unnecessary with opam 2.1
ENV FSTAR_HOME=$HOME/FStar
ENV KRML_HOME=$HOME/karamel
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends \
    wget \
    jq \
    && \
    git clone --branch $(jq -c -r '.RepoVersions.fstar' pulse/ci/config.json || echo master) https://github.com/FStarLang/FStar $FSTAR_HOME && \
    eval $(opam env) && \
    opam depext conf-gmp z3.4.8.5-1 conf-m4 && \
    opam install --deps-only $FSTAR_HOME/fstar.opam && \
    env OTHERFLAGS='--admit_smt_queries true' make -C $FSTAR_HOME -j $opamthreads && \
    git clone --branch $(jq -c -r '.RepoVersions.karamel' pulse/ci/config.json || echo master) https://github.com/FStarLang/karamel $KRML_HOME && \
    eval $(opam env) && $KRML_HOME/.docker/build/install-other-deps.sh && \
    env OTHERFLAGS='--admit_smt_queries true' make -C $KRML_HOME -j $opamthreads

# FIXME: The recent changes to MLish and bootstrapping mean that we must
# not try to check prims.fst or the rest of ulib in --MLish mode, since
# some files fail to do so. This will happen when trying to extract the
# files in src/syntax_extension, as there are no checked files for them.
# So, call the F* makefile to bootstrap F* and generate the files. This
# is probably only a bandaid... but I'm not sure what the best thing to
# do is.
RUN eval $(opam env) && \
    env OTHERFLAGS='--admit_smt_queries true' make -C $FSTAR_HOME -j $opamthreads bootstrap

# Produce the binary package
RUN eval $(opam env) && . $HOME/.cargo/env && pulse/ci/package.sh -j $opamthreads

ENV PULSE_HOME $HOME/pulse
