# This Dockerfile creates a base image suitable to start building F*.
#
# It is used by the CI job. It MAY miss some dependency, these are
# anyway re-checked and installed if needed when running the CI job. We
# only install them here to speed up that process.
#
# The ONLY file read by this dockerfile is fstar.opam in the root,
# and it is copied into the home directory on the image. CI jobs
# will NOT use this file.

# We always try to build against the most current ubuntu image.
FROM ubuntu:latest

RUN apt-get update

# Install editors, for the rare cases where we spin up a container to
# see the status. Not a big deal to have them here, only installed
# nightly and the files are shared by all subcontainers due to
# overlayfs.
RUN apt-get -y --no-install-recommends install vim emacs

# Base dependencies: opam
# CI dependencies: jq (to identify F* branch)
# python3 (for interactive tests)
# libicu (for .NET, cf. https://aka.ms/dotnet-missing-libicu )
RUN apt-get install -y --no-install-recommends \
      jq \
      bc \
      ca-certificates \
      curl \
      wget \
      git \
      gnupg \
      sudo \
      python3 \
      python-is-python3 \
      libicu70 \
      opam

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

# Install GitHub CLI
# From https://github.com/cli/cli/blob/trunk/docs/install_linux.md#debian-ubuntu-linux-raspberry-pi-os-apt
# This is only used by the workflow that makes a release and publishes
# it, but no harm in having it in the base.
RUN { type -p curl >/dev/null || sudo apt-get install curl -y ; } \
    && curl -fsSL https://cli.github.com/packages/githubcli-archive-keyring.gpg | sudo dd of=/usr/share/keyrings/githubcli-archive-keyring.gpg \
    && sudo chmod go+r /usr/share/keyrings/githubcli-archive-keyring.gpg \
    && echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/githubcli-archive-keyring.gpg] https://cli.github.com/packages stable main" | sudo tee /etc/apt/sources.list.d/github-cli.list > /dev/null \
    && sudo apt-get update \
    && sudo apt-get install gh -y

# CI dependencies: .NET Core
# Repository install may incur some (transient?) failures (see for instance https://github.com/dotnet/sdk/issues/27082 )
# So, we use manual install instead, from https://docs.microsoft.com/en-us/dotnet/core/install/linux-scripted-manual#manual-install
ENV DOTNET_ROOT /home/opam/dotnet
RUN wget -nv https://download.visualstudio.microsoft.com/download/pr/cd0d0a4d-2a6a-4d0d-b42e-dfd3b880e222/008a93f83aba6d1acf75ded3d2cfba24/dotnet-sdk-6.0.400-linux-x64.tar.gz && \
    mkdir -p $DOTNET_ROOT && \
    tar xf dotnet-sdk-6.0.400-linux-x64.tar.gz -C $DOTNET_ROOT && \
    echo 'export PATH=$PATH:$DOTNET_ROOT:$DOTNET_ROOT/tools' | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile && \
    rm -f dotnet-sdk*.tar.gz

# Install OCaml
ARG OCAML_VERSION=4.12.0
RUN opam init --compiler=$OCAML_VERSION --disable-sandboxing 
RUN opam env --set-switch | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile
RUN opam option depext-run-installs=true
ENV OPAMYES=1

# F* dependencies. This is the only place where we read a file from
# the F* repo.
ADD fstar.opam $HOME/fstar.opam
RUN opam install --confirm-level=unsafe-yes --deps-only $HOME/fstar.opam

# Some karamel dependencies
RUN opam install --confirm-level=unsafe-yes fix fileutils visitors camlp4 wasm ulex

# Set up $HOME/bin. Note, binaries here take precedence over OPAM
RUN mkdir $HOME/bin
RUN echo 'export PATH=$HOME/bin:$PATH' | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile

# Install runlim
RUN git clone --depth 1 https://github.com/arminbiere/runlim
RUN (cd runlim && ./configure.sh --prefix=$HOME/bin && make && make install)
RUN rm -rf runlim

WORKDIR $HOME

# Configure the git user for hint refresh
RUN git config --global user.name "Dzomo, the Everest Yak" && \
    git config --global user.email "everbld@microsoft.com"
