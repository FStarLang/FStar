# For check-world workflow, should be coallesced to the other base.
# This could definitely use a big cleanup too.
FROM ubuntu:23.10

RUN apt-get update

# Base dependencies: opam
# python3 (for interactive tests)
RUN apt-get install -y --no-install-recommends \
      git \
      sudo \
      python3 \
      python-is-python3 \
      opam \
      rustc \
      && apt-get clean -y

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
    && sudo apt-get install gh -y \
    && sudo apt-get clean

# Install OCaml
ARG OCAML_VERSION=4.14.2
RUN opam init --compiler=$OCAML_VERSION --disable-sandboxing
RUN opam env --set-switch | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile
RUN opam option depext-run-installs=true
ENV OPAMYES=1

# F* dependencies. This is the only place where we read a file from
# the F* repo.
ADD fstar.opam $HOME/fstar.opam
RUN opam install --confirm-level=unsafe-yes --deps-only $HOME/fstar.opam && opam clean

# Some karamel dependencies
RUN opam install --confirm-level=unsafe-yes fix fileutils visitors camlp4 wasm ulex uucp ctypes ctypes-foreign && opam clean

# Set up $HOME/bin. Note, binaries here take precedence over OPAM
RUN mkdir $HOME/bin
RUN echo 'export PATH=$HOME/bin:$PATH' | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile

WORKDIR $HOME

RUN sudo apt-get install -y npm && sudo apt-get clean

RUN sudo apt-get install -y --no-install-recommends \
      time \
      && sudo apt-get clean -y

# To run Vale
# RUN sudo apt-get install -y dotnet-runtime-6.0 dotnet-sdk-6.0

# everparse (hex for quackyducky)
RUN opam install --confirm-level=unsafe-yes hex sexplib re sha && opam clean

# CI dependencies: .NET Core
# Repository install may incur some (transient?) failures (see for instance https://github.com/dotnet/sdk/issues/27082 )
# So, we use manual install instead, from https://docs.microsoft.com/en-us/dotnet/core/install/linux-scripted-manual#manual-install
ENV DOTNET_ROOT /home/opam/dotnet
RUN wget -nv https://download.visualstudio.microsoft.com/download/pr/cd0d0a4d-2a6a-4d0d-b42e-dfd3b880e222/008a93f83aba6d1acf75ded3d2cfba24/dotnet-sdk-6.0.400-linux-x64.tar.gz && \
    mkdir -p $DOTNET_ROOT && \
    tar xf dotnet-sdk-6.0.400-linux-x64.tar.gz -C $DOTNET_ROOT && \
    rm -f dotnet-sdk*.tar.gz
    # echo 'export PATH=$PATH:$DOTNET_ROOT:$DOTNET_ROOT/tools' | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile && \

RUN sudo ln -s $DOTNET_ROOT/dotnet /usr/local/bin/dotnet
