# For check-world workflow, should be coallesced to the other base.
# This could definitely use a big cleanup too.
# FIXME: z3.4.8.5-1 can no longer be installed on Ubuntu 24.04 because python3-distutils disappeared, and the z3 opam package has not been fixed for version 4.8.5, and 23.10 and all prior non-LTS are now EOL. Reverting to the previous LTS
FROM ubuntu:24.04

RUN apt-get update

# Base dependencies: opam
# python3 (for interactive tests)
RUN apt-get install -y --no-install-recommends \
      git \
      sudo \
      ca-certificates \
      python3 \
      python-is-python3 \
      opam \
      rustc \
      && apt-get clean -y

# Install the relevant Z3 versions.
COPY ./bin/get_fstar_z3.sh /usr/local/bin
RUN get_fstar_z3.sh /usr/local/bin

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

RUN opam install --confirm-level=unsafe-yes mtime && opam clean

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
