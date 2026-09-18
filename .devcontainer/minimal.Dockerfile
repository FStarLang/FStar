FROM mcr.microsoft.com/devcontainers/base:ubuntu24.04

# Base dependencies: opam
# CI dependencies: jq (to identify F* branch)
# python3 (for interactive tests)
# libicu (for .NET, cf. https://aka.ms/dotnet-missing-libicu )
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
      ca-certificates \
      curl \
      wget \
      git \
      gnupg \
      sudo \
      python3 \
      python-is-python3 \
      libgmp-dev \
      opam \
      vim \
      pkg-config \
      time \
      libffi-dev \
      tmux \
      rustup \
      libicu-dev \
    && apt-get clean -y
# FIXME: libgmp-dev should be installed automatically by opam,
# but it is not working, so just adding it above.
# Same for pkg-config. OPAM prompts even if we're giving --yes
# and setting OPAMYES.

USER vscode
ENV HOME=/home/vscode
WORKDIR /home/vscode

# Make sure ~/bin is in the PATH
RUN mkdir -p $HOME/bin
RUN echo 'export PATH=$HOME/bin:$PATH' | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile

# Install Rust
RUN rustup install stable

# Install .NET.  Ubuntu's archive only carries the SDKs that were current
# when the release was cut, and F* targets the latest LTS, so this goes
# through Microsoft's installer rather than apt.  It lands in ~/.dotnet,
# which must therefore be on the PATH and named by DOTNET_ROOT -- without
# the latter a published apphost looks for a runtime under /usr/lib/dotnet
# and does not find one.
ARG DOTNET_CHANNEL=10.0
RUN curl -fsSL https://dot.net/v1/dotnet-install.sh -o /tmp/dotnet-install.sh \
    && bash /tmp/dotnet-install.sh --channel $DOTNET_CHANNEL --install-dir $HOME/.dotnet \
    && rm /tmp/dotnet-install.sh
ENV DOTNET_ROOT=$HOME/.dotnet
ENV PATH=$HOME/.dotnet:$PATH
ENV DOTNET_CLI_TELEMETRY_OPTOUT=1
ENV DOTNET_NOLOGO=1
RUN echo 'export DOTNET_ROOT=$HOME/.dotnet' \
    | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile
RUN echo 'export PATH=$HOME/.dotnet:$PATH' \
    | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile

# Install OCaml
ARG OCAML_VERSION=5.3.0
RUN opam init --compiler=$OCAML_VERSION --disable-sandboxing
RUN opam option depext-run-installs=true
ENV OPAMYES=1
COPY ./fstar.opam .
RUN opam install --deps-only . && rm fstar.opam
RUN opam install domainslib

# Install Z3
COPY ./.scripts/get_fstar_z3.sh /usr/local/bin
RUN get_fstar_z3.sh ~/bin

# Install copilot-cli
RUN curl -fsSL https://gh.io/copilot-install | bash

# Instrument .profile and .bashrc to set the opam switch. Note that this
# just appends the *call* to eval $(opam env) in these files, so we
# compute the new environments after the fact.
RUN echo 'eval $(opam env --set-switch)' | tee --append $HOME/.profile $HOME/.bashrc
