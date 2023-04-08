# This Dockerfile should be run from the root FStar directory
# It regenerates the hints and the version number

# Build the package
ARG ocaml_version=4.12

FROM ocaml/opam:ubuntu-20.04-ocaml-$ocaml_version AS fstarbuild

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
RUN opam depext conf-gmp z3.4.8.5 conf-m4

ADD --chown=opam:opam ./fstar.opam fstar.opam

# Install opam dependencies only
RUN opam install --deps-only ./fstar.opam && \
    rm fstar.opam

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

# Download Karamel and install its dependencies
# We don't build Karamel here, advance.sh will take care of it
RUN git clone https://github.com/FStarLang/karamel karamel && \
    cd ./karamel && .docker/build/install-other-deps.sh
ENV KRML_HOME /home/opam/karamel

# More CI dependencies:
# python3 (for interactive tests)
RUN sudo apt-get update && \
    sudo apt-get install -y --no-install-recommends \
    python3 \
    python-is-python3

ADD --chown=opam:opam ./ FStar/

# Regenerate hints
ARG CI_THREADS=24
RUN --mount=type=secret,id=DZOMO_GITHUB_TOKEN eval $(opam env) && env CI_THREADS=$CI_THREADS DZOMO_GITHUB_TOKEN=$(sudo cat /run/secrets/DZOMO_GITHUB_TOKEN) ./FStar/.scripts/advance.sh build_and_refresh
