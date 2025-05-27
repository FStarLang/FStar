FROM ubuntu:24.04

SHELL ["/bin/bash", "-c"]

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
    && apt-get clean -y
# FIXME: libgmp-dev should be installed automatically by opam,
# but it is not working, so just adding it above.
# Same for pkg-config. OPAM prompts even if we're giving --yes
# and setting OPAMYES.

# Create a new user and give them sudo rights
ARG USER=vscode
RUN useradd -d /home/$USER -s /bin/bash -m $USER
RUN echo "$USER ALL=NOPASSWD: ALL" >> /etc/sudoers
USER $USER
ENV HOME /home/$USER
WORKDIR $HOME
RUN mkdir -p $HOME/bin

# Make sure ~/bin is in the PATH
RUN echo 'export PATH=$HOME/bin:$PATH' | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile

# Install OCaml
ARG OCAML_VERSION=4.14.0
RUN opam init --compiler=$OCAML_VERSION --disable-sandboxing
RUN opam option depext-run-installs=true
ENV OPAMYES=1
RUN opam install --yes batteries zarith stdint yojson dune menhir menhirLib pprint sedlex ppxlib process ppx_deriving ppx_deriving_yojson memtrace

# Get F* master and build (install opam deps too)
RUN eval $(opam env) \
 && source $HOME/.profile \
 && git clone --depth=1 https://github.com/FStarLang/FStar \
 && cd FStar/ \
 && opam install --deps-only ./fstar.opam \
 && make -j$(nproc) ADMIT=1 \
 && ln -s $(realpath bin/fstar.exe) $HOME/bin/fstar.exe

# Install z3 with F* script
RUN ./FStar/.scripts/get_fstar_z3.sh $HOME/bin

# Get karamel master and build (installing opam deps too, but ignoring fstar dependency)
RUN eval $(opam env) \
 && source $HOME/.profile \
 && git clone --depth=1 https://github.com/FStarLang/karamel \
 && cd karamel/ \
 && sed -i '/"fstar"/d' karamel.opam \
 && opam install --deps-only ./karamel.opam \
 && .docker/build/install-other-deps.sh \
 && make -j$(nproc)

ENV FSTAR_EXE  $HOME/FStar/bin/fstar.exe
ENV KRML_HOME $HOME/karamel

# Instrument .profile and .bashrc to set the opam switch. Note that this
# just appends the *call* to eval $(opam env) in these files, so we
# compute the new environments after the fact.
RUN echo 'eval $(opam env --set-switch)' | tee --append $HOME/.profile
RUN echo 'eval $(opam env --set-switch)' | tee --append $HOME/.bashrc

# We do not build Pulse itself, the devcontainer does that on spinup,
# on the up-to-date files.
