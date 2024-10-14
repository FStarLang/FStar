FROM ubuntu:23.10

RUN apt-get update

RUN apt-get install -y --no-install-recommends \
      git \
      sudo \
      python3 \
      python-is-python3 \
      opam \
      rustc \
      curl \
      ca-certificates \
      rsync \
      wget \
      && apt-get clean -y

RUN useradd -ms /bin/bash user
RUN echo 'user ALL=NOPASSWD: ALL' >> /etc/sudoers
USER user
WORKDIR /home/user

# Install OCaml
ARG OCAML_VERSION=4.14.2
RUN opam init --compiler=$OCAML_VERSION --disable-sandboxing
RUN opam env --set-switch | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile
RUN opam option depext-run-installs=true
ENV OPAMYES=1

# F* dependencies. This is the only place where we read a file from
# the F* repo.
ADD fstar.opam ./fstar.opam
RUN opam install -j$(nproc) --confirm-level=unsafe-yes --deps-only ./fstar.opam && opam clean

# Some karamel dependencies too
RUN opam install -j$(nproc) --confirm-level=unsafe-yes fix fileutils visitors camlp4 wasm ulex uucp ctypes ctypes-foreign && opam clean

RUN sudo apt install time

# Sigh, install dotnet. The setup-dotnet action does not
# work on a container apparently.
ENV DOTNET_ROOT /dotnet
RUN wget -nv https://download.visualstudio.microsoft.com/download/pr/cd0d0a4d-2a6a-4d0d-b42e-dfd3b880e222/008a93f83aba6d1acf75ded3d2cfba24/dotnet-sdk-6.0.400-linux-x64.tar.gz && \
    sudo mkdir -p $DOTNET_ROOT && \
    sudo tar xf dotnet-sdk-6.0.400-linux-x64.tar.gz -C $DOTNET_ROOT && \
    rm -f dotnet-sdk*.tar.gz
RUN sudo ln -s $DOTNET_ROOT/dotnet /usr/local/bin/dotnet

RUN rm fstar.opam # move up

# install rust (move up and remove rustv)
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends llvm-dev libclang-dev clang libgmp-dev pkg-config
RUN . "$HOME/.cargo/env" && rustup component add rustfmt && cargo install bindgen-cli
