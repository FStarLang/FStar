FROM ubuntu:18.04

MAINTAINER Benjamin Beurdouche <benjamin.beurdouche@inria.fr>; Victor Dumitrescu <victor.dumitrescu@nomadic-labs.com>; Daniel Fabian <daniel.fabian@integral-it.ch>;

# Install required packages
RUN apt-get -qq update
RUN apt-get install -y software-properties-common
RUN add-apt-repository -y ppa:avsm/ppa # for opam 2
RUN apt-get -qq update
RUN apt-get install -y sudo wget libssl-dev libsqlite3-dev g++ gcc m4 make opam pkg-config python libgmp3-dev unzip cmake

# Create user
RUN useradd -ms /bin/bash build
RUN echo "build ALL=(ALL:ALL) NOPASSWD:ALL" >> /etc/sudoers
USER build
WORKDIR /home/build

# Prepare and build OPAM and OCaml
RUN opam init -y --disable-sandboxing --compiler=4.07.0
RUN opam update
RUN opam install -y ocamlbuild ocamlfind batteries stdint zarith yojson fileutils pprint menhir ulex ppx_deriving ppx_deriving_yojson process pprint visitors fix wasm

# Prepare and build Z3
ENV z3=z3-4.8.5-x64-debian-8.11
ADD https://github.com/FStarLang/binaries/raw/master/z3-tested/${z3}.zip .
RUN sudo unzip ${z3}.zip
ENV PATH=/home/build/${z3}/bin:${PATH}
WORKDIR /home/build

# Prepare and build F*
ADD update-fstar.sh .
RUN git clone https://github.com/FStarLang/FStar.git --depth=1
ENV FSTAR_HOME=/home/build/FStar
WORKDIR $FSTAR_HOME
RUN opam config exec -- make
WORKDIR /home/build
