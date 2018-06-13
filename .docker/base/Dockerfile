FROM ubuntu:bionic

MAINTAINER Benjamin Beurdouche <benjamin.beurdouche@inria.fr>; Daniel Fabian <daniel.fabian@integral-it.ch>

# Define versions of dependencies
ENV opamv 4.05.0
ENV z3v 4.5.1.1f29cebd4df6-x64-ubuntu-14.04

# Install required packages and set versions
RUN apt-get -qq update
RUN apt-get install --yes sudo wget libssl-dev libsqlite3-dev g++ gcc m4 make opam pkg-config python libgmp3-dev unzip

# Create user
RUN useradd -ms /bin/bash FStar
RUN echo "FStar ALL=(ALL:ALL) NOPASSWD:ALL" >> /etc/sudoers
USER FStar
WORKDIR /home/FStar

# Prepare build (OCaml packages)
ENV OPAMYES true
RUN opam init
RUN echo ". /home/FStar/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true" >> .bashrc
RUN opam switch ${opamv}
RUN opam install ocamlfind batteries sqlite3 fileutils stdint zarith yojson pprint menhir ulex ppx_deriving ppx_deriving_yojson process

# Prepare and build Z3
RUN wget https://github.com/FStarLang/binaries/raw/master/z3-tested/z3-${z3v}.zip
RUN unzip z3-${z3v}.zip
RUN mv z3-${z3v} z3
ENV PATH "/home/FStar/z3/bin:$PATH"
WORKDIR /home/FStar

# Prepare and build F*
ADD update-fstar.sh .
RUN git clone https://github.com/FStarLang/FStar.git --depth=1
ENV PATH "~/FStar/bin:$PATH"
RUN opam config exec -- make -C FStar/src/ocaml-output
