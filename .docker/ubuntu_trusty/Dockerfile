FROM ubuntu:trusty

MAINTAINER Benjamin Beurdouche <benjamin.beurdouche@inria.fr>


# Define versions of dependencies
ENV opamv 4.02.3
ENV z3v z3-4.4.1

# Define working directory
RUN mkdir -p /worker
WORKDIR /worker

# Repositories required specifically for opam on Ubuntu
RUN apt-get -qq update
RUN apt-get --yes install software-properties-common
RUN add-apt-repository --yes ppa:avsm/ppa

# Repositories required specifically for opam on Ubuntu 14.04 (Deprecated OpenSSL)
RUN add-apt-repository --yes ppa:ubuntu-toolchain-r/test
RUN add-apt-repository --yes ppa:0k53d-karl-f830m/openssl
RUN apt-get -qq update

# Install required packages and set versions
RUN apt-get install --yes libssl-dev libsqlite3-dev g++-5 gcc-5 m4 make opam pkg-config python
RUN update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-5 200
RUN update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-5 200

# Prepare build (OCaml packages)
ENV OPAMYES true
RUN opam init
RUN eval $(opam config env)
RUN opam switch ${opamv}
RUN eval $(opam config env)
RUN opam install ocamlfind batteries sqlite3 fileutils stdint
RUN eval $(opam config env)

# Prepare Z3
ENV z3v ${z3v}-x64-ubuntu-14.04
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.4.1/${z3v}.zip
RUN unzip ${z3v}.zip
ENV PATH "/worker/${z3v}/bin:$PATH"

# Prepare and build F*
RUN git clone https://github.com/FStarLang/FStar.git
ENV PATH "/worker/FStar/bin:$PATH"
WORKDIR FStar
RUN opam config exec -- make -C src/ocaml-output

# F* Testing
RUN opam config exec -- make -C examples/unit-tests
RUN opam config exec -- make -C src regressions OTHERFLAGS=--lax