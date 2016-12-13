FROM ubuntu:xenial

MAINTAINER Benjamin Beurdouche <benjamin.beurdouche@inria.fr>; Daniel Fabian <daniel.fabian@integral-it.ch>

# Define versions of dependencies
ENV opamv 4.03.0
ENV z3v z3-4.4.1

# Install required packages and set versions
RUN apt-get -qq update
RUN apt-get install --yes sudo libssl-dev libsqlite3-dev g++-5 gcc-5 m4 make opam pkg-config python libgmp3-dev
RUN update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-5 200
RUN update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-5 200

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
RUN opam install ocamlfind batteries sqlite3 fileutils stdint zarith yojson pprint

# Prepare and build Z3
RUN git clone -b ${z3v} https://github.com/Z3Prover/z3.git
WORKDIR z3
RUN python scripts/mk_make.py
WORKDIR build
RUN make
RUN sudo make install
WORKDIR /home/FStar


# Prepare and build F*
ADD update-fstar.sh .
RUN git clone https://github.com/FStarLang/FStar.git
ENV PATH "~/FStar/bin:$PATH"
RUN opam config exec -- make -C FStar/src/ocaml-output
RUN make ocaml -C FStar/src
RUN opam config exec -- make -C FStar/src/ocaml-output

# F* Testing
RUN opam config exec -- make -C FStar/src regressions OTHERFLAGS=--lax