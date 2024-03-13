FROM rust:latest

WORKDIR /usr/src/hacl
RUN apt-get update
RUN apt-get install --yes --no-install-recommends llvm-dev libclang-dev clang
RUN rustup component add rustfmt
RUN cargo install bindgen-cli
ADD c/*.h .
ADD krmllib.h .
RUN for f in EverCrypt*.h ; do bindgen -o $(basename $f .h).rs --allowlist-file 'EverCrypt.*' $f ; done
