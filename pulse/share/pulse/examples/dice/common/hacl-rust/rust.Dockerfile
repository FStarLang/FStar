FROM rust:latest

WORKDIR /usr/src/hacl
RUN apt-get update
RUN apt-get install --yes --no-install-recommends llvm-dev libclang-dev clang
RUN rustup component add rustfmt
RUN cargo install bindgen-cli
ADD c/*.h .
ADD krmllib.h .
RUN bindgen -o evercrypt.rs --allowlist-file '.*EverCrypt.*' bindings.h
