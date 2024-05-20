FROM rust:latest

WORKDIR /usr/src/hacl
RUN apt-get update
RUN apt-get install --yes --no-install-recommends llvm-dev libclang-dev clang
RUN rustup component add rustfmt
RUN cargo install bindgen-cli
ADD _output/*.h .
ADD krmllib.h .
ADD compat.h .
RUN bindgen -o evercrypt_gen.rs --allowlist-file '.*EverCrypt.*' bindings.h --dynamic-loading "evercrypt" --dynamic-link-require-all
RUN bindgen -o l0core_gen.rs --allowlist-file '.*L0Core.*' bindings.h --dynamic-loading "l0" --dynamic-link-require-all
