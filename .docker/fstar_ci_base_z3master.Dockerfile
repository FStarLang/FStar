FROM fstar_ci_base

RUN git clone https://github.com/Z3Prover/z3
COPY .docker/Z3.patch .
WORKDIR z3
RUN git am ../Z3.patch

RUN ./configure

ARG CI_THREADS=12
RUN make -C build -j$(nproc)

USER root
RUN make -C build install
USER opam
