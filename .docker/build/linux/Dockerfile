# Fstar build container
FROM everest_base_image:1

ARG BUILDLOGFILE
ARG MAXTHREADS

#BUILD FSTAR
RUN mkdir ${MYHOME}/FStar
COPY --chown=everest / ${MYHOME}/FStar/
RUN rm -rf  ${MYHOME}/FStar/.git
WORKDIR ${MYHOME}/FStar
RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}

# For anything printed on stdout or stderr, prepend each line with
# stdout or stderr accordingly, then gather everything and get
# everything printed to both the log file and stdout.  `stdbuf` avoids
# buffering, to preserve interleaving as much as possible. `3>&1 1>&2
# 2>&3` actually swaps stdout and stderr, because `|` only works on
# stdout.
RUN { { { stdbuf -i0 -o0 -e0 make -C src -j ${MAXTHREADS} utest-prelude && echo "success" > "result.txt" || echo "failed" > "result.txt" ; } 3>&1 1>&2 2>&3 | stdbuf -i0 -o0 -e0 sed 's!^![STDERR] !' ; } 3>&1 1>&2 2>&3 | stdbuf -i0 -o0 -e0 sed 's!^![STDOUT] !' ; } 2>&1 | stdbuf -i0 -o0 -e0 tee --append ${BUILDLOGFILE}

RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}


