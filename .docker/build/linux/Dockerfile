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

RUN { { { stdbuf -i0 -o0 -e0 make -C src -j ${MAXTHREADS} utest-prelude && echo "success" > "result.txt" || echo "failure" > "result.txt" ; } 3>&1 1>&2 2>&3 | stdbuf -i0 -o0 -e0 sed 's!^![STDERR] !' ; } 3>&1 1>&2 2>&3 | stdbuf -i0 -o0 -e0 sed 's!^![STDOUT] !' ; } 2>&1 | stdbuf -i0 -o0 -e0 tee --append ${BUILDLOGFILE}

RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}

# Generate query-stats.
# List the hints that fail to replay.
RUN bash -c ".scripts/query-stats.py -f ${BUILDLOGFILE} -F html -o log_no_replay.html -n all '--filter=fstar_usedhints=+' '--filter=fstar_tag=-' -g"

# Worst offenders (longest times)
RUN bash -c ".scripts/query-stats.py -f ${BUILDLOGFILE} -F html -o log_worst.html -c -g -n 10"
