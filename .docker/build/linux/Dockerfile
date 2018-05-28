# Fstar build container
FROM everest_base_image:1

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG TARGET

#BUILD FSTAR
RUN mkdir ${MYHOME}/FStar
COPY --chown=everest / ${MYHOME}/FStar/
RUN rm -rf  ${MYHOME}/FStar/.git
WORKDIR ${MYHOME}/FStar

RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}
COPY --chown=everest build_fstar_with_regressions.sh ${MYHOME}/FStar/build_fstar_with_regressions.sh
RUN chmod +x build_fstar_with_regressions.sh
RUN ./build_fstar_with_regressions.sh ${TARGET} ${BUILDLOGFILE} ${MAXTHREADS}

RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}

# Generate query-stats.
# List the hints that fail to replay.
RUN bash -c ".scripts/query-stats.py -f ${BUILDLOGFILE} -F html -o log_no_replay.html -n all '--filter=fstar_usedhints=+' '--filter=fstar_tag=-' -g"

# Worst offenders (longest times)
RUN bash -c ".scripts/query-stats.py -f ${BUILDLOGFILE} -F html -o log_worst.html -c -g -n 10"