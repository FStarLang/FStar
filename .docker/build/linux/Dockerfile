# Fstar build container
FROM everest_base_image:1

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG TARGET

# ADD SSH KEY
RUN mkdir -p ${MYHOME}/.ssh
RUN chown everest ${MYHOME}/.ssh
RUN chmod 700 ${MYHOME}/.ssh
COPY --chown=everest id_rsa ${MYHOME}/.ssh/id_rsa
RUN chmod 600 ${MYHOME}/.ssh/id_rsa
RUN eval $(ssh-agent)

#BUILD FSTAR
RUN mkdir ${MYHOME}/FStar
COPY --chown=everest / ${MYHOME}/FStar/
WORKDIR ${MYHOME}/FStar

RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}
COPY --chown=everest build_fstar.sh ${MYHOME}/FStar/build_fstar.sh
RUN chmod +x build_fstar.sh
COPY --chown=everest build.sh ${MYHOME}/FStar/build.sh
RUN chmod +x build.sh
RUN ./build.sh ${TARGET} ${BUILDLOGFILE} ${MAXTHREADS} || true

RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}

# Generate query-stats.
# List the hints that fail to replay.
RUN bash -c ".scripts/query-stats.py -f ${BUILDLOGFILE} -F html -o log_no_replay.html -n all '--filter=fstar_usedhints=+' '--filter=fstar_tag=-' -g"

# Worst offenders (longest times)
RUN bash -c ".scripts/query-stats.py -f ${BUILDLOGFILE} -F html -o log_worst.html -c -g -n 10"

# Remove ssh identities.
RUN rm ${MYHOME}/.ssh/id_rsa
RUN eval $(ssh-agent) && ssh-add -D