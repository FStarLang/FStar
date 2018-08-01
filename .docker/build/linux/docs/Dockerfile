# Fstar docs container used to build fstar documentation.
# Docs should always use the latest fstar image available.
FROM fstar:latest

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG TARGET

#BUILD FSTAR Docs
RUN rm -f ${BUILDLOGFILE}
RUN rm -f log_no_replay.html
RUN rm -f log_worst.html
RUN rm -f orange_status.txt
RUN rm -f result.txt
RUN rm -f status.txt
RUN rm -f commitinfofilename.json

WORKDIR ${MYHOME}/FStar

# ADD SSH KEY
RUN eval $(ssh-agent)
COPY --chown=everest id_rsa ${MYHOME}/FStar/id_rsa
RUN ssh-add -k ${MYHOME}/FStar/id_rsa
RUN rm ${MYHOME}/FStar/id_rsa

# Build FStar docs
RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}
COPY --chown=everest build_fstar.sh ${MYHOME}/FStar/build_fstar.sh
RUN chmod +x build_fstar.sh
COPY --chown=everest build.sh ${MYHOME}/FStar/build.sh
RUN chmod +x build.sh
RUN ./build.sh ${TARGET} ${BUILDLOGFILE} ${MAXTHREADS} || true

RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}

# Remove ssh identities.
RUN ssh-add -D