# Fstar build container
FROM everest_base_image:1

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG TARGET
ARG BRANCHNAME
ARG FSTARSOURCEVERSION

# ADD SSH KEY
RUN mkdir -p ${MYHOME}/.ssh
RUN chown everest ${MYHOME}/.ssh
RUN chmod 700 ${MYHOME}/.ssh
COPY --chown=everest id_rsa ${MYHOME}/.ssh/id_rsa
RUN chmod 600 ${MYHOME}/.ssh/id_rsa
RUN eval $(ssh-agent)

# Copy FSTAR source code.
RUN mkdir ${MYHOME}/FStar
COPY --chown=everest / ${MYHOME}/FStar/

WORKDIR ${MYHOME}

# Remove extra files.
RUN rm ${MYHOME}/FStar/Dockerfile
RUN rm ${MYHOME}/FStar/build.sh
RUN rm ${MYHOME}/FStar/build_helper.sh
RUN rm ${MYHOME}/FStar/id_rsa
RUN rm ${MYHOME}/FStar/commitinfofilename.json

COPY --chown=everest build.sh ${MYHOME}/build.sh
RUN chmod +x build.sh
COPY --chown=everest build_helper.sh ${MYHOME}/build_helper.sh
RUN chmod +x build_helper.sh

RUN ./build_helper.sh ${TARGET} ${BUILDLOGFILE} ${MAXTHREADS} ${BRANCHNAME} ${FSTARSOURCEVERSION} || true

# Remove ssh key
RUN rm .ssh/id_rsa