# Fstar build container
FROM everest_windows_base_image:1

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG TARGET

#USER "NT AUTHORITY\SYSTEM"

#BUILD FSTAR
RUN md ${MYHOME}\FStar
COPY / ${MYHOME}/FStar/
WORKDIR ${MYHOME}/FStar

RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}
COPY build_fstar_with_regressions.sh ${MYHOME}/FStar/build_fstar_with_regressions.sh
RUN c:\Cygwin64\bin\bash.exe --login -c "cd FStar && ./build_fstar_with_regressions.sh ${TARGET} ${BUILDLOGFILE} ${MAXTHREADS}"

RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}

# Generate query-stats.
# List the hints that fail to replay.
RUN c:\Cygwin64\bin\bash.exe --login -c "cd FStar && .scripts/query-stats.py -f ${BUILDLOGFILE} -F html -o log_no_replay.html -n all '--filter=fstar_usedhints=+' '--filter=fstar_tag=-' -g"

# Worst offenders (longest times)
RUN c:\Cygwin64\bin\bash.exe --login -c "cd FStar && .scripts/query-stats.py -f ${BUILDLOGFILE} -F html -o log_worst.html -c -g -n 10"