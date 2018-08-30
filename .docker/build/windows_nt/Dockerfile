# Fstar build container
FROM everest_base_image:1

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG TARGET
ARG BRANCHNAME
ARG FSTARSOURCEVERSION

# Add ssh key
# We cannot copy directly to the .ssh folder, instead we copy to a temp folder
WORKDIR "everestsshkey"
COPY id_rsa .
WORKDIR ".."

# Now, using bash we copy the file, set the correct security and remove the previous folder
RUN Invoke-BashCmd '"cd .ssh && cp ../everestsshkey/id_rsa . && chmod 600 id_rsa && rm -rf ../everestsshkey"'

COPY build.sh build.sh
COPY build_helper.sh build_helper.sh

# Copy FSTAR source code.
WORKDIR "FStar"
COPY / .

# Remove extra files.
RUN Invoke-BashCmd rm Dockerfile
RUN Invoke-BashCmd rm build.sh
RUN Invoke-BashCmd rm build_helper.sh
RUN Invoke-BashCmd rm id_rsa
RUN Invoke-BashCmd rm commitinfofilename.json
WORKDIR ".."

RUN Invoke-BashCmd echo "$(date -u """+%Y-%m-%d %H:%M:%S""")" | Add-Content $Env:BUILDLOGFILE
RUN Invoke-BashCmd echo "FStar source version: $Env:FSTARSOURCEVERSION" | Add-Content $Env:BUILDLOGFILE
RUN Invoke-BashCmd ./build_helper.sh "$Env:TARGET" "$Env:BUILDLOGFILE" "$Env:MAXTHREADS" "$Env:BRANCHNAME" '||' true
RUN Invoke-BashCmd echo "$(date -u """+%Y-%m-%d %H:%M:%S""")" | Add-Content $Env:BUILDLOGFILE

# Remove ssh key.
RUN Invoke-BashCmd '"cd .ssh && rm -f id_rsa"'

# Generate query-stats.
# List the hints that fail to replay.
RUN Invoke-BashCmd "FStar/.scripts/query-stats.py -f $Env:BUILDLOGFILE -F html -o log_no_replay.html -n all '\"'--filter=fstar_usedhints=+'\"' '\"'--filter=fstar_tag=-'\"' -g"

# Worst offenders (longest times)
RUN Invoke-BashCmd "FStar/.scripts/query-stats.py -f $Env:BUILDLOGFILE -F html -o log_worst.html -c -g -n 10"

RUN dir