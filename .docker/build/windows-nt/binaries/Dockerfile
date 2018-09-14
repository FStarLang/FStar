# Fstar binaries container used to build fstar binaries.
# Binaries should always use the latest fstar image available.
FROM fstar-windows-nt:latest

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

# Remove extra files.
RUN Invoke-BashCmd rm -f $Env:BUILDLOGFILE
RUN Invoke-BashCmd rm -f log_no_replay.html
RUN Invoke-BashCmd rm -f log_worst.html
RUN Invoke-BashCmd rm -f orange_status.txt
RUN Invoke-BashCmd rm -f result.txt
RUN Invoke-BashCmd rm -f status.txt
RUN Invoke-BashCmd rm -f commitinfofilename.json

COPY build.sh build.sh
COPY build_helper.sh build_helper.sh

RUN Invoke-BashCmd ./build_helper.sh $Env:TARGET $Env:BUILDLOGFILE $Env:MAXTHREADS $Env:BRANCHNAME $Env:FSTARSOURCEVERSION '||' true

# Remove ssh key.
RUN Invoke-BashCmd rm .ssh/id_rsa