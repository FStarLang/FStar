# Fstar build container

# Define on config.json what base container image build should use.
# By default it always look for the latest container available
# In case you would like to reference a specific commit,
# replace latest with the commit id from github using 12 characters.
ARG DOCKERHUBPROJECT
ARG COMMITID
FROM ${DOCKERHUBPROJECT}everest-ci-windows-nt:${COMMITID}

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG BUILDTARGET
ARG BRANCHNAME

# Add ssh key
# We cannot copy directly to the .ssh folder, instead we copy to a temp folder
WORKDIR "everestsshkey"
COPY id_rsa .
WORKDIR ".."

# Now, using bash we copy the file, set the correct security and remove the previous folder
RUN Invoke-BashCmd '"cd .ssh && cp ../everestsshkey/id_rsa . && chmod 600 id_rsa && rm -rf ../everestsshkey"'

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

COPY build.sh build.sh
COPY build_helper.sh build_helper.sh

RUN Invoke-BashCmd ./build_helper.sh $Env:BUILDTARGET $Env:BUILDLOGFILE $Env:MAXTHREADS $Env:BRANCHNAME '||' true

# Remove ssh key.
RUN Invoke-BashCmd rm .ssh/id_rsa
