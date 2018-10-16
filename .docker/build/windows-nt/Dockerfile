# Fstar build container
FROM everest-base-windows-nt:1

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

RUN Invoke-BashCmd ./build_helper.sh $Env:TARGET $Env:BUILDLOGFILE $Env:MAXTHREADS $Env:BRANCHNAME $Env:FSTARSOURCEVERSION '||' true

# Remove ssh key.
RUN Invoke-BashCmd rm .ssh/id_rsa