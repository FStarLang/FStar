#!/usr/bin/env bash

# Look for config.json file
FILE=".docker/build/config.json"
if [ ! -f $FILE ]; then
   echo "File $FILE does not exist."
fi

# In case you want to build windows, change agentOS here to windows-nt
agentOS=Linux
DOCKERFILE=$(jq -c -r ".DockerFile" "$FILE")
DOCKERFILE=$( echo ${DOCKERFILE} | sed "s/{agentOS}/${agentOS}/g" )

# Copy dockerfile to root
cp $DOCKERFILE ./Dockerfile

# Copy dependencies
DEPFILES=$(jq -c -r ".DependencyFiles[]" "$FILE")
cp -r $DEPFILES .

PROJECTNAME=$(jq -c -r ".ProjectName" "$FILE" | awk '{print tolower($0)}')
BUILDTARGET=$(jq -c -r ".CIBuildTarget" "$FILE")
LOCALBRANCHNAME=$(git branch | grep \* | cut -d ' ' -f2)

#Find commit id.
REQUESTEDBRANCHNAME=$(jq -c -r ".BranchName" "$FILE")
REQUESTEDCOMMITID=$(jq -c -r ".BaseContainerImageTagOrCommitId" "$FILE")
COMMITURL=$(jq -c -r ".GithubCommitUrl" "$FILE")/$REQUESTEDBRANCHNAME

if [ $(jq -c -r ".GithubCommitUrl" "$FILE") -ne "latest" ]; then
    COMMITURL=$(jq -c -r ".GithubCommitUrl" "$FILE")/$REQUESTEDCOMMITID
fi

CONTENT=$(curl $COMMITURL)
FULLCOMMITID="$( echo ${CONTENT} | sed 's/.*commit\/\([^"]*\).*/\1/g' )"
COMMITID=${FULLCOMMITID:0:12}

# create fake files ssh key, commitinfofilename.json, etc
echo "fake" > id_rsa
echo "fake" > commitinfofilename.json

# build container
docker build --file Dockerfile --build-arg BUILDLOGFILE="buildlogfile.txt" --build-arg MAXTHREADS="8" --build-arg TARGET="$BUILDTARGET" --build-arg BRANCHNAME="$LOCALBRANCHNAME" --build-arg COMMITID="$COMMITID" --build-arg DOCKERHUBPROJECT="projecteverest/" --tag "$PROJECTNAME:local" .

# delete fake files
rm -f id_rsa
rm -f commitinfofilename.json

# Remove dep files.
for f in $DEPFILES; do rm -f $(basename $f); done

# delete dockerfile
rm -f Dockerfile