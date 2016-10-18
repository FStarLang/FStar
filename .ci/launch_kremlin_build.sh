#!/bin/bash 
BRANCH=`git branch | cut -d ' ' -f2`

echo "Branch : $BRANCH"

if [[ "$BRANCH" == "master" ]]; then 
    set body='{
    "request": {
    "branch":"master"
    }}';

    echo "Triggering Kremlin Travis build -- "
    curl -s -X POST \
    -H "Content-Type: application/json" \
    -H "Accept: application/json" \
    -H "Travis-API-Version: 3" \
    -H "Authorization: token $(TRAVIS_TOKEN)" \
    -d "$body" \
    https://api.travis-ci.org/repo/FStarLang%2Fkremlin/requests;

    echo "Travis build trigger complete"
fi 
