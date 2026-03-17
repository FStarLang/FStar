#!/bin/bash

exec
sed -n '/\* Error/,/^$/p
	/\* Warning 19/,/^$/p
	/\* Warning 303/,/^$/p
	/\* Warning 359/,/^$/p
	/Unexpected error/,/^$/p' "$@"
