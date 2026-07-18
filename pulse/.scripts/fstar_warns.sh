#!/bin/bash

exec
sed -n '/\* Error/,/^$/p
	/\* Warning/,/^$/p
	/Unexpected error/,/^$/p' "$@"
