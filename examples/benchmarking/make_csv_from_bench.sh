#!/bin/sh

FIELDS=('name', 'time_secs', 'user_time_secs', 'sys_time_secs', 'maxrss_kB', 'gc.allocated_words', 'gc.minor_words', 'gc.promoted_words', 'gc.major_words', 'gc.minor_collections', 'gc.major_collections', 'gc.heap_words', 'gc.heap_chunks', 'gc.top_heap_words', 'gc.compactions')

HEADER=$(printf "%s" ${FIELDS[@]})
JQ_ARGS=$(printf ".%s" ${FIELDS[@]})

echo $HEADER
jq -s -r "[$HEADER], .[] | [$JQ_ARGS] | @csv"

#echo '.name,time_secs,user_time_secs,sys_time_secs,maxrss_kB,gc.allocated_words,gc.minor_words,gc.promoted_words,gc.major_words,gc.minor_collections,gc.major_collections,gc.heap_words,gc.heap_chunks,gc.top_heap_words,gc.compactions'
#jq -s -r '.[] | [.name, .time_secs, .user_time_secs, .sys_time_secs, .maxrss_kB, .gc.allocated_words, .gc.minor_words, .gc.promoted_words, .gc.major_words, .gc.minor_collections, .gc.major_collections, .gc.heap_words, .gc.heap_chunks, .gc.top_heap_words, .gc.compactions] | @csv'
