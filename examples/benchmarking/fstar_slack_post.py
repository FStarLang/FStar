#!/usr/bin/env python3

import argparse
import json
import numpy as np
import os
import pandas as pd
import re
import urllib.error
import urllib.parse
import urllib.request


DEFAULT_GITHUB_COMMIT_LOC='https://github.com/FStarLang/FStar/commit/'
DEFAULT_CODESPEED_REV_FMT='http://bench2.ocamllabs.io:8070/changes/?rev=%s'
RED_THRESH = 20. # percentage change of all benchmarks worse than this
GREY_THRESH = 10. # percentage change of a benchmark worse than this

# create app here:
#   https://api.slack.com/incoming-webhooks#

parser = argparse.ArgumentParser(description='Post a message to a slack webhook')
parser.add_argument('url', type=str, help='webhook url to post to')
parser.add_argument('last_daily_dir', type=str, help='directory with last daily data (e.g. /local/scratch/ctk21/FStar_bench/daily)')
parser.add_argument('--github_commit_loc', type=str, help='web link for finding github commits (e.g. %s)'%DEFAULT_GITHUB_COMMIT_LOC, default=DEFAULT_GITHUB_COMMIT_LOC)
parser.add_argument('--codespeed_rev_fmt', type=str, help='web link for codespeed changes page (e.g. %s)'%DEFAULT_CODESPEED_REV_FMT, default=DEFAULT_CODESPEED_REV_FMT)
parser.add_argument('--dry_run', action='store_true', default=False)
parser.add_argument('-v', '--verbose', action='store_true', default=False)

args = parser.parse_args()

def get_dir_sorted_by_creation(d, filter=None):
    xs = os.listdir(d)
    if not filter is None:
        xs = [x for x in xs if filter(x)]
    xs = [os.path.join(d, x) for x in xs]
    xs = [(x, os.path.getctime(x)) for x in xs]
    xs = sorted(xs, key=lambda xy: xy[1])
    return [xy[0] for xy in xs]

def get_result_dir_from_run(d):
    hash_dir = get_dir_sorted_by_creation(
        d,
        filter=lambda x: not x.startswith('logfile')
    )[-1]
    return os.path.join(hash_dir, 'bench_results')

## work out last two daily commits
new_daily_dir = os.path.abspath(args.last_daily_dir)

datestamp_pat = re.compile('[0-9]{8}_[0-9]{6}')
new_daily_results = get_result_dir_from_run(new_daily_dir)

# figure out the last daily run before new as the base
new_timestamp = os.path.basename(new_daily_dir)
old_daily_results = get_dir_sorted_by_creation(
        os.path.dirname(new_daily_dir),
        filter=lambda x: (not datestamp_pat.match(x) is None) and (x < new_timestamp)
    )[-1]
old_daily_results = get_result_dir_from_run(old_daily_results)

def get_hash_from_result_dir(d):
    d = os.path.dirname(d) ## remove 'result_dir'
    return os.path.basename(d)[0:12]

new_short_hash = get_hash_from_result_dir(new_daily_results)
old_short_hash = get_hash_from_result_dir(old_daily_results)

if args.verbose:
    print('Will compare [new=%s] %s vs [old=%s] %s'%(new_short_hash, new_daily_results, old_short_hash, old_daily_results))

## load csv files
def load_results(dir, files=['ulib.csv', 'ocaml_extract.csv', 'micro-benchmarks.csv'], verbose=args.verbose):
    dfs = []
    for f in [os.path.join(dir, f) for f in files]:
        if os.path.exists(f):
            if verbose: print('loading: %s'%f)
            df = pd.read_csv(f, header=0)
            prefix = os.path.basename(f).split('.')[0] + '/'
            df['name'] = prefix + df['name']
            dfs.append(df)
        else:
            print("WARN: couldn't find %s"%f)
    df = pd.concat(dfs, ignore_index=True)
    if verbose:
        df.info()
        print(df.head(3).T)
    return df

new_df = load_results(new_daily_results)
old_df = load_results(old_daily_results)

## filter to valid
good_names = np.intersect1d(new_df.name.values, old_df.name.values)
new_df = new_df[new_df['name'].isin(good_names)]
old_df = old_df[old_df['name'].isin(good_names)]

if args.verbose:
    print('filtered new_df and old_df to %s good names'%str(len(good_names)))

## calculate changes
new_df = new_df.set_index('name')
old_df = old_df.set_index('name')

change_data = 100.*(new_df['time_secs']-old_df['time_secs'])/old_df['time_secs']
change_data = change_data.sort_values()

message_str = 'Performance of <%s|%s> [new] compared with <%s|%s> [old]:\n' % (args.github_commit_loc+new_short_hash, new_short_hash, args.github_commit_loc+old_short_hash, old_short_hash)

## calculate top 3 improves, bottom 3 worst
def long_pre_fn(title, series):
    s = title + '\n'
    s += '```\n'
    for index, value in series.items():
        s += '   %-48s %6.2f%%\n'%(index, value)
    s += '```\n'
    return s

def simple_compact_fn(title, series):
    return '```' + title + '\n  ' + ', '.join(['%s %.1f%%'%(index,value) for index,value in series.items()] ) + '```\n'

N = 3
#print('Best %s improvements:\n %s'%(str(N), change_data.head(N)))
#print('Worst %s regressions:\n %s'%(str(N), change_data.tail(N)))

fn = simple_compact_fn
best_worst_str = ''
best_worst_str += fn('Best %s changes in runtime:'%str(N), change_data.head(N))
best_worst_str += fn('Worst %s changes in runtime:'%str(N), change_data.sort_values(ascending=False).head(N))
print(best_worst_str)

message_str += best_worst_str

## calculate best|25|50|75|worst
quants = [0., 0.25, 0.5, 0.75, 1.]
quantile_str = '```\n'
quantile_str += 'quantiles ' + '|'.join(['%7.0f '%(x*100.) for x in quants]) + '\n'
quantile_str += '          ' + '|'.join(['%6.2f%% '%x for x in change_data.quantile(quants)]) + '\n'
quantile_str += '```\n'
print(quantile_str)

message_str += quantile_str

full_results_str = '<%s|All results and graphs>\n' %(args.codespeed_rev_fmt%(new_short_hash[0:7]))

def color_code(df):
    if (df > RED_THRESH).all():
        color_code = 'danger'
    elif (df > GREY_THRESH).any():
        color_code = ''
    else:
        color_code = 'good'
    return color_code

color_code_str = color_code(change_data)

def create_slack_text_message(s):
    return {'text': s}

# see https://api.slack.com/docs/message-attachments
# (color can be 'good'(green), 'warning'(orange), 'danger'(red), ''(grey))
def create_slack_attachment_message(fallback, color, text, footer):
    return  {
             "attachments": [
                {
                    "fallback": fallback,
                    "color": color,
                    "text": text,
                    "footer":footer
                }
             ]
            }


def post_data_to_webhook(url, json_data, dry_run=args.dry_run, verbose=args.verbose):

    data_payload = json.dumps(json_data).encode('ascii')

    if dry_run:
        print('DRY_RUN would have sent request: ')
        print(' url: %s'%url)
        print(' data: %s'%data_payload)
        return

    if verbose:
        print('requesting url=%s  data=%s'%(url, data_payload))

    try:
        req = urllib.request.Request(
            url,
            headers={'Content-Type': 'application/json'},
            data=data_payload)
        f = urllib.request.urlopen(req)
    except urllib.error.HTTPError as e:
        print("EXCEPTION: " + str(e))
        print(e.read())
        return
    response = f.read()
    f.close()

    print("Server (%s) response: %s\n" % (url, response))

if args.verbose:
    print('going to send:')
    print(message_str)

#post_data_to_webhook(args.url, create_slack_text_message(message_str+full_results_str))
post_data_to_webhook(args.url, create_slack_attachment_message(fallback='', color=color_code_str, text=message_str+full_results_str, footer='-ve new faster/+ve new slower'))


