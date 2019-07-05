#!/usr/bin/env python3

import argparse
import datetime
import glob
import inspect
import json
import os
import pandas
import subprocess
import sys

import codespeed_upload

def get_script_dir():
    return os.path.dirname(inspect.getabsfile(get_script_dir))

SCRIPTDIR = get_script_dir()
DEFAULT_REPO = os.path.join(SCRIPTDIR, 'FStar') ## TODO: what should this be
DEFAULT_BENCHMARK_RUN_SCRIPT = 'make_bench_results.sh' ## TODO: what should this be
DEFAULT_BRANCH = 'master'
ENVIRONMENT = 'bench_machine'
CODESPEED_URL = 'http://localhost:8070/'

parser = argparse.ArgumentParser(description='Run FStar benchmarks across multiple git commits')
parser.add_argument('outdir', type=str, help='directory of output')
parser.add_argument('--benchmark_run_script', type=str, help='benchmark run script', default=DEFAULT_BENCHMARK_RUN_SCRIPT)
parser.add_argument('--repo', type=str, help='local location of Fstar repo (default: %s)'%DEFAULT_REPO, default=DEFAULT_REPO)
parser.add_argument('--repo_branch', type=str, help='git branch for the compiler (default: %s)'%DEFAULT_BRANCH, default=DEFAULT_BRANCH)
parser.add_argument('--repo_pull', action='store_true', help="do a pull on the git repo before selecting hashes", default=False)
parser.add_argument('--repo_reset_hard', action='store_true', help="after pulling a branch, reset it hard to the origin. Can need this for remote branches where they have been force pushed", default=False)
parser.add_argument('--commit_after', type=str, help='select commits after the specified date (e.g. 2017-10-02)', default=None)
parser.add_argument('--commit_before', type=str, help='select commits before the specified date (e.g. 2017-10-02)', default=None)
parser.add_argument('--max_hashes', type=int, help='maximum_number of hashes to process', default=16)
parser.add_argument('--benchmark_hook_patch', type=str, help='Patch to try if we don\'t have the benchmark hooks', default=None)
parser.add_argument('--benchmark_no_cleanup', action='store_true', default=False)
parser.add_argument('--run_stages', type=str, help='stages to run', default='bench,upload')
parser.add_argument('--environment', type=str, help='environment tag for run (default: %s)'%ENVIRONMENT, default=ENVIRONMENT)
parser.add_argument('--codespeed_url', type=str, help='codespeed URL for upload', default=CODESPEED_URL)
parser.add_argument('-v', '--verbose', action='store_true', default=False)

args = parser.parse_args()

def shell_exec(cmd, verbose=args.verbose, check=False, stdout=None, stderr=None):
	if verbose:
		print('+ %s'%cmd)
	return subprocess.run(cmd, shell=True, check=check, stdout=stdout, stderr=stderr)

def shell_exec_redirect(cmd, fname, verbose=args.verbose, check=False):
    if verbose:
        print('+ %s'%cmd)
        print('+ with stdout/stderr -> %s'% fname)
    with open(fname, 'w') as f:
        return shell_exec(cmd, verbose=False, check=check, stdout=f, stderr=subprocess.STDOUT)

def get_git_hashes(args):
	old_cwd = os.getcwd()
	repo_path = os.path.abspath(args.repo)
	if args.verbose: print('using repo: %s'%repo_path)
	os.chdir(repo_path)
	shell_exec('git checkout %s'%args.repo_branch)
	if args.repo_pull:
		if args.repo_reset_hard:
			shell_exec('git fetch')
			shell_exec('git reset --hard origin/%s'%args.repo_branch)
		shell_exec('git pull')

	# git date notes:
	#   https://docs.microsoft.com/en-us/azure/devops/repos/git/git-dates?view=azure-devops
	commit_xtra_args = ' --date=local'
	if args.commit_after:
		commit_xtra_args += ' --after %s'%args.commit_after
	if args.commit_before:
		commit_xtra_args += ' --before %s'%args.commit_before

	proc_output = shell_exec('git log %s --pretty=format:\'%%H %%s\' %s | grep "\\[CI\\] regenerate hints + ocaml snapshot"'%(commit_xtra_args, args.repo_branch), stdout=subprocess.PIPE)
	hash_comments = proc_output.stdout.decode('utf-8').split('\n')[::-1]
	hash_comments = filter(bool, hash_comments) # remove empty strings

	hashes = [hc.split(' ')[0] for hc in hash_comments]
	if args.verbose:
		for hc in hash_comments:
			print(hc)

	hashes = [ h for h in hashes if h ] # filter any null hashes
	hashes = hashes[-args.max_hashes:]

	os.chdir(old_cwd)
	return hashes

def parse_and_format_results_for_upload(fname):
    bench_data = []
    with open(fname) as f:
        for l in f:
            raw_data = json.loads(l)
            bench_data.append({
                'name': raw_data['name'],
                'time_secs': raw_data['time_secs'],
                'user_time_secs': raw_data['user_time_secs'],
                'gc.minor_collections': raw_data['gc']['minor_collections'],
                'gc.major_collections': raw_data['gc']['major_collections'],
                'gc.compactions': raw_data['gc'].get('compactions', 0),
                })
    if not bench_data:
        print('WARN: Failed to find any data in %s'%fname)
        return []

    bench_data = pandas.DataFrame(bench_data)
    aggregated_data = bench_data.groupby('name').apply(lambda x: x.describe().T)
    aggregated_data.index.set_names(['bench_name', 'bench_metric'], inplace=True)

    upload_data = []
    for bench_name in aggregated_data.index.levels[0]:
        # TODO: how to make this configurable
        metric_name, metric_units, metric_units_title = ('time_secs', 'seconds', 'Time')

        results = aggregated_data.loc[(bench_name, 'time_secs')]
        upload_data.append({
            'commitid': h[:7],
            'commitid_long': h,
            'project': 'fstar_%s'%args.repo_branch,
            'branch': args.repo_branch,
            'executable': 'fstar',
            'executable_description': 'fstar (%s)'%args.repo_branch,
            'environment': args.environment,
            'benchmark': bench_name,
            'units': metric_units,
            'units_title': metric_units_title,
            'result_value': results['mean'],
            'min': results['min'],
            'max': results['max'],
            'std_dev': results['std'],
            })

    return upload_data


run_timestamp = datetime.datetime.now().strftime('%Y%m%d_%H%M%S')

run_stages = args.run_stages.split(',')
if args.verbose: print('will run stages: %s'%run_stages)

## setup directory
outdir = os.path.abspath(args.outdir)
if args.verbose: print('making directory: %s'%outdir)
shell_exec('mkdir -p %s'%outdir)

## generate list of hash commits
hashes = get_git_hashes(args)

if args.verbose:
	print('Found %d hashes'%len(hashes))

verbose_args = ' -v' if args.verbose else ''
for h in hashes:
	os.chdir(outdir)
	hashdir = os.path.join(outdir, h)
	if args.verbose: print('processing to %s'%hashdir)
	shell_exec('mkdir -p %s'%hashdir)

	fstar_dir = os.path.join(hashdir, 'fstar')

	if 'bench' in run_stages:
		if os.path.exists(fstar_dir):
			print('Skipping fstar setup for %s as directory there'%h)
		else:
			## setup fstar (make a clone and change the hash)
			os.chdir(hashdir)
			shell_exec('git clone --reference %s %s %s'%(args.repo, args.repo, fstar_dir))

			os.chdir(fstar_dir)
			shell_exec('git checkout %s'%h)
			shell_exec('git clean -f -d -x')

			# HACK: dynamically patch the fstar repo to have the benchmark stubs
			if args.benchmark_hook_patch:
				shell_exec('grep BENCHMARK_FSTAR ulib/gmake/fstar.mk || git apply %s'%args.benchmark_hook_patch)

			log_fname = os.path.join(hashdir, 'bench_%s.log'%run_timestamp)
			completed_proc = shell_exec_redirect('%s'%args.benchmark_run_script, log_fname)
			if completed_proc.returncode != 0:
				print('ERROR[%d] in fstar bench run for %s (see %s)'%(completed_proc.returncode, h, log_fname))

			## collate benchmark output
			shell_exec('mkdir -p ../bench_results; cp -r bench_results/*/* ../bench_results')

			## clean directory after use
			if not args.benchmark_no_cleanup:
				os.chdir(hashdir)
				shell_exec('rm -rf %s'%h)

	if 'upload' in run_stages:
		os.chdir(hashdir)
		resultdir = os.path.join(hashdir, 'bench_results')
		glob_pat = '%s/*.bench'%resultdir
		fnames = sorted(glob.glob(glob_pat))
		if not fnames:
			print('ERROR: could not find any results of form %s to upload'%glob_pat)
			continue

		for fname in fnames:
			print('Uploading data from %s'%fname)

			upload_data = parse_and_format_results_for_upload(fname)

			## upload this stuff into the codespeed server
			if upload_data:
				codespeed_upload.post_data_to_server(args.codespeed_url, upload_data, verbose=args.verbose)


