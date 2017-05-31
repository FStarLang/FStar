#!/usr/bin/env python

import os
import re
import subprocess
import sys
import time
import smtplib
import glob
import shutil
import traceback

PLATFORMS = [ "x64-osx", "x86-ubuntu", "x64-ubuntu", "x64-debian", "x86-win", "x64-win" ]

FSTAR_BIN_URL = "https://github.com/FStarLang/binaries.git"
FSTAR_BIN_LOCAL = "fstar-binaries"
FSTAR_BIN_SUBDIR = "z3-latest"
FSTAR_BIN_RBRANCH = "origin/master"

Z3_BIN_URL = "https://github.com/Z3Prover/bin.git"
Z3_BIN_LOCAL = "z3-binaries"
Z3_BIN_SUBDIR = "nightly"
Z3_BIN_RBRANCH = "origin/master"

Z3_PKG_NAME_PAT = re.compile("^z3-([0-9].[0-9].[0-9]).([a-z0-9]{12})-(x86|x64)-(.*).zip$")


class UpdateZ3Exception(Exception):
    pass

def mk_args(cmd):
    css = cmd.split(' ')
    in_string = False
    cs = []
    cur = ""
    for i in css:
        if not in_string and i.startswith('"') and i.endswith('"'):
            cs = cs + [i[1:-1]]
        elif not in_string and i.startswith('"'):
            in_string = True
            cur = i[1:]
        elif in_string and i.endswith('"'):
            in_string = False
            cur = cur + ' ' + i
            cs = cs + [cur[:-1]]
        elif in_string:
            cur = cur + ' ' + i
        else:
            cs = cs + [i]
    return cs

def call_logged(cmd, log, checked=True):
    cs = mk_args(cmd)
    # log.write("> " + " ".join(cs) + "\n")
    ec = subprocess.call(cs, stdin=None, stdout=log, stderr=log)
    log.flush()
    if (checked and ec != 0):
        log.write("Error code: %d\n" % ec)        
        raise UpdateZ3Exception("Command failed.")

def update_git(url, branch, dir, subdir, log):
    if not os.path.isdir(dir):
        call_logged("git clone %s %s" % (url, dir), log)
    else:
        prev_wd = os.getcwd()
        os.chdir(dir)
        call_logged("git reset --hard %s" % branch, log)
        call_logged("git clean -f", log)
        call_logged("git pull -v -s recursive -Xtheirs", log)
        os.chdir(prev_wd)
    sp = os.path.join(dir, subdir)
    if not os.path.isdir(sp):
        os.mkdir(sp)

def find_latest_binary(dir, pattern, log):
    best_offer = None
    for f in os.listdir(dir):
        m = pattern.match(f)
        if m is not None:
            fp = os.path.join(dir, f)
            mt = os.path.getmtime(fp)
            if best_offer == None or mt > best_offer[1]:
                version, githash, bitness, platform = m.groups()
                best_offer = (fp, mt, version, githash, bitness, platform)
    return best_offer

def pick_better(old, new, from_path, pattern, platforms):
    if (old is None and new is not None) or (new[3] != old[3] and new[1] > old[1]):
        files = []
        for pf in platforms:
            fnpat = "z3-" + new[2] + "." + new[3] + "-" + pf + "*.zip"
            pp = os.path.join(from_path, fnpat)
            matching_files = glob.glob(pp)
            if len(matching_files) == 0:
                return None
            files.append(matching_files[0])
        return files
    return None
        
def wipe_old_pkgs(to_repo, to_subdir, pattern, log):
    prev_dir = os.getcwd()
    os.chdir(to_repo)
    for f in os.listdir(to_subdir):
        if pattern.match(f) is not None:
            call_logged('git filter-branch -f --prune-empty --tree-filter "rm -f %s/%s" HEAD' % (to_subdir, f), log)
    os.chdir(prev_dir)

def add_new_pkgs(files, to_repo, to_subdir, pattern, log):
    prev_dir = os.getcwd()
    os.chdir(to_repo)
    for f in files:
        f_to_path = os.path.join(to_subdir, os.path.basename(f))
        shutil.copy2(os.path.join(prev_dir, f), f_to_path)
        call_logged('git add -v %s' % f_to_path, log)
    call_logged('git commit -v -m "Automatic update of Z3 nightly packages."', log)
    call_logged('git gc --aggressive --auto --prune=all', log)
    call_logged('git push -v --force', log)
    os.chdir(prev_dir)

def update_z3(log):
    wd = os.getcwd()
    try:
        update_git(FSTAR_BIN_URL, FSTAR_BIN_RBRANCH, FSTAR_BIN_LOCAL, FSTAR_BIN_SUBDIR, log)
        update_git(Z3_BIN_URL, Z3_BIN_RBRANCH, Z3_BIN_LOCAL, Z3_BIN_SUBDIR, log)
        old_bin_path = os.path.join(FSTAR_BIN_LOCAL, FSTAR_BIN_SUBDIR)
        new_bin_path = os.path.join(Z3_BIN_LOCAL, Z3_BIN_SUBDIR)
        best_old = find_latest_binary(old_bin_path, Z3_PKG_NAME_PAT, log)
        best_new = find_latest_binary(new_bin_path, Z3_PKG_NAME_PAT, log)
        better = pick_better(best_old, best_new, new_bin_path, Z3_PKG_NAME_PAT, PLATFORMS)
        if better is not None:
            wipe_old_pkgs(FSTAR_BIN_LOCAL, FSTAR_BIN_SUBDIR, Z3_PKG_NAME_PAT, log)
            add_new_pkgs(better, FSTAR_BIN_LOCAL, FSTAR_BIN_SUBDIR, Z3_PKG_NAME_PAT, log)
        return 0
    except Exception as ex:
        os.chdir(wd)
        traceback.print_exc(log)
        log.close()
        return 1

if  __name__ =='__main__':
    sys.exit(update_z3(sys.stdout))
