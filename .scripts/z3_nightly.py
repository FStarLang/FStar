#!/usr/bin/env python

import os
import re
import io
import subprocess
import sys
import time
import smtplib
import glob
import shutil
import traceback
import zipfile
import platform

PLATFORMS = [ "x64-osx", "x86-ubuntu", "x64-ubuntu", "x64-debian", "x86-win", "x64-win" ]
REQUIRE_ALL_PLATFORMS = True

FSTAR_BIN_URL = "https://github.com/FStarLang/binaries.git"
FSTAR_BIN_LOCAL = os.path.join("nightly", "fstar-binaries")
FSTAR_BIN_SUBDIR = "z3-tested"
FSTAR_BIN_RBRANCH = "origin/master"

Z3_BIN_URL = "https://github.com/Z3Prover/bin.git"
Z3_BIN_LOCAL = os.path.join("nightly", "z3-binaries")
Z3_BIN_SUBDIR = "nightly"
Z3_BIN_RBRANCH = "origin/master"

Z3_PKG_NAME_PAT = re.compile("^z3-([0-9].[0-9].[0-9]).([a-z0-9]{12})-(x86|x64)-([a-zA-Z]*)-?([\.0-9]*).zip$")

Z3_DIR = os.path.join("nightly", "z3")

class Z3NightlyException(Exception):
    pass

def get_platform():
    z3bn = "z3"
    s = platform.system()
    a, fmt = platform.architecture()

    z3a = "x64" if a == "64bit" else "x86"

    if s == "Windows" or s.startswith("CYGWIN") or s.startswith("MSYS"):
        z3bn = "z3.exe"
        z3s = "win"
    elif s == "Linux":
        d, v, nn = platform.linux_distribution()
        if d == "Ubuntu":
            z3s = "ubuntu"
        elif d == "Debian":
            z3s = "debian"
        else:
            print("Warning: unknown linux distribution '%s', assuming Ubuntu." % d)
            z3s = "ubuntu"
    elif s == "Darwin":
        z3s = "osx"
    else:
        print("Warning: unknown system '%s', assuming Ubuntu." % s)
        return "ubuntu", "x64"

    return z3bn, z3s, z3a

def mk_args(cmd):
    css = cmd.split(" ")
    in_string = False
    cs = []
    cur = ""
    for i in css:
        if not in_string and i.startswith("\"") and i.endswith("\""):
            cs = cs + [i[1:-1]]
        elif not in_string and i.startswith("\""):
            in_string = True
            cur = i[1:]
        elif in_string and i.endswith("\""):
            in_string = False
            cur = cur + " " + i
            cs = cs + [cur[:-1]]
        elif in_string:
            cur = cur + " " + i
        elif i == "":
            pass
        else:
            cs = cs + [i]
    return cs

def call_logged(cmd, log, checked=True):
    cs = mk_args(cmd)
    # log.write(">>>>> " + " ".join(cs) + " <<<<<\n")
    ec = subprocess.call(cs, stdin=None, stdout=log, stderr=log)
    log.flush()
    if (checked and ec != 0):
        log.write("Error code: %d\n" % ec)        
        raise Z3NightlyException("Command failed.")

def call_with_output(cmd):
    cs = mk_args(cmd)
    # log.write(">>>>> " + " ".join(cs) + " <<<<<\n")
    p = subprocess.Popen(cs, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = p.communicate()
    if err is None or err == "":
        return out
    else:
        return out + " " + err

def update_git(url, branch, dir, subdir, log, quiet=False):
    q = "--quiet" if quiet else ""
    v = "--verbose" if not quiet else ""
    if not os.path.isdir(dir):                
        call_logged("git clone %s %s %s" % (q, url, dir), log)
    else:
        prev_wd = os.getcwd()
        os.chdir(dir)
        call_logged("git reset %s --hard %s" % (q, branch), log)
        call_logged("git clean %s -f" % (q), log)
        call_logged("git pull %s -s recursive -Xtheirs" % (v), log)
        call_logged("git reset %s --hard %s" % (q, branch), log)
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
            mt = call_with_output("git log -n 1 --date-order --date=raw --pretty=format:\"%cd\"").strip("\"").split(" ")[0]
            if best_offer == None or mt > best_offer[1]:
                version, git_hash, bitness, platform, pversion = m.groups()
                best_offer = (fp, mt, version, git_hash, bitness, platform, pversion)
    return best_offer

def find_specific_binary(dir, pattern, version, git_hash, log):
    for f in os.listdir(dir):
        m = pattern.match(f)
        if m is not None:
            fp = os.path.join(dir, f)
            fversion, fgit_hash, bitness, platform, pversion = m.groups()
            if (version == None or fversion == version) and fgit_hash == git_hash:
                return (fp, None, version, git_hash, bitness, platform, pversion)
    return None

def get_platform_files(from_path, version, git_hash, platforms):
    res = []
    for pf in platforms:
        fnpat = "z3-" + version + "." + git_hash + "-" + pf + "*.zip"
        pp = os.path.join(from_path, fnpat)
        matching_files = glob.glob(pp)
        if REQUIRE_ALL_PLATFORMS == True and len(matching_files) == 0:
            raise Z3NightlyException("No platform files for '%s' with version=%s and git_hash=%s." % (pf, version, git_hash))
        elif len(matching_files) > 0:
            res.append(matching_files[0])
    return res

def pick_better(old, new, from_path, pattern, platforms):
    if (old is None and new is not None) or (new[3] != old[3] and new[1] > old[1]):
        return get_platform_files(from_path, new[2], new[3], platforms)
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

def empty(d):
    if not os.path.isdir(d):
        os.mkdir(d)

    for old_file in os.listdir(d):
        ofp = os.path.join(d, old_file)
        if os.path.isdir(ofp):
            shutil.rmtree(ofp)
        else:
            os.remove(ofp)

def push(version, git_hash, log):
    wd = os.getcwd()
    try:
        old_bin_path = os.path.join(FSTAR_BIN_LOCAL, FSTAR_BIN_SUBDIR)
        new_bin_path = os.path.join(Z3_BIN_LOCAL, Z3_BIN_SUBDIR)
        update_git(FSTAR_BIN_URL, FSTAR_BIN_RBRANCH, FSTAR_BIN_LOCAL, FSTAR_BIN_SUBDIR, log)

        if git_hash == None:            
            update_git(Z3_BIN_URL, Z3_BIN_RBRANCH, Z3_BIN_LOCAL, Z3_BIN_SUBDIR, log)
            best_old = find_latest_binary(old_bin_path, Z3_PKG_NAME_PAT, log)
            best_new = find_latest_binary(new_bin_path, Z3_PKG_NAME_PAT, log)
            better = pick_better(best_old, best_new, new_bin_path, Z3_PKG_NAME_PAT, PLATFORMS)
            if better is not None:
                wipe_old_pkgs(FSTAR_BIN_LOCAL, FSTAR_BIN_SUBDIR, Z3_PKG_NAME_PAT, log)
                add_new_pkgs(better, FSTAR_BIN_LOCAL, FSTAR_BIN_SUBDIR, Z3_PKG_NAME_PAT, log)
        else:
            sb = find_specific_binary(new_bin_path, Z3_PKG_NAME_PAT, version, git_hash, log)
            if sb == None:
                raise Z3NightlyException("Z3 packages with git hash '%s' not found." % git_hash)
            else:
                pfiles = get_platform_files(new_bin_path, version, git_hash, PLATFORMS)
                wipe_old_pkgs(FSTAR_BIN_LOCAL, FSTAR_BIN_SUBDIR, Z3_PKG_NAME_PAT, log)
                add_new_pkgs(pfiles, FSTAR_BIN_LOCAL, FSTAR_BIN_SUBDIR, Z3_PKG_NAME_PAT, log)
            pass
        os.chdir(wd)
        return 0
    except Exception as ex:
        os.chdir(wd)
        traceback.print_exc(log)
        log.close()
        return 1

def get(binary_name, platform, bitness, log, Tested=True):
    wd = os.getcwd()
    try:
        if Tested:
            bsdir = os.path.join(FSTAR_BIN_LOCAL, FSTAR_BIN_SUBDIR)
            update_git(FSTAR_BIN_URL, FSTAR_BIN_RBRANCH, FSTAR_BIN_LOCAL, FSTAR_BIN_SUBDIR, log, quiet=True)
        else:
            bsdir = os.path.join(Z3_BIN_LOCAL, Z3_BIN_SUBDIR)
            update_git(Z3_BIN_URL, Z3_BIN_RBRANCH, Z3_BIN_LOCAL, Z3_BIN_SUBDIR, log, quiet=True)

        empty(Z3_DIR)
        for f in os.listdir(bsdir):
            m = Z3_PKG_NAME_PAT.match(f)
            if m is not None:
                fp = os.path.join(bsdir, f)
                version, git_hash, fbitness, fplatform, pversion = m.groups()
                if fplatform == platform and fbitness == bitness:
                    zfn = os.path.join(bsdir, f)
                    # print("Extracting Z3 from %s" % zfn)
                    with zipfile.ZipFile(zfn, "r") as zf:
                        zf.extractall(Z3_DIR)
                    break

        Z3_BINARY_PATH = ""
        for root, dirs, files in os.walk(Z3_DIR):
            for f in files:
                if f == binary_name:
                    Z3_BINARY_PATH = os.path.join(root, f)
        
        if not os.path.isfile(Z3_BINARY_PATH):
            raise Z3NightlyException("Z3 not where it should be.")
        else:
            print("%s" % Z3_BINARY_PATH)
        
        os.chdir(wd)
        return 0
    except Exception as ex:
        os.chdir(wd)
        traceback.print_exc(log)
        log.close()
        return 1

def print_help():
    print("Usage: %s (get-tested|get-latest|push)" % sys.argv[0])

if  __name__ =='__main__':    
    if len(sys.argv) < 2:
        print_help()
        sys.exit(1)
    else:
        r = 1
        log = sys.stdout
        op = sys.argv[1]
        if op == "get-tested":
            bn, pfm, bits = get_platform()
            if len(sys.argv) >= 3:
                pfm = sys.argv[2]
            if len(sys.argv) >= 4:
                bits = sys.argv[3]
            r = get(bn, pfm, bits, log, Tested=True)
        elif op == "get-latest":
            bn, pfm, bits = get_platform()
            if len(sys.argv) >= 3:
                pfm = sys.argv[2]
            if len(sys.argv) >= 4:
                bits = sys.argv[3]
            r = get(bn, pfm, bits, log, Tested=False)
        elif op == "push":
            version = None
            git_hash = None
            if len(sys.argv) >= 3:
                version = sys.argv[2]
            if len(sys.argv) >= 4:
                git_hash = sys.argv[3]
            r = push(version, git_hash, log)
        else:
            print("Error: Unknown operation '" + op + "'")
            print_help()
            r = 1
        sys.exit(r)
