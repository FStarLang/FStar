## On Windows

* If you already use [Cygwin](http://cygwin.com/), make sure it's the the 64-bit version.
* Use the latest [Windows installer with OPAM](https://protz.github.io/ocaml-installer/). This document was most recently updated when *Installer for 64-bit OCaml 4.02.3 + OPAM* was presented as the latest version.

```
opam init
opam install depext depext-cygwinports
opam depext ssl
opam depext sqlite3
opam install sqlite3
```

### Environment

OPAM requires the environment to be set up properly in order to function. Manually addressing this involves the following:
```
export CAML_LD_LIBRARY_PATH=$HOME/.opam/system/lib/stublibs:/cygdrive/c/OCaml/lib/stublibs
export MANPATH=$HOME/.opam/system/man:$MANPATH
export PATH=$HOME/.opam/system/bin:/usr/x86_64-w64-mingw32/sys-root/mingw/bin/:$PATH
```
OPAM may attempt to address this itself by appending the following to your `$HOME/.bash_profile`:
```
# OPAM configuration
. C:\cygwin64\home\(username)\.opam\opam-init\init.sh > /dev/null 2> /dev/null || true
```
This is incorrect and should be replaced with correct environment settings  (see above) until this issue is addressed.

### Troubleshooting

- if OPAM doesn't recognize that Cygwin's `curl` is installed, installing `wget` has been reported to work.
- make sure your OCaml executable is the right one (`which ocaml`)
- make sure `OCAMLLIB` is properly set using a Windows-style path (e.g. `C:\OCaml\lib`). This is known to cause `opam install sqlite3` to fail.
- check the output of `ocamlopt -config` (should contain
  `native_c_compiler: x86_64-w64-mingw32-gcc -O -mms-bitfields -Wall -Wno-unused`)
- please double-check that the Cygwin package called
  `x86_64-w64-mingw32-pkg-config` is installed.
- Unfortunately, 64-bit Cygwin appears to be a requirement for `install depext-cygwinports` to succeed. 
- If running `make redux-gen` in `mitls-fstar/src/tls` fails with this:

```
** Cannot resolve symbols for C:/cygwin/home/protz/.opam/system/lib/sqlite3\libsqlite3_stubs.a(sqlite3_stubs.o):
 sqlite3_enable_load_extension
```

Then, you need to do:

```
opam update
opam remove sqlite3
opam install sqlite3
```

## On Linux

* On recent Ubuntus and Debians, installing `openssl-dev` should be enough and work out of the box. (JP: OpenSSL 1.0.2d 9 Jul 2015 worked for me).
* On older Ubuntus, we've had success with some PPA that offers a recent OpenSSL. See the `.travis.yml` file in the repo.
* On Arch first run git clone https://github.com/openssl/openssl.git in `pub/ucontrib/CoreCrypto/ml` and then run `make` here as usual.

Otherwise, if you get errors about missing `EVP_AES_GCM`, then you need to obtain the OpenSSL source code, e.g. using

    git clone https://github.com/openssl/openssl.git

Then, compile and install into a local directory (e.g. `/opt`), then tweak the `Makefile` so that it has the proper `-L` and `-I` flags.

## On OSX

The outdated, system-wide `openssl` library does not work. However, the `Makefile` is setup so that recent versions of `openssl` installed via either Homebrew or MacPorts are found.

You might have trouble building `miTLS*` under OSX because of `openssl` or `sqlite3`.
This is because OSX ship with old versions of those libraries by default.

This will cause errors similar to this one when building `miTLS*`:
```
Undefined symbols for architecture x86_64:
  "_sqlite3_enable_load_extension", referenced from:
      _caml_sqlite3_enable_load_extension in libsqlite3_stubs.a(sqlite3_stubs.o)
     (maybe you meant: _caml_sqlite3_enable_load_extension)
ld: symbol(s) not found for architecture x86_64
clang: error: linker command failed with exit code 1 (use -v to see invocation)
File "caml_startup", line 1:
Error: Error during linking
ocamlopt.opt returned with exit code 2
```

You might want to install newer versions using `homebrew` to solve this problem, but be aware that it will not be linked by default. When installing `ocaml-sqlite3` using `opam`, please make sure to reference the correct library or by default it will use the system one. 

In order to do that please set the `PKG_CONFIG_PATH` variable properly before doing `opam install sqlite3`: 
```
export PKG_CONFIG_PATH="/usr/local/opt/sqlite/lib/pkgconfig:$PKG_CONFIG_PATH"
```
This should be enough to reference and build against the correct `sqlite3` library and solve the problem.
Note that you might have similar problems with `openssl`, as we use it for some cryptographic primitives.

An alternative solution (not recommended) is to still link against the outdated system-wide `sqlite3`, but disable support for loadable extensions.

```
SQLITE3_DISABLE_LOADABLE_EXTENSIONS=1 opam reinstall sqlite3
```
