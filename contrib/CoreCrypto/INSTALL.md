## On Windows

We will use the  [OCaml Installer for Windows](http://protz.github.io/ocaml-installer/). Follow the [installation guide](https://github.com/protz/ocaml-installer/wiki) that's over there (it's optimized for F*).

## On Linux

### Install OpenSSL

* On recent Ubuntus and Debians, installing `openssl-dev` should be enough and work out of the box. (JP: OpenSSL 1.0.2d 9 Jul 2015 worked for me).
* On older Ubuntus, we've had success with some PPA that offers a recent OpenSSL. See the `.travis.yml` file in the repo.
* On Arch you just need the `openssl` package (`pacman -S openssl`)

Otherwise, if you get errors about missing `EVP_AES_GCM`, then you need to obtain the OpenSSL sourcecode, e.g. using

    git clone https://github.com/openssl/openssl.git

Then, compile and install into a local directory (e.g. `/opt`), then tweak the `Makefile` so that it has the proper `-L` and `-I` flags.

### Install OCaml package dependencies with opam

```
opam install fileutils sqlite3
```

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
