* Obtain the OpenSSL sourcecode, e.g. using

  `git clone https://github.com/openssl/openssl.git`,

and put it into the parent directory of FStar.

#### On Windows

* Use the latest windows installer with OPAM.

```
opam init
opam install depext depext-cygwinports
opam depext ssl
opam depext sqlite3
opam install sqlite3
```

Troubleshooting:
- make sure your OCaml executable is the right one (`which ocaml`)
- make sure `OCAMLLIB` is properly set
- check the output of `ocamlopt -config` (should contain
  `native_c_compiler: x86_64-w64-mingw32-gcc -O -mms-bitfields -Wall -Wno-unused`)
- please double-check that the Cygwin package called
  `x86_64-w64-mingw32-pkg-config` is installed.
- it looks like only Cygwin64 is supported, unfortunately.

If running `make redux-gen` in `mitls-fstar/src/tls` fails with this:

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

#### On other platforms

* Run `./config && make` in the `openssl` folder.

#### Alternatively

You can try your luck installing `openssl` and `openssl-dev` using
your favorite package manager.

This might not work on Mac OS X, where there is an outdated
system-wide `openssl` library that could interfere with the build process.

On Linux x64 OpenSSL 1.0.2d 9 Jul 2015 does not work, but the current
git version (1f003251) works fine.
