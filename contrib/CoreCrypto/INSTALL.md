* Obtain the OpenSSL sourcecode, e.g. using

  `git clone https://github.com/openssl/openssl.git`,

and put it into the parent directory of FStar.

#### On Windows

* Make sure you installed OCaml as described in `FStar/INSTALL.md`.

* In Cygwin run `./config --cross-compile-prefix=i686-w64-mingw32- mingw`
in the `openssl` source folder.

  Note that the cross compilation flag is important to make it work.

* Run `make` and get a coffee.

#### On other platforms

* Run `./config && make` in the `openssl` folder.

#### Alternatively

You can try your luck installing `openssl` and `openssl-dev` using
your favorite package manager.

This might not work on Mac OS X, where there is an outdated
system-wide `openssl` library that could interfere with the build process.

On Linux x64 OpenSSL 1.0.2d 9 Jul 2015 does not work, but the current
git version (1f003251) works fine.
