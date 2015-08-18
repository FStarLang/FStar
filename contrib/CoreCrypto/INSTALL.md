## From OpenSSL sourcecode

* Obtain the OpenSSL sourcecode, eg. using `git clone https://github.com/openssl/openssl.git`,
  and put it into the parent directory of FStar

#### On Windows

* Make sure you installed OCaml as described in `FStar/INSTALL.md`

* In Cygwin run `./Configure --cross-compile-prefix=i686-w64-mingw32- mingw` in the `openssl` source folder.

  Note that the cross compilation flag is important to make it work.

* Run `make` and get a coffee

#### On other platforms

Install openssl and openssl-dev using your favorite package manager.