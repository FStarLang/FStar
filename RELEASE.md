
## Creating binary packages for your platform ##

**Note**: to create the package successfully you will need tools like
ocaml, opam, z3, make, git, Madoko, LaTeX, and zip installed.

**Note**: no cross-platform compilation supported at the moment

0. Build F\* using the OCaml snapshot (step 3 in INSTALL.md)

1. Make sure you have the Z3 4.4.1 binary in your `$PATH` or
   in the `$FSTAR_HOME/bin` directory.
   Please make sure it's precisely this version!

        $ z3 --version

2. Run the following command:

        $ make package -C src/ocaml-output

3. Run the testing of binary packages (described in INSTALL.md)

## Release process ##

* Find volunteers for creating and testing packages
  on Windows, Mac, and Linux

* Make sure that F* builds, passes all the tests, and
  that creating binary packages works well

* (Maybe one day) Close all issues that were already fixed
  (helps getting nicer release notes, but only works
   well if people actually use the tracker for their work).

* Bump the version in `version.txt`

* Push all changes to the OCaml snapshot

* [Draft a new release] on GitHub using the version number
  (e.g. v0.9.2.0) as the tag, a precise commit id (not a branch!) as
  the target, the version maybe followed by some mnemonic as the
  release title, and a description of the changes. Can use GitHub for
  a list of [changes between two releases] or of
  [issues closed between two dates].

[Draft a new release]: https://github.com/FStarLang/FStar/releases/new
[changes between two releases]: https://github.com/FStarLang/FStar/compare/v0.9.1...v0.9.1.1
[issues closed between two dates]: https://github.com/FStarLang/FStar/issues?page=1&q=is%3Aissue+is%3Aclosed+closed%3A%222015-08-29+..+2015-10-09%22&utf8=%E2%9C%93

* Have the volunteers create packages for their platform and add
  them to the release

* Have the volunteers test the releases for their platform

* If something goes terribly wrong fix it, obtain a new commit id,
  edit the GitHub release with new commit id, and repeat the last 2 steps

* At the end of a release, please remember to update the links at:
  https://www.fstar-lang.org/#download and the version number on
  https://en.wikipedia.org/wiki/F*_(programming_language) and
  https://en.wikipedia.org/wiki/Proof_assistant
