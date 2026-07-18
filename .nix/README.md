# Installing F* with Nix

## Prerequisites: installing `Nix` with the `flakes` feature enabled
To install Nix, follow the instructions given at
[https://nixos.org/download.html](https://nixos.org/download.html).

To enable the Nix `flakes` feature, follow the instructions given at
[https://nixos.wiki/wiki/Flakes#Enable_flakes](https://nixos.wiki/wiki/Flakes#Enable_flakes).

## Quick start

You can:
 - typecheck a module `Module.fst` with F* directly: `nix run github:FStarLang/FStar Module.fst`;
 - run a Emacs with F* available: `nix run github:FStarLang/FStar#emacs`;
 - get a shell with F* in path: `nix shell github:FStarLang/FStar`;
 - install F* imperatively in your profile: `nix profile install github:FStarLang/FStar`.

Note that in the commands above, `github:FStarLang/FStar` is a *flake
URI* that points to the `FStar` repository from the `FStarLang`
organization or user hosted on GitHub. The syntax
`github:FStarLang/FStar/some-reference` allows you to point to a
specific reference: a branch name, a tag, a commit hash.

**Use F\* from a specific branch:** just replace
`github:FStarLang/FStar` with `github:FStarLang/FStar/branch-name`.

**Use F\* of a specific commit:** just replace `github:FStarLang/FStar`
with `github:FStarLang/FStar/hash` with `hash` the full commit hash.

**Use F\* of a fork:** just replace `github:FStarLang/FStar`
with `github:repo/user`.

*Note that running any of the command above will trigger (if not
cached locally) a build of F\* from sources, which takes some time.*

## Bootstraping

The `flake.nix` at the root of this repository builds the current
OCaml snapshot by default (package named `fstar`), but also exposes
the full bootsrap build via a package named `fstar-bootsrap`.

To build/run/install/... `fstar-bootsrap`, just use
`github:FStarLang/FStar#fstar-bootsrap` instead of
`github:FStarLang/FStar`.

## Hacking on F\*

Just run `nix develop` in your local clone of F\*, you will be dropped
into a shell with the correct OCaml packages required to build & hack
on F\*.
