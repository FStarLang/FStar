# Contributor's license agreement

Contributors to F\* are required to sign the contributor's license
agreement provided by https://cla.opensource.microsoft.com/

The code of F* is released under the Apache 2.0 license.

# Pull requests

Please make your contribution available as a pull request. We expect
all regression tests to pass on your pull request before considering
it eligible for review.

The rationale for the PR should be explained, either in the commit messages
or in Github's PR system. Ideally, PRs should come with comments and
documentation within the source tree, if applicable. If the PR
involves a non-backwards-compatible or possibly breaking change,
it should update `CHANGES.md` to reflect it.

Please add regression tests for your PR. Ideally, both positive and negative
ones. Specially so if the change is a bugfix, or touches a critical component.
[Failure attributes can help for that](https://github.com/FStarLang/FStar/wiki/Failure-attributes).

## Snapshots

The F\* compiler is written in F\*/F#, then extracted to OCaml. We keep a copy
of the OCaml extracted compiler under version control. We do *not* expect pull
requests to refresh the snapshot; reviewers should take it upon themselves to
merge then let the nightly build refresh the snapshot automatically.

## Merge vs. rebase

Historically, F\* has favored merges over rebases, so we encourage pull requests
to merge `master` in frequently. We like commit dates to be consistent, and we
may try your pull request locally; finding that the remote has rebased tends to
make it harder to work with your pull request.

## Line endings

All of the important file formats should be in the `.gitattributes`, but we
expect any new file to have Unix line endings.

## F\* oranges

Internally, each regression build tests a new F\* version against "important"
projects, e.g. Vale, HACL\*, etc. Should a new F\* commit break one of these
projects, the breakage will be flagged via a Slack channel, but the CI system
will report a successful build on the pull request.

It is up to the reviewer to parse the logs and figure out whether this is
something that needs attention from you. You should not have to worry about
this.

## Debugging a build failure

Right now, the "Details" link points to a Visual Studio instance that requires
manual approval to read the build logs. We plan to make our CI bot post a
message on a pull request after each build, with a link to publicly-hosted logs
(they exist! ask a reviewer about them if you need them) along with a full
report on the aforementioned "orange" builds.

# Contributions should adhere to the style guide

See https://github.com/FStarLang/FStar/wiki/Style-guide

# Reviewers of pull requests

To help the review process, and reduce turnaround time, it helps
if you can identify good reviewers for it. If you don't know who
should review it, one way to obtain a set of candidates is to look
at the Git history of the files the PR changes to see who worked on
that code in the past.

Aside from the committers on the files that are being changed, various
components of the repository have primary maintainers who are
expected to review pull requests:

## Lexing

Antoine Delignat-Lavaud

## Parsing

Jonathan Protzenko

## Desugaring and name resolution

Tahina Ramananandro and Nik Swamy

## Printing

Victor Dumitrescu

## Core syntax

Aseem Rastogi, Guido Martinez, Nik Swamy

## Type checker

Aseem Rastogi, Guido Martinez, Nik Swamy

## Extraction

Nik Swamy, Jonathan Protzenko

## SMT Encoding

Aseem Rastogi, Guido Martinez, Nik Swamy

## Meta-F*

Guido Martinez

## IDE support

Clement Pit-Claudel

## Build

Jonathan Protzenko, Victor Dumitrescu

## Libraries

### Basic types, integers, lists, sequences, etc.

Jonathan Protzenko, Tahina Ramananandro, Nik Swamy

### Memory models

Aseem Rastogi, Tahina Ramananandro

### Reflection and Tactics

Guido Martinez

## Tutorial

Catalin Hritcu

## Examples

Many
