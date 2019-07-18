# Open source

F* is an open source project developed in the open using an inclusive
collaboration model meant to attract contributions from a broad and
growing community, which includes various companies, universities,
research institutes, and individuals.

The code of F* is released under the permissive Apache v2.0 License 
and is developed at https://github.com/FStarLang/FStar

# Contributor License Agreement

Contributors to F\* are required to sign a standard [Contributor License Agreement]
(CLA) giving a non-exclusive license for their contribution to Microsoft,
the main contributor to F*. The use of such a CLA is [relatively common]
for open source projects where companies are involved.

[Contributor License Agreement]: https://cla.opensource.microsoft.com
[relatively common]: https://en.wikipedia.org/wiki/Contributor_License_Agreement#Users

# Pull requests

Please make your contribution available as a pull request (PR). We expect
all regression tests to pass on your PR before considering it eligible
for review ("All checks have passed" green checkbox on GitHub).

The rationale for the PR should be explained, in the commit messages
and/or the Github PR. Ideally, PRs should come with comments and
documentation within the source tree, if applicable. If the PR
involves a non-backwards-compatible or possibly breaking change,
it should update `CHANGES.md` to reflect it.

Please add regression tests for your PR. Ideally, both positive and negative
ones; especially so if the change is a bugfix, or touches a critical component.
[Failure attributes can help for that](https://github.com/FStarLang/FStar/wiki/Failure-attributes).

Finally, contributions should adhere to the following style guide:
https://github.com/FStarLang/FStar/wiki/Style-guide

## Snapshots

The F\* compiler is written in F\*/F#, then extracted to OCaml. We keep a copy
of the OCaml extracted compiler under version control. We **do not** expect external
pull requests to refresh the snapshot. However, reviewers should take it upon
themselves to update the snapshot before merging to master when this is needed
to obtain a "Success" without breakages from CI (in particular without
"snapshot-diff" breakages in the VSTS "Extra logs" = "Build Summary").
The reviewer may (in rare cases, when the change touches extraction)
need to bootstrap twice to reach the fixpoint.

## Merge vs. rebase

Historically, F\* has favored merges over rebases, so we encourage pull requests
to merge `master` in frequently. We like commit dates to be consistent, and we
may try your pull request locally; finding that the remote has rebased tends to
make it harder to work with your pull request.

## Line endings

All of the important file formats should be in the `.gitattributes`, but we
expect any new file to have Unix line endings.

## CI can report "Success with breakages"

Internally, each regression build tests a new F\* version against "important"
projects, e.g. Vale, HACL\*, etc. Should a new F\* commit break one of these
projects, the breakage will be flagged as a "Success with breakages" in the CI
logs, but the CI system will still report a successful build on the GitHub PR.

It is up to the reviewer to detect such problems and if they occur parse the
CI logs and figure out whether this is something that needs attention from you.

## Debugging a build failure

Right now, the "Details" link points to a Visual Studio instance that requires
manual approval to read the build logs. We plan to make our CI bot post a
message on a pull request after each build, with a link to publicly-hosted logs
(they exist! ask a reviewer about them if you need them) along with a full
report on the aforementioned "Success with breakages" builds.

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
