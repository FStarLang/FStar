# Contributor's license agreement

Contributors to F* are required to sign the contributor's license
agreement provided by https://cla.opensource.microsoft.com/

Contributions are received under the Apache 2.0 license.

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
