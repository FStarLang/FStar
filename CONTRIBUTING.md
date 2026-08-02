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
[Failure attributes can help for that](https://github.com/FStarLang/FStar/wiki/
Failure-attributes).

Finally, contributions should adhere to the following style guide:
https://github.com/FStarLang/FStar/wiki/Style-guide

## Snapshots

The F\* compiler is written in F\*, then extracted to OCaml. We keep a copy
of the OCaml extracted compiler under version control. We **do not** expect external
pull requests to refresh the snapshot. However, reviewers should take it upon
themselves to update the snapshot before merging to master when this is needed
to obtain a "Success" without breakages from CI (in particular without
"snapshot-diff" breakages in the VSTS "Extra logs" = "Build Summary").
The reviewer may (in rare cases, when the change touches extraction)
need to bootstrap twice to reach the fixpoint.

## Bumping the stage0 snapshot

`stage0/` is a generated snapshot of the extracted OCaml compiler. It must
never be edited by hand, and the following rules apply:

- **Only `.scripts/bump-stage0-from-stage1.sh` may change `stage0/`.** Do not
  edit files under `stage0/` directly, and do not hand-craft a bump.
- **A stage0 bump commit must contain nothing else.** The script creates a
  dedicated commit touching only `stage0/` (and `mk/generic-0.mk`). Any other
  change must go in a separate commit.
- **A branch containing a bump commit must be rebased onto `master`, never
  merged.**
- **When rebasing, the bump commit must be regenerated**: drop the old bump
  commit and re-run `.scripts/bump-stage0-from-stage1.sh` on top of the
  rebased branch, so the snapshot matches the rebased sources.

## Merge vs. rebase

Historically, F\* has favored merges over rebases, so we encourage pull requests
to merge `master` in frequently. We like commit dates to be consistent, and we
may try your pull request locally; finding that the remote has rebased tends to
make it harder to work with your pull request. The one exception is a branch
that contains a stage0 bump commit: such a branch must be rebased (and the
bump commit regenerated), see "Bumping the stage0 snapshot" above.

## Line endings

All of the important file formats should be in the `.gitattributes`, but we
expect any new file to have Unix line endings.

# Reviewers of pull requests

To help the review process, and reduce turnaround time, it helps
if you can identify good reviewers for it. If you don't know who
should review it, one way to obtain a set of candidates is to look
at the Git history of the files the PR changes to see who worked on
that code in the past.