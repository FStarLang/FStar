In this folder, the following Docker images are in use or can be used:

* `opam.Dockerfile`: tests the F* opam package definition,
  `fstar.opam`.

* `package.Dockerfile`: builds a Linux binary package, and tests it
  with and without OCaml.

* `release.Dockerfile`: builds, tests and creates a new Linux binary
  release. This image is used by the `release.yml` GitHub Actions
  workflow.

* `standalone.Dockerfile`: builds and tests F*. This is the main CI
  image, used by the `linux-x64.yml` GitHub Actions workflow. It uses
  the CI scripts and the configuration files from the `build`
  subdirectory (inherited from the previous CI system, but still in
  use.)

The Docker images from the `build/*` subdirectories are no longer
used.
