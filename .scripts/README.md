In this folder, the following scripts are in use or can be used:

* `advance.sh`: refreshes hints all across F*, and commits and pushes
  new hints. On branches `master` and `_release`, this script also
  updates the version number in `version.txt` and `fstar.opam`. This
  script is run when a user triggers a task for the `linux-x64.yml`
  GitHub Actions workflow with the "Refresh hints" box checked.

* `publish_release.sh`: assuming that a package has been created in
  `src/ocaml-output` by `make package`, this script uploads that
  package to a release corresponding to an existing tag. This script
  DOES NOT create a new release tag, which must be done by building an
  image with `.docker/release.Dockerfile` on Linux. This script is
  used by `release.sh`

* `release.sh`: builds, tests and uploads a binary package to a
  release corresponding to an existing tag. This script DOES NOT
  create a new release tag, which must be done by building an image
  with `.docker/release.Dockerfile` on Linux. This script is run when
  a task for the `release.yml` GitHub Actions workflow is triggered.

* `test_package.sh`: assuming that a package has been created in
  `src/ocaml-output` by `make package`, this script tests that package
  by extracting it to a temporary directory and verifying examples and
  the tutorial. This script is run:
  
  - to test the Windows binary package created when a task for the
    `windows.yml` GitHub Actions workflow is triggered

  - when a task for the `release.yml` GitHub Actions workflow is triggered:
  
    + to test the Linux binary package created by the
    `release.Dockerfile` Docker image
    
    + to test the Windows binary package created by the workflow

(TODO: expand this list)
