# CI

GallinaC has some rudimentary CI. A `Containerfile` constructs an image able to
build the project. In addition, `.gitlab-ci.yml` specifies a job to execute that
performs a full project build.

## Containerfile

The Containerfile is very straightforward. It directly uses the
`rocq/rocq-prover:MAJOR.MINOR` image as a base, with MAJOR and MINOR being the
versions required as stated in the README. Certain images have issues with
compiling certain dependencies, for instance `rocq/rocq-prover:9.1-native` had a
stack overflow issue.

The build instruction is a single command to keep the image size as small as
possible. CompCert is very finicky, so we pin it. MetaRocq is less complicated
(each Rocq version has a tailored version of MetaRocq; the complexity is
offloaded to the MetaRocq team), so this is not required. The final `opam clean`
should remove as much as possible.

For now, only a single image is constructed, tagged `base` which contains all
dependencies. A "dev container" could be a future work.

## .gitlab-ci.yml

The Gitlab-specific CI file contains a single job: Perform a full build of the
project and also execute `reverse` to have a trace of the produced output, in
case a regression appears. As the reverse artifacts are not essential, they
expire after 1 month.
