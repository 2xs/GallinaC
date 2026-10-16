FROM rocq/rocq-prover:9.1 AS base

RUN opam update && opam upgrade -y && opam pin add -y coq-compcert 3.17 && opam pin add -y rocq-elpi 3.5.0 && opam pin add -y rocq-hierarchy-builder 1.10.3 && opam install -y rocq-metarocq-utils rocq-metarocq-quotation rocq-metarocq-template && opam clean -acrs --untracked --unused-repositories