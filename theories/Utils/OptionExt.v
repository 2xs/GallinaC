From Stdlib Require Import ssrfun ssrbool.
Export ssrfun.Option.

Definition isSome := @ssrbool.isSome.
Arguments isSome {A} o: rename.
