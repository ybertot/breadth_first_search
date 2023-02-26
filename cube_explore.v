Require Import List ZArith.

Require Import bfs db.

Check bfs.

Definition bfs step : list (Z * Z) -> option (Zot.t Z) :=
  fun l => bfs _ _ _ bfs_find bfs_add step 21 l empty.
