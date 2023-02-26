(* The objective is to provide a finite map interface for numbers. *)
Require Import Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx ZArith.

Include Z_as_OT.

Module Zot := FMapAVL.Make Z_as_OT.

Arguments Zot.find _ (_)%Z _.
Arguments Zot.add _ (_)%Z _ _.

Definition empty : Zot.t Z := Zot.empty _.

Definition bfs_find : Zot.t Z -> Z -> option Z :=
  fun m k => Zot.find k m.

Definition bfs_add : Zot.t Z -> Z -> Z -> Zot.t Z :=
  fun m k v => Zot.add k v m.
