Require Import List Arith ZArith Uint63.
From cube_puzzle Require Import cube_explore.

Definition res17 := cube_explore 17.

Definition remain (result :  intmap.t int * nat + list (int * int) * intmap.t int) :
          list (int * int)  :=
  match result with
  | inr (w, db) => 
    starting_positions (new_ones w db)
  | inl _ => nil
  end.

Definition one_more_step (res : intmap.t int * nat + list (int * int) * intmap.t int) :
    intmap.t int * nat + list (int * int) * intmap.t int :=
  match res with
  | inr(w, db) =>
    inr(bfs.bfs_aux _ _ _ bfs_find bfs_add reverse_steps w nil db)
  | inl _ => inr(nil, empty)
  end.

Definition db17 :=
  match res17 with inr(_, db) => db | inl _ => empty end.

Time Compute hd (0, 0) (remain res17).
(* This returns (118872, 4) *)

Import String.
Compute print_state 118872.

Time Compute state_left 118872.
(* This returns 53336 *)

Time Compute List.length (make_solution 53336 db17).
(* This returns 16 *)
(* So 118872 is at depth 17, as it is not in db17, but it moves in one
  step to 53336 which is in db17 and at depth 16. *)

(* TODO: complain about the huge time for this definition :
Definition res18 :=
  match res17 with
  | inr(w, db) =>
    inr(bfs.bfs_aux _ _ _ bfs_find bfs_add reverse_steps w nil db)
  | inl _ => inr(nil, empty)
  end.
*)

Definition res18 := one_more_step res17.

Definition get_db (res : intmap.t int * nat + list (int * int) * intmap.t int) :
    intmap.t int :=
  match res with
  | inl(db, _) => db
  | inr(_, db) => db
  end.

Definition get_w (res : intmap.t int * nat + list (int * int) * intmap.t int) :
    list (int * int) :=
  match res with inl _ => nil | inr(w, _) => w end.

Time Compute List.length (get_w res18).
(* The answer is 4216 *)
Time Compute hd (0, 0) (remain res18).
(* There is no starting position at depth 18. *)
Time Compute List.length (new_ones (get_w res18) (get_db res18)).
(* But there are 136 position that are not at depth 17 or less. *)
Definition res19 := one_more_step res18.

Time Compute List.length (new_ones (get_w res19) (get_db res19)).
(* There are no positions that are not at depth 18 or less.
  In other words, all positions are at depth 18 or less.  but
  *)

Import String.
Compute print_state 644106.

Compute List.length (make_solution 644106 db17).

Time Compute bfs_find intmap.empty 644106.
Compute List.length (remain res17).

Definition res18 :=
  bfs_aux _ _ _ bfs_find bfs_add

Definition remain18 := remain 18.
Compute List.length remain18.

Compute List.length (filter (fun p => ((get_board (fst p) >> get_position (fst p)) land 1) =? 0)
           remain17).

Compute List.length (filter (fun p => ((get_board (fst p) >> get_position (fst p)) land 1) =? 0)
           remain18).

Compute hd (0, 0) remain18.

Compute print_state 694283.

Definition require n := 
  match cube_explore n with
  | inr (w, _) => w
  | inl _ => nil
  end.

Definition require19 := require 19.

Compute hd (0,0) require19.
(* The answer is 36589577 *)
(* This answer shows that there are positions at level 19 *)

Compute new_ones require19 .

Definition db_of_result
  (r : intmap.t int * nat + list (int * int) * intmap.t int) :=
  match r with inl(db, _) => db | inr(_, db) => db end.

Compute List.length (make_solution 36589577 all_positions).
(* This answer shows that a position at level 19 has length 16. *)

Definition require20 := require 20.

Compute hd (0,0) require20.

(* This result shows that there are no positions at level 20. *)

Compute List.length (filter (fun p => ((get_board (fst p) >> get_position (fst p)) land 1) =? 0)
           remain18).
Compute (map fst (firstn 20 (filter (fun p => ((get_board (fst p) >> get_position (fst p)) land 1) =? 0)
           remain18))).
Definition db_of_result
  (r : intmap.t int * nat + list (int * int) * intmap.t int) :=
match r with inl(db, _) => db | inr(_, db) => db end.

Definition all_solutions_raw :=
  intmap.this (db_of_result (cube_explore 20)).

Time Definition all_solutions_computed := Eval vm_compute in all_solutions_raw.


Time Compute make_solution_array 0x0620e big_array.


(* If I write 

Time Compute make_solution 0x0620E
     match result with inl(t, _) => t | _ => empty end.

Then the computation is unreasonably long. *)
Time Compute make_solution 0x0620E all_positions.
(* This one still takes 8 mn? *)

(* The next computation takes not time, because all_positions is already
  memorized. *)
Time Compute make_solution 0xF0C63 all_positions.
