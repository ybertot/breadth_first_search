Require Import List Arith ZArith Uint63.
From cube_puzzle Require Import cube_explore.

Definition remain n :=
  match cube_explore n with
  | inr (w, db) => 
    starting_positions w
  | inl _ => nil
  end.
    
Time Compute remain 17.

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
