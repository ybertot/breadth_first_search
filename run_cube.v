Require Import List Arith ZArith Uint63.
Require Import cube_explore.

(* If I write 

Time Compute make_solution 0x0620E
     match result with inl(t, _) => t | _ => empty end.

Then the computation is unreasonably long. *)
Time Compute make_solution 0x0620E all_positions.
(* This one still takes 8 mn? *)

(* The next computation takes not time, because all_positions is already
  memorized. *)
Time Compute make_solution 0xF0C63 all_positions.
