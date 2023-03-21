Require Import List Arith ZArith Uint63.
From cube_puzzle Require Import cube_explore.

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

Definition get_db (res : intmap.t int * nat + list (int * int) * intmap.t int) :
    intmap.t int :=
  match res with
  | inl(db, _) => db
  | inr(_, db) => db
  end.

Definition get_w (res : intmap.t int * nat + list (int * int) * intmap.t int) :
    list (int * int) :=
  match res with inl _ => nil | inr(w, _) => w end.

Definition res17 := cube_explore 17.

Definition db17 := get_db res17.

Definition res18 := one_more_step res17.

Definition res19 := one_more_step res18.

Time Compute hd (0, 0) (remain res17).
(* This returns (118872, 4)  after 560 seconds on nardis, recomputing
   takes 4 seconds(res4 is memorized, the processing of remain is redone *)

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

Time Compute List.length (get_w res18).
(* The answer is 4216, the computation takes 4.2 seconds. *)
Time Compute hd (0, 0) (remain res18).
Compute List.length (remain res18).
(* There is no starting position at depth 18. *)
Time Compute List.length (new_ones (get_w res18) (get_db res18)).
(* But there are 136 position that are not at depth 17 or less. *)

Time Compute List.length (get_w res19).
Time Compute List.length (new_ones (get_w res19) (get_db res19)).
(* There are no positions that are not at depth 18 or less.
  In other words, all positions are at depth 18 or less.  but
  since there are no starting position at depth 18, the deeper
  positions are at depth 17.
*)

Compute List.length (make_solution 118872 (get_db res19)).
(* This reiterates that the length of path for 118872 is 17 *)
Import ListNotations.

Definition hard17 :=
  map of_Z (nodup Z.eq_dec (map (fun x => to_Z (fst x)) 
          (remain res17))).
Compute hard17.
(* The answer is
[118872; 301578; 301322; 886029; 565417; 565401; 45224; 365581; 20684;
        365833; 838661; 626777; 821771; 643145; 118812; 86108; 446601; 636937;
        988429; 172171; 249937; 932362; 964618; 407818; 902405; 901389; 696467;
        694285; 172195; 364683; 700429; 996106; 700584; 176289; 700553; 372873;
        176259; 700457; 372749; 569489; 987356; 692393; 15112; 364813; 692493;
        333069; 496901; 610460; 432649; 741592; 774296; 269066; 249089; 430603;
        364937; 692617; 565425; 497925; 372761; 494853; 493837; 905477; 708873;
        379141; 628761; 741529; 643097; 446489; 819379; 643153; 741465; 432153;
        86045; 430109; 626955; 268555; 924171; 428555; 237619; 432139; 628747;
        931851; 643083; 446475] *)

Compute List.length hard17.
(* So there are only 84 different positions that require 17 steps to solve.
   modulo symmetry, that gives 21.  Let's list the one
    whose positions are in the top left corner. *)

Import Bool.
Definition top_left_hard :=
  filter (fun s => (get_position s =? 0) ||
                         (get_position s =? 1) ||
                         (get_position s =? 4) ||
                         (get_position s =? 5)) hard17.
Compute List.length top_left_hard.

Compute fold_right (fun s buffer =>
  (print_position (get_position s) ++ 
  print_board (get_board s) ++ string_return ++
  buffer)%string) ""%string top_left_hard.

Compute get_position 102610.
Compute print_board (get_board 102610).
Compute ((get_board 102610 >> 1) land 1).
(* If I write 

Time Compute make_solution 0x0620E
     match result with inl(t, _) => t | _ => empty end.

Then the computation is unreasonably long. *)
Time Compute make_solution 0x0620E all_positions.
(* This one still takes 8 mn? *)

(* The next computation takes not time, because all_positions is already
  memorized. *)
Time Compute make_solution 0xF0C63 all_positions.
