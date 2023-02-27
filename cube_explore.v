Require Import List ZArith Uint63 String OrderedType OrderedTypeEx FMapAVL.
Require Import bfs.

Import ListNotations.

Module int_as_OT <: UsualOrderedType.

Definition t := int.

Definition lt (x y : t) := (to_Z x < to_Z y)%Z.

Definition eq := @Logic.eq t.

Definition eq_refl := @Logic.eq_refl t.

Definition eq_sym := @Logic.eq_sym t.

Definition eq_trans := @Logic.eq_trans t.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.
intros x y z; apply Z.lt_trans.
Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> x <> y.
Proof.
intros x y xlty xy.
rewrite xy in xlty.
now apply Z.lt_irrefl in xlty.
Qed.

Lemma compare_eq (x y : int) :
   (to_Z x ?= to_Z y)%Z = Eq -> eq x y.
Proof.
intros cmp; apply Z.compare_eq in cmp.
now rewrite <- (of_to_Z x), <- (of_to_Z y), cmp.
Qed.

Lemma compare_lt (x y : int) :
  (to_Z x ?= to_Z y)%Z = Lt -> lt x y.
Proof.
now rewrite Z.compare_lt_iff.
Qed.

Lemma compare_gt (x y : int) :
  (to_Z x ?= to_Z y)%Z = Gt -> lt y x.
Proof.
now rewrite Z.compare_gt_iff.
Qed.


Locate Compare.
Definition compare (x y : t) : OrderedType.Compare lt eq x y.
destruct (to_Z x ?= to_Z y)%Z eqn:cmp.  
- apply OrderedType.EQ.
  now apply compare_eq.
- apply OrderedType.LT.
  now apply compare_lt.
- apply OrderedType.GT.
  now apply compare_gt.
Defined.

Lemma eq_Z_to_eq_int (x y : t) : to_Z x = to_Z y -> x = y.
Proof.
now intros cmp; rewrite <- (of_to_Z x), <- (of_to_Z y), cmp.
Qed.

Lemma not_eq_Z_to_not_eq_int (x y : t) : to_Z x <> to_Z y -> x <> y.
Proof.
now intros cmp xeqy; case cmp; rewrite xeqy.
Qed.

Lemma eq_dec : forall x y : t, {x = y}+{x <> y}.
Proof.
intros x y; case (Z.eq_dec (to_Z x) (to_Z y)); intros cmp.
- left.   
  now apply eq_Z_to_eq_int.
- right.
  now apply not_eq_Z_to_not_eq_int.
Defined.

End int_as_OT.

Locate Make.
Module intmap := FMapAVL.Make int_as_OT.

Arguments intmap.find _ (_)%uint63 _.
Arguments intmap.add _ (_)%uint63 _ _.

Definition empty : intmap.t Z := intmap.empty _.

Definition bfs_find : intmap.t Z -> int -> option Z :=
  fun m k => intmap.find k m.

Definition bfs_add : intmap.t Z -> int -> Z -> intmap.t Z :=
  fun m k v => intmap.add k v m.

(* The following code is taken from Laurent Thery : puzzle_cube repository *)

Open Scope uint63_scope.

(* The number of bits for the board *)
Definition size_board := 4.
Definition nsize_board := 4%nat.
Definition size_board2 := size_board * size_board.

(* The number of bits for the position *)
Definition size_position := 4.
Definition size_board2_position := size_board2 + size_position.

(* Tne number of bits for the cube *)
Definition size_cube := 6.
Definition size_all := size_cube + size_board2_position.

Definition mask_all := (1 << size_all) -1.

Definition mask_board := (1 << size_board2) -1.
Definition clean_board := mask_all lxor mask_board.
Definition get_board s := (s land mask_board).
Definition set_board s i := (s land clean_board) lor i.

Fixpoint mk_string n s :=
  match n with 0 => ""%string | S n1 => append s (mk_string n1 s) end.

Fixpoint print_line s n :=
  match n with 
  | 0 => ""%string  
  | S n1 => if (is_zero (s land 1)) then
              append " "%string (print_line (s >> 1) n1) 
            else
              append "X"%string (print_line (s >> 1) n1) 
    end.

Definition string_return := "
"%string.

Fixpoint print_board_rec s n :=
  match n with 
  | 0 => ""%string  
  | S n1 => append "|"%string
             (append (append (print_line s nsize_board) "|"%string)
                     (append string_return
                        (print_board_rec (s >> size_board) n1)))
    end.

Definition print_board b := 
  append string_return (print_board_rec b nsize_board).

(* Test *)
Compute (print_board 34).
Compute (print_board (get_board (set_board mask_all 9))).

Definition mask_position := (((1 << size_position) - 1) << size_board2).
Definition clean_position := mask_all lxor mask_position.
Definition get_position s := (s land mask_position) >> size_board2.
Definition get_positionX s :=
  (get_position s) land ((1 << (size_position / 2)) - 1).
Definition get_positionY s := (get_position s) >> (size_position / 2).
Definition set_position s i := (s land clean_position) lor (i << size_board2).
Definition set_positionXY s x y := 
  set_position s ((y << (size_position / 2)) lor x).

(* Lazyness : only till 9  *)
Definition print_one_position p :=
 if p =? 0 then "0"%string else
 if p =? 1 then "1"%string else
 if p =? 2 then "2"%string else
 if p =? 3 then "3"%string else
 if p =? 4 then "4"%string else
 if p =? 5 then "5"%string else
 if p =? 6 then "6"%string else
 if p =? 7 then "7"%string else
 if p =? 8 then "8"%string else
 if p =? 9 then "9"%string else "?"%string.

Definition print_position p :=
  append (print_one_position (p land ((1 << (size_position / 2)) - 1)))
  (append ", " (print_one_position (p >> (size_position / 2)))).

(* Test *)
Compute let s := set_positionXY mask_all 2 1 in
      (print_position (get_position s)).

Definition mask_cube := (((1 << size_cube) - 1) << size_board2_position).
Definition clean_cube := mask_all lxor mask_cube.
Definition get_cube s := (s land mask_cube) >> size_board2_position.
Definition set_cube s i := (s land clean_cube) lor (i << size_board2_position).

(* Test *)
Compute get_cube (set_cube mask_all 12).


(* Cube
       ---
       |4|
     -------
     |2|1|5|
     -------
       |3|
       ---
       |6|
       ---       
*)



(* Definition d1 := 1 << 5. *)
Definition get_d1 c := (c >> 5) land 1.
(* Definition d2 := 1 << 4. *)
Definition get_d2 c := (c >> 4) land 1.
(* Definition d3 := 1 << 3. *)
Definition get_d3 c := (c >> 3) land 1.
(* Definition d4 := 1 << 2. *)
Definition get_d4 c := (c >> 2) land 1.
(* Definition d5 := 1 << 1. *)
Definition get_d5 c := (c >> 1) land 1.
(* Definition d6 := 1. *)
Definition get_d6 c := c land 1.
Definition mk_cube v1 v2 v3 v4 v5 v6 :=
  (((((((v1 << 1 lor v2) << 1) lor v3) << 1) lor v4) << 1) lor v5) << 1 lor v6.

Definition print_cube c :=
  let f x := if is_zero x then "O"%string else "X"%string in
  let res1 := append "         "%string 
                (append (f (get_d4 c)) string_return) in 
  let res2 := append "        "%string 
                (append 
                  (append (f (get_d2 c))(append (f (get_d1 c)) (f (get_d5 c))))
                   string_return) in
   let res3 := append "         "%string 
                (append (f (get_d3 c)) string_return) in 
   let res4 := append "         "%string 
                (append (f (get_d6 c)) string_return) in 
   let res5 := string_return in 
   append (append (append (append (append
      string_return res1) res2) res3) res4) res5. 

Compute print_cube (mask_cube >> size_board2_position).

(* Test *)
Compute let c := mk_cube 0 1 0 1 0 1 in
  (get_d1 c, get_d2 c, get_d3 c, get_d4 c, get_d5 c, get_d6 c). 

(* Rol Up 
       ---
       |6|
     -------
     |2|4|5|
     -------
       |1|
       ---
       |3|
       ---       

*)

Definition roll_up c :=
  mk_cube (get_d4 c) (get_d2 c) (get_d1 c) (get_d6 c) (get_d5 c) (get_d3 c).

(* Down
       ---
       |1|
     -------
     |2|3|5|
     -------
       |6|
       ---
       |4|
       ---       
*)

Definition roll_down c :=
  mk_cube (get_d3 c) (get_d2 c) (get_d6 c) (get_d1 c) (get_d5 c) (get_d4 c).

(* Test *)
Compute print_cube 13.
Compute print_cube (roll_down 13).
Compute print_cube (roll_up (roll_down 13)).
Compute print_cube (roll_up (roll_up (roll_up (roll_up 13)))).

(* Right
       ---
       |4|
     -------
     |1|5|6|
     -------
       |3|
       ---
       |2|
       ---       
*)

Definition roll_right c :=
  mk_cube (get_d5 c) (get_d1 c) (get_d3 c) (get_d4 c) (get_d6 c) (get_d2 c).

(* Left
       ---
       |4|
     -------
     |6|2|1|
     -------
       |3|
       ---
       |5|
       ---       
*)

Definition roll_left c :=
  mk_cube (get_d2 c) (get_d6 c) (get_d3 c) (get_d4 c) (get_d1 c) (get_d5 c).


(* Test *)
Compute print_cube 13.
Compute print_cube (roll_left 13).
Compute print_cube (roll_left (roll_right 13)).
Compute print_cube (roll_right (roll_right (roll_right (roll_right 13)))).

Fixpoint in_state s1 l := 
  match l with 
  | nil => false 
  | s2 :: l1 => if s2 <=? s1 then (s1 =? s2) else in_state s1 l1
  end.

Fixpoint add_state s1 l := 
  match l with 
  | nil => s1 :: nil 
  | s2 :: l1 => if s2 <=? s1 then 
                  if (s1 =? s2) then l else s1 :: l1 
                  else s2 :: add_state s1 l1
  end.

Compute (add_state 11 (add_state 10 (add_state 11 nil))).

Definition swap_state s := 
  let c := get_cube s in
  let b := get_board s in 
  let p := get_position s in 
  let d1 := get_d1 c in 
  let v := (b >> p) land 1 in 
  let s1 := set_cube s
    (mk_cube v (get_d2 c) (get_d3 c) (get_d4 c) (get_d5 c) (get_d6 c)) in 
  let b1 := if (v =? d1) then b else
              if is_zero v then b lor (1 << p) else b lxor (1 << p) in
  set_board s1 b1.

Definition s0 := set_cube (set_positionXY 0 1 2) ((1 << size_cube) - 1).

Compute print_cube (get_cube (swap_state s0)).
Compute print_board (get_board (swap_state s0)).

Definition one_step s vls := 
  let px := get_positionX s in 
  let py := get_positionY s in
  let c := get_cube s in 
  let (r1,vls1) := if is_zero px then (nil, vls) else
      let c1 := roll_left c in 
      let s1 := swap_state (set_cube (set_positionXY s (px - 1) py) c1) in
      if in_state s1 vls then (nil, vls) else
      (s1 :: nil, add_state s1 vls) in
  let (r2,vls2) := if px =? (size_board - 1) then (r1, vls1) else
      let c1 := roll_right c in 
      let s1 := swap_state (set_cube (set_positionXY s (px + 1) py) c1) in
      if in_state s1 vls1 then (r1, vls1) else
      (s1 :: r1, add_state s1 vls1) in
  let (r3,vls3) := if is_zero py then (r2, vls2) else
      let c1 := roll_up c in 
      let s1 := swap_state (set_cube (set_positionXY s px (py - 1)) c1) in
      if in_state s1 vls2 then (r2, vls2) else
      (s1 :: r2, add_state s1 vls2) in
  let (r4,vls4) := if py =? (size_board - 1) then (r3, vls3) else
      let c1 := roll_down c in 
      let s1 := swap_state (set_cube (set_positionXY s px (py + 1)) c1) in
      if in_state s1 vls3 then (r3, vls3) else
      (s1 :: r3, add_state s1 vls3) in
  (r4, vls4).

Definition compute_state_up s : option int :=
  let py := get_positionY s in
  if py =? 0 then None
  else 
    let px := get_positionX s in
    let s1 := set_positionXY s px (py - 1) in
    let c := get_cube s in
    let c1 := roll_up c in
    let s2 := set_cube s1 c1 in
     Some (swap_state s2).

Definition compute_state_down s : option int :=
  let py := get_positionY s in
  if py =? size_board - 1 then None
  else 
    let px := get_positionX s in
    let s1 := set_positionXY s px (py + 1) in
    let c := get_cube s in
    let c1 := roll_down c in
    let s2 := set_cube s1 c1 in
     Some (swap_state s2).

Definition compute_state_left s : option int :=
  let px := get_positionX s in
  if px =? 0 then None
  else 
    let py := get_positionY s in
    let s1 := set_positionXY s (px - 1) py in
    let c := get_cube s in
    let c1 := roll_up c in
    let s2 := set_cube s1 c1 in
     Some (swap_state s2).

Definition compute_state_right s : option int :=
  let px := get_positionX s in
  if px =? size_board - 1 then None
  else 
    let py := get_positionY s in
    let s1 := set_positionXY s (px + 1) py in
    let c := get_cube s in
    let c1 := roll_down c in
    let s2 := set_cube s1 c1 in
     Some (swap_state s2).

Definition compute_pre_state_up s : list (int * Z):=
match compute_state_up s with
| None => nil
| Some s1 =>
  match compute_state_down s1 with
  | None => nil
  | Some s2 =>
    match compute_state_up s2 with
    | None => nil
    | Some s3 => [(s3, 1%Z)]
    end
  end
end.

Definition compute_pre_state_right s :=
match compute_state_right s with
| None => nil
| Some s1 =>
  match compute_state_left s1 with
  | None => nil
  | Some s2 =>
    match compute_state_right s2 with
    | None => nil
    | Some s3 => [(s3, 2%Z)]
    end
  end
end.

Definition compute_pre_state_down s :=
match compute_state_down s with
| None => nil
| Some s1 =>
  match compute_state_up s1 with
  | None => nil
  | Some s2 =>
    match compute_state_down s2 with
    | None => nil
    | Some s3 => [(s3, 3%Z)]
    end
  end
end.

Definition compute_pre_state_left s :=
match compute_state_left s with
| None => nil
| Some s1 =>
  match compute_state_right s1 with
  | None => nil
  | Some s2 =>
    match compute_state_left s2 with
    | None => nil
    | Some s3 => [(s3, 4%Z)]
    end
  end
end.

Definition reverse_steps (s : int) : list (int * Z) :=
  compute_pre_state_left s ++
  compute_pre_state_down s ++
  compute_pre_state_right s ++
  compute_pre_state_up s.

Check bfs int Z (intmap.t Z) bfs_find bfs_add reverse_steps.

Definition full_cube := mk_cube 1 1 1 1 1 1.

Definition final_states :=
  List.concat
   (map (fun nx =>
         map (fun ny => 
           set_cube (set_positionXY 0 (of_Z (Z.of_nat nx))(of_Z (Z.of_nat ny)))
               full_cube)
               (seq 0 (Z.to_nat (to_Z size_board)))) 
               (seq 0 (Z.to_nat (to_Z size_board)))).

Definition print_state s := 
    append (print_cube (get_cube s)) 
    (append (print_position (get_position s)) (print_board (get_board s))).

 Definition print_opt_state s :=
   match s with None => ""%string | Some s => print_state s end.


Compute get_positionY (nth 6 final_states 0).
Compute print_position (get_position (nth 6 final_states 0)).

Definition cube_explore (n : nat) : intmap.t Z + (list (int * Z) * intmap.t Z) :=
  bfs _ _ _ bfs_find bfs_add reverse_steps n
    (map (fun i => (i, 0%Z)) final_states) empty.

Time Compute match cube_explore 17 with inr _ => false | inl _ => true end.
(* answer for 17 is true in 17s *)
Time Compute match cube_explore 16 with inr _ => false | inl _ => true end.
(* answer for 16 is true in 17s *)
Time Compute match cube_explore 15 with inr _ => false | inl _ => true end.
(* answer for 15 is false in 17s *)
Definition furthest_positions :=
  match cube_explore 14 with inl _ => nil | inr (l, _) => l end.

(* Amazingly this definition takes a very long time to return, while it is
   making the same computations as computations just before.
Definition solution_map := Eval vm_compute in
  match cube_explore 16 with inl v => v | _ => empty end. *)

Definition make_solution (x : int) : list (Z * int) :=
  let table := match cube_explore 16 with
               | inl table => table | inr _ => empty
               end in
  fix mkp (x : int)(fuel : nat) : list (Z * int) :=
    match fuel with
      0 => nil
    | S p =>
      match bfs_find table x with
      | Some move =>
        if move =? 1 then
           let x' := compute_state_up x in
             (1, x') :: mkp x p
        else if move =? 2 then
           let x' := compute_state_right x in
             (1, x') :: mkp x p
        else if move =? 3 then
           let x' := compute_state_down x in
             (1, x') :: mkp x p
        else if move =? 4 then
           let x' := compute_state_left x in
             (1, x') :: mkp x p
        else nil
      end
    end x 16.
