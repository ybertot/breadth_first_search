Require Import List ZArith Uint63 String OrderedType OrderedTypeEx FMapAVL.
Require Import FMapFacts.
Require Import Lia  Wellfounded  PArray.
Import ListNotations.

Require Import bfs.

(* We are going to generated huge lists of integers, for which  *)
(* the default length function provided in the list module is   *)
(* inadequate.  We reimplement a length function that computes  *)
(* in a tail recursive fashion, and produced a number of        *)
(* type Z.                                                      *)
Definition tlength {A : Type}(l : list A) :=
  (fix f (l : list A) (acc : Z) : Z :=
     match l with nil => acc | _ :: tl => f tl (acc + 1)%Z end) l 0%Z.

(* Preparatory work to use the predefined module for AVL        *)
(* tables.                                                      *)

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

Module intmap := FMapAVL.Make int_as_OT.
Module facts := FMapFacts.OrdProperties intmap.

Arguments intmap.find _ (_)%uint63 _.
Arguments intmap.add _ (_)%uint63 _ _.

(* Preparatory work to use the bfs and bfs_aux functions        *)
Definition empty : intmap.t int := intmap.empty _.

Definition bfs_find : intmap.t int -> int -> option int :=
  fun m k => intmap.find k m.

Definition bfs_add : intmap.t int -> int -> int -> intmap.t int :=
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

Definition mask_cube := (((1 << size_cube) - 1) << size_board2_position).
Definition clean_cube := mask_all lxor mask_cube.
Definition get_cube s := (s land mask_cube) >> size_board2_position.
Definition set_cube s i := (s land clean_cube) lor (i << size_board2_position).


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

(* The specific functions to compute the effect of one move.    *)
Definition state_up s : option int :=
  let py := get_positionY s in
  if py =? 0 then None
  else 
    let px := get_positionX s in
    let s1 := set_positionXY s px (py - 1) in
    let c := get_cube s in
    let c1 := roll_up c in
    let s2 := set_cube s1 c1 in
     Some (swap_state s2).

Definition state_down s : option int :=
  let py := get_positionY s in
  if py =? size_board - 1 then None
  else 
    let px := get_positionX s in
    let s1 := set_positionXY s px (py + 1) in
    let c := get_cube s in
    let c1 := roll_down c in
    let s2 := set_cube s1 c1 in
     Some (swap_state s2).

Definition state_left s : option int :=
  let px := get_positionX s in
  if px =? 0 then None
  else 
    let py := get_positionY s in
    let s1 := set_positionXY s (px - 1) py in
    let c := get_cube s in
    let c1 := roll_left c in
    let s2 := set_cube s1 c1 in
     Some (swap_state s2).

Definition state_right s : option int :=
  let px := get_positionX s in
  if px =? size_board - 1 then None
  else 
    let py := get_positionY s in
    let s1 := set_positionXY s (px + 1) py in
    let c := get_cube s in
    let c1 := roll_right c in
    let s2 := set_cube s1 c1 in
     Some (swap_state s2).

(* The specific function to compute the reverse step of each    *)
(* move.                                                        *)

Definition pre_state_up s : list (int * int):=
match state_up s with
| None => nil
| Some s1 =>
  match state_down s1 with
  | None => nil
  | Some s2 =>
    match state_up s2 with
    | None => nil
    | Some s3 => [(s3, 3)]
    end
  end
end.

Definition pre_state_right s :=
match state_right s with
| None => nil
| Some s1 =>
  match state_left s1 with
  | None => nil
  | Some s2 =>
    match state_right s2 with
    | None => nil
    | Some s3 => [(s3, 4)]
    end
  end
end.

Definition pre_state_down s :=
match state_down s with
| None => nil
| Some s1 =>
  match state_up s1 with
  | None => nil
  | Some s2 =>
    match state_down s2 with
    | None => nil
    | Some s3 => [(s3, 1)]
    end
  end
end.

Definition pre_state_left s :=
match state_left s with
| None => nil
| Some s1 =>
  match state_right s1 with
  | None => nil
  | Some s2 =>
    match state_left s2 with
    | None => nil
    | Some s3 => [(s3, 2)]
    end
  end
end.

Definition reverse_steps (s : int) : list (int * int) :=
  pre_state_left s ++ pre_state_down s ++ pre_state_right s ++ pre_state_up s.

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

(* As a complement to print_state, a procedure to output the game ID as used in
  the original game by S. Tatham. The relevant function is  print_game_ID, and
  is only relevant for starting positions. *)
Fixpoint int_to_bit_list (bit_count : nat) (n : int) :=
  match bit_count with
  | 0 => nil
  | S p => (if (n land 1) =? 1 then true else false) :: int_to_bit_list p (n >> 1)
  end.

Definition int_smaller_than_16_to_digit (n : int) :=
  if n =?  0 then "0"%string else
  if n =?  1 then "1"%string else
  if n =?  2 then "2"%string else
  if n =?  3 then "3"%string else
  if n =?  4 then "4"%string else
  if n =?  5 then "5"%string else
  if n =?  6 then "6"%string else
  if n =?  7 then "7"%string else
  if n =?  8 then "8"%string else
  if n =?  9 then "9"%string else
  if n =?  10 then "A"%string else
  if n =?  11 then "B"%string else
  if n =?  12 then "C"%string else
  if n =?  13 then "D"%string else
  if n =?  14 then "E"%string else
  "F"%string.

Definition four_bit_list_to_hexa (l : list bool) :=
  let n := fold_right (fun (b : bool) (v : int) => (if b then 1 else 0) + 2 * v)
               0 l in
    int_smaller_than_16_to_digit n.

Definition int_smaller_than_20_to_decimal (n : int) :=
  if n <? 10 then int_smaller_than_16_to_digit n else
   (int_smaller_than_16_to_digit (n / 10) ++
    int_smaller_than_16_to_digit (n mod 10))%string.

Definition bits_to_hexa (s : int) := four_bit_list_to_hexa (rev (int_to_bit_list 4 s)).

Definition print_game_ID (s : int) :=
  ("c4x4:" ++ bits_to_hexa (s land 15) ++ bits_to_hexa ((s >> 4) land 15) ++
     bits_to_hexa ((s >> 8) land 15) ++ bits_to_hexa ((s >>  12) land 15) ++
   "," ++ int_smaller_than_20_to_decimal (get_cube s))%string.

(* The big computation of full bread first seach, where the     *)
(* number of iterations is limited by fuel.                     *)
(* - the result should be understood as follows:                *)
(*  * when the result is inl(t, k), t is the final table and k  *)
(*    is the minimal number of rounds to obtain it.             *)
(*  * when the result is inr(l, t), l is the current list of    *)
(*    positions that are predecessors of position that were     *)
(*    introduced at the last round,                             *)
(*    t is the table containing all positions that have already *)
(*    been processed.                                           *)
(*    When the result has the inr form, the list may have       *)
(*    duplicates and elements already present in t.             *)
(*    when the result has the inf form, the number of rounds    *)
(*    is 2 + the round number of the round index where the last *)
(*    element was added to table.                               *)
Definition cube_explore (n : nat) :
  intmap.t int * nat + list (int * int) * intmap.t int :=
  bfs _ _ _ bfs_find bfs_add reverse_steps n
    (map (fun i => (i, 0)) final_states) empty 0.

Definition make_solution_generic {T : Type} (find : T -> int -> option int) (x : int)
   (table : T) : list (int * int) :=
  (fix mkp (x : int)(fuel : nat) {struct fuel} : list (int * int) :=
    match fuel with
      0 => nil
    | S p =>
      match find table x with
      | None => nil
      | Some move =>
        if move =? 1 then
           match state_up x with
           | Some x' => (1, x') :: mkp x' p
           | None => nil
           end
        else if move =? 2 then
           match state_right x with
           | Some x' => (2, x') :: mkp x' p
           | None => nil
           end
        else if move =? 3 then
           match state_down x with
           | Some x' => (3, x') :: mkp x' p
           | None => nil
           end
        else if move =? 4 then
           match state_left x with
           | Some x' => (4, x') :: mkp x' p
           | None => nil
           end
        else nil
      end
    end) x 20%nat.

Definition play (state : int) (move : int) : option int :=
  if move =? 1 then state_up state else
  if move =? 2 then state_right state else
  if move =? 3 then state_down state else
  if move =? 4 then state_left state else
  None.

Definition make_solution (x : int) (table : intmap.t int) : list (int * int) :=
  make_solution_generic bfs_find x table.

Definition make_solution' (x : int) (table : intmap.t int) : list int :=
  match 
    make_path _ _ _ bfs_find table (fun s => PrimInt63.eqb (get_cube s) 63) 
    play x 20 with
    Some l => l
  | None => nil
  end.
 
Definition new_ones (l : list (int * int)) (table : intmap.t int) :
   list (int * int)
   :=
  filter (fun p => 
            match bfs_find table (fst p) with Some _ => false | _ => true end)
       l.

Definition starting_positions (l : list (int * int)) : list (int * int) :=
   filter (fun p => andb (PrimInt63.eqb (get_cube (fst p)) 0)
                         (PrimInt63.eqb 
                           ((get_board (fst p) >> get_position (fst p)) land 1)
                                0)) l.

Definition result3 := cube_explore 3.
Definition positions3 := match result3 with inl(t, _) => t | inr(_, t) => t end.

Definition short := intmap.Raw.enumeration.

Definition esize_more {T : Type} (e : intmap.Raw.enumeration T)
  (cont : short T -> int -> int)
  (acc : int) : int :=
  match e with
     intmap.Raw.End _ => 0
  | intmap.Raw.More k v t e' => (cont (intmap.Raw.cons t e') (1 + acc))
  end.
  
Fixpoint size_cont {T : Type} (t : intmap.Raw.tree T)
         (cont : int -> int) (acc : int) : int :=
  match t with
  | intmap.Raw.Leaf _ => cont acc
  | intmap.Raw.Node l1 x1 d1 r1 _ =>
    size_cont l1 (size_cont r1 cont) (1 + acc)
  end.

Definition size {T : Type} (table : intmap.t T) :=
   size_cont (intmap.this table) (fun x => x) 0.

Definition combine' (position move : int) :=
  (position << 3) lor (move land (1 << 4 - 1)).

Fixpoint table_to_array_cont (t : intmap.Raw.tree int)
  (cont : int -> array int -> array int) (rank : int) (a : array int) :=
  match t with
  | intmap.Raw.Leaf _ => cont rank a
  | intmap.Raw.Node l1 x1 d1 r1 _ =>
    table_to_array_cont l1
       (fun r a => table_to_array_cont r1 cont (r + 1) a.[r <- combine' x1 d1])
       rank a
  end.

Definition table_to_array (table : intmap.t int) (array_size : int) :=
   table_to_array_cont (intmap.this table)
         (fun r a => a) 0 (PArray.make array_size 0).

Definition extractkey (i : int) := i / 8.

Definition initial_gap := 2 ^ 21.

Definition array3 := table_to_array positions3.

Time Definition array3' := Eval compute in array3.

Definition result20 := cube_explore 20.

Definition all_positions := match result20 with inl(t, _) => t | _ => empty end.

Definition big_array_size :=
  Eval vm_compute in (22 * 21 * 20 * 19 * 18 * 17 * 16) / 720.

Definition big_array := table_to_array all_positions big_array_size.

(* Function to find values in the array, to replace the access that we
  had in FMapAVL.  This uses a fuel, which could be based on the log
  of the array size.  *)
Fixpoint lookup (a : array int) (x : int) (gap : int)
  (position : int) (n : nat) :=
match n with
| 0 => None
| S p =>
  let current := a.[position] in
  if x =? extractkey current then
     Some (current mod 8)
  else if x <? extractkey current then
     lookup a x (gap / 2) (position - (gap / 2)) p
  else
     if position + gap / 2 <? PArray.length a then
       lookup a x (gap / 2) (position + (gap / 2)) p
     else
       lookup a x (gap / 2) position p
end.

Definition lookup_fuel :=
  Eval vm_compute in
  Z.to_nat (Z.log2_up (to_Z big_array_size)).

Definition array_find (table : array int) (x : int) :=
  lookup table x (1 << 20) (1 << 20) lookup_fuel.

Definition make_solution_array := make_solution_generic array_find.

Definition make_solution_array' 
   (x : int) (table : array int) : option (list int) :=
  make_path _ _ _ array_find table (fun s => PrimInt63.eqb (get_cube s) 63)
    play x 20.

Definition max_card := Z.to_nat wB.

Definition map_order (t1 t2 : intmap.t int) :=
  (max_card - intmap.cardinal t1 < max_card - intmap.cardinal t2)%nat.

Definition map_order_wf : well_founded map_order :=
   wf_inverse_image (intmap.t int) nat lt
     (fun t => (max_card - intmap.cardinal t)%nat) lt_wf.

Lemma size_list_max bound : (0 < bound)%Z ->
  forall l, Sorted Z.lt l -> (forall x, In x l -> (0 <= x < bound)%Z) ->
   Datatypes.length l <= Z.to_nat bound.
Proof.
intros boundgt0 l sortl allbounds.
enough (main : Datatypes.length l <= Z.to_nat (bound - hd bound l)).
  assert (subbounds : (0 <= hd bound l <= bound)%Z).
   destruct l as [ | a l'].
     simpl; lia.
   assert (ain : In a (a :: l')) by (simpl; tauto).
   assert (tmp := allbounds a ain); simpl; lia.
   apply Nat.le_trans with (1 := main).
   rewrite <- Z2Nat.inj_le; lia.
revert sortl allbounds.
induction l as [ | a l Ih].
  intros _ _; simpl.
  now rewrite Z.sub_diag; simpl.
simpl.
destruct l as [ | b l'].
  simpl; intros _ inbounds.
  assert (altbound : (1 <= bound - a)%Z).
    destruct (inbounds a); auto; lia.
  replace 1%nat with (Z.to_nat 1) by easy.
  rewrite <- Z2Nat.inj_le; try lia.
intros sortabl' inbouds.
assert (inbounds' : forall x, In x (b :: l') -> (0 <= x < bound)%Z).
  now intros x xin; apply inbouds; right.
assert (altb : (a < b)%Z).
  inversion sortabl' as [ | dum1 dum2 sbl' cmp].
  now inversion cmp.
assert (bin : (0 <= b < bound)%Z) by (apply inbouds; simpl; tauto).
assert (tonatab : (bound - a = bound - b + (b - a))%Z) by ring.
rewrite tonatab.
rewrite Z2Nat.inj_add; try lia.
transitivity  (S ( Z.to_nat (bound - b))).
  rewrite <- Nat.succ_le_mono.
  apply Ih; auto.
  now inversion sortabl'.
lia.
Qed.

(* TODO : remove this lemma if useless. *)

Lemma add_list_length_le (l1 l2 : list Z) :
  Sorted Z.lt l1 -> Sorted Z.lt l2 ->
  (forall x, In x l1 -> In x l2) ->
  Datatypes.length l1 <= Datatypes.length l2.
Proof.
revert l2; induction l1 as [ | a l1 Ih]; intros [ | b l2]; simpl;
  auto with arith.
intros _ _ abs; case (abs a); tauto.
case (Z.eq_dec a b).
  intros abq; rewrite abq; intros sl1 sl2 incmp.
  rewrite <- Nat.succ_le_mono; apply Ih.
  now inversion sl1.
  now inversion sl2.
intros x inl1.
assert (xnb : x <> b).
  assert (tmp : Forall (Z.lt b) l1).
  apply Sorted_extends; auto.
  exact Z.lt_trans.
  revert tmp; rewrite Forall_forall; intros tmp.
  assert (tmp' := tmp x inl1); lia.
  assert (inl2 : (b = x \/ In x l1)) by now right.
  apply incmp in inl2; destruct inl2 as [xb | it]; auto.
  now case xnb; rewrite xb.
intros anb sl1 sl2 sub12; assert (blta : (b < a)%Z).
  assert (cases : (a < b \/ b < a)%Z) by lia.
  destruct cases; auto.
  assert (tmp: Forall (Z.lt a) (b :: l2)).
    assert (sabl2 : Sorted Z.lt (a :: b :: l2)).
      constructor; auto.
    apply Sorted_extends; auto.
    exact Z.lt_trans.
  revert tmp; rewrite Forall_forall; intros tmp.
  enough (a < a)%Z by lia.
  apply tmp.
  now simpl; apply sub12; left.
rewrite <- Nat.succ_le_mono.
apply Ih.
    now inversion sl1.
  now inversion sl2.
intros x inl1.
assert (xinl2 :  a = x \/ In x l1) by tauto.
apply sub12 in xinl2; destruct xinl2 as [bx | ?]; auto.
apply Sorted_extends in sl1;[ | exact Z.lt_trans].
rewrite Forall_forall in sl1; apply sl1 in inl1.
lia.
Qed.

Lemma add_list_length_lt (l1 l2 : list Z) y :
  Sorted Z.lt l1 -> Sorted Z.lt l2 ->
  (forall x, In x l1 -> In x l2) ->
  In y l2 -> ~ In y l1 -> Datatypes.length l1 < Datatypes.length l2.
Proof.
intros sl1; revert l2.
induction sl1 as [ | a l1 sl1 Ih hdrel]; intros [ | b l2]; simpl; auto with arith.
    tauto.
  intros _ abs; case (abs a); intuition auto.
intros sl2 subl1l2 yin2 ynin1.
assert (sl1' : Sorted Z.lt (a :: l1)) by now constructor.
destruct (Z.eq_dec a b) as [abq | nab].
  assert (yin2' : In y l2).
    destruct yin2 as [byq | ?]; auto.
    now case ynin1; left; rewrite abq, byq.
  assert (yin1' : ~In y l1).
    now intros ctr; case ynin1; right.
  rewrite <- Nat.succ_lt_mono.
  apply Ih; auto.
    now inversion sl2.
  intros x xin1.
  assert (tmp : a = x \/ In x l1) by now right.
  apply subl1l2 in tmp; destruct tmp as [bxq | ?]; auto.
  enough (a < x)%Z by lia.
  apply Sorted_extends in sl1';[ | exact Z.lt_trans].
  rewrite Forall_forall in sl1'; apply sl1' in xin1; lia.
assert (blta : (b < a)%Z).
  assert (cases : (a < b \/ b < a)%Z) by lia.
  destruct cases; auto.
  assert (tmp: Forall (Z.lt a) (b :: l2)).
    assert (sabl2 : Sorted Z.lt (a :: b :: l2)).
      constructor; auto.
    apply Sorted_extends; auto.
    exact Z.lt_trans.
  revert tmp; rewrite Forall_forall; intros tmp.
  enough (a < a)%Z by lia.
  apply tmp.
  now simpl; apply subl1l2; left.
  rewrite <- Nat.succ_lt_mono.
  destruct yin2 as [byq | yinl2].
  assert (hyple : forall x, In x (a :: l1) -> In x l2).
    intros x; simpl; intros xinl1; assert (xinl1' := xinl1).
    apply subl1l2 in xinl1; destruct xinl1; auto.
    destruct xinl1' as [ | xinl1']; try congruence.
    assert (sl12 := sl1').
    apply Sorted_extends in sl1';[ | exact Z.lt_trans].
    rewrite Forall_forall in sl1'; apply sl1' in xinl1'; lia.
  now apply add_list_length_le in hyple; auto; inversion sl2.
apply Ih;[ now inversion sl2 | |auto | tauto].
intros x xinl1.
assert (xinl2 : a = x \/ In x l1) by tauto.
apply subl1l2 in xinl2; destruct xinl2 as [bx | ?]; auto.
apply Sorted_extends in sl1';[ | exact Z.lt_trans].
rewrite Forall_forall in sl1'.
apply sl1' in xinl1.
lia.
Qed.

Lemma Sorted_map [A B : Type] (f : A -> B) (Ra : A -> A -> Prop)
  [Rb : B -> B -> Prop] l :
  Sorted Ra l ->
  (forall x y, In x l -> In y l -> Ra x y -> Rb (f x) (f y)) ->
  Sorted Rb (map f l).
Proof.
induction 1 as [ | x l ls Ih cmpx].
  intros; constructor.
intros monot; simpl; constructor.
  apply Ih.
  intros u v uin vin; apply monot; simpl; tauto.
destruct l as [ | b l]; simpl; auto.
constructor.
apply monot; simpl; try tauto.
now inversion cmpx.
Qed.

Lemma add_decrease :
  forall map s v, bfs_find map s = None -> map_order (bfs_add map s v) map.
Proof.
intros m s v snin.
unfold map_order.
enough (intmap.cardinal m < intmap.cardinal (bfs_add m s v)).
  enough (bnd : forall (m' : intmap.t int), intmap.cardinal m' <= max_card).
    assert (tmp1 := bnd m).
    assert (tmp2 := bnd (bfs_add m s v)).
    lia.
  intros m'; rewrite intmap.cardinal_1.
  (*TODO : complain about the need for this pattern command. *)
  pattern (Datatypes.length (intmap.elements m')).
  rewrite <- (map_length (fun p => to_Z (fst p)) (intmap.elements m')).
  apply size_list_max.
        easy.
      apply (Sorted_map (fun p => to_Z (fst p)) (intmap.lt_key (elt := int))).
      now apply intmap.elements_3.
    now auto.
  intros x; simpl.
  rewrite in_map_iff; intros [y [to_Zy _]]; rewrite <- to_Zy.
  now apply to_Z_bounded.

enough (eqlistA (facts.O.eqke (elt:= int)) (intmap.elements (bfs_add m s v))
          (facts.elements_lt (s, v) m ++ (s, v) :: facts.elements_ge (s, v) m)).
  apply eqlistA_length in H.
  rewrite app_length in H; simpl in H; rewrite Nat.add_succ_r in H.
  rewrite <- app_length in H; rewrite <-facts.elements_split in H.
  rewrite !intmap.cardinal_1.
  (* TODO : complain that " rewrite H " does not work here. *)
  assert (circ : forall a b : nat, a = S b -> b < a) by (intros; lia).
  apply (circ _ _ H).
  apply facts.elements_Add.
  rewrite facts.P.F.in_find_iff.
  now unfold bfs_find in snin; rewrite snin.
 unfold facts.P.Add; reflexivity.
 Qed.

Lemma  map_order_trans :
  forall map2 map1 map3, map_order map1 map2 -> map_order map2 map3 ->
   map_order map1 map3.
Proof.
now intros map2 map1 map3; unfold map_order; apply Nat.lt_trans.
Qed.

Definition cube_explore' (v : unit) : intmap.t int * nat :=
  match bfs' _ _ _ bfs_find bfs_add reverse_steps map_order map_order_wf
    add_decrease map_order_trans
    (map (fun i => (i, 0)) final_states) empty 0 with
  | inl r => r
  | inr (_, r) => (r, 0%nat)
  end.


(* Definition big_array' := Eval vm_compute in big_array. *)
