Require Import List ZArith Uint63 String OrderedType OrderedTypeEx FMapAVL.
Require Sorting.Mergesort Orders.
Import ListNotations.

Require Import bfs.

(* Preparatory work to use the predefined module for merge sort. *)
(* Note that Orders is not imported, because some of its defined *)
(* names clash with OrderedType.                                 *)
Module intZle <: Orders.TotalLeBool'.

Definition t := (int * Z)%type.

Definition leb := 
  fun x y : int * Z => PrimInt63.leb (fst x) (fst y).

Lemma leb_total : forall x y : int * Z, leb x y = true \/ leb y x = true.
Proof.
intros x y; unfold leb; rewrite !leb_spec; apply Z.le_ge_cases.
Qed.

End intZle.

Module msort := Mergesort.Sort intZle.

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

Arguments intmap.find _ (_)%uint63 _.
Arguments intmap.add _ (_)%uint63 _ _.

(* Preparatory work to use the bfs and bfs_aux functions        *)
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

Definition pre_state_up s : list (int * Z):=
match state_up s with
| None => nil
| Some s1 =>
  match state_down s1 with
  | None => nil
  | Some s2 =>
    match state_up s2 with
    | None => nil
    | Some s3 => [(s3, 3%Z)]
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
    | Some s3 => [(s3, 4%Z)]
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
    | Some s3 => [(s3, 1%Z)]
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
    | Some s3 => [(s3, 2%Z)]
    end
  end
end.

Definition reverse_steps (s : int) : list (int * Z) :=
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

 Definition print_opt_state s :=
   match s with None => ""%string | Some s => print_state s end.

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
  intmap.t Z * Z + list (int * Z) * intmap.t Z :=
  bfs _ _ _ bfs_find bfs_add reverse_steps n
    (map (fun i => (i, 0%Z)) final_states) empty 0%Z.

Definition make_solution (x : int) (table : intmap.t Z) : list (Z * int) :=
  (fix mkp (x : int)(fuel : nat) {struct fuel} : list (Z * int) :=
    match fuel with
      0 => nil
    | S p =>
      match bfs_find table x with
      | None => nil
      | Some move =>
        if (move =? 1)%Z then
           match state_up x with
           | Some x' => (1%Z, x') :: mkp x' p
           | None => nil
           end
        else if (move =? 2)%Z then
           match state_right x with
           | Some x' => (2%Z, x') :: mkp x' p
           | None => nil
           end
        else if (move =? 3)%Z then
           match state_down x with
           | Some x' => (3%Z, x') :: mkp x' p
           | None => nil
           end
        else if (move =? 4)%Z then
           match state_left x with
           | Some x' => (4%Z, x') :: mkp x' p
           | None => nil
           end
        else nil
      end
    end) x 20%nat.

Definition new_ones (l : list (int * Z)) (table : intmap.t Z) : list (int * Z)
   :=
  filter (fun p => 
            match bfs_find table (fst p) with Some _ => false | _ => true end)
       l.

Definition starting_positions (l : list (int * Z)) : list (int * Z) :=
   filter (fun p => PrimInt63.eqb (get_cube (fst p)) 0) l.

Definition explore1 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps 
    (map (fun i => (i, 0%Z)) final_states) nil empty.

Definition table1 := snd explore1.

Definition positions1 := fst explore1.

Fixpoint undup_aux  (i : int * Z) (l acc : list (int * Z)) :=
  match l with
  | nil => i::acc
  | a :: tl =>
    if fst i =? fst a then undup_aux i tl acc else  undup_aux a tl (i :: acc)
  end.

Definition undup (l : list (int * Z)) :=
  match l with nil => nil | a :: tl => undup_aux a tl nil end.

Definition new1 := undup (msort.sort (new_ones positions1 table1)).

Definition explore2 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new1 nil table1.

Definition table2 := snd explore2.

Definition positions2 := fst explore2.

Definition new2 := undup (msort.sort (new_ones positions2 table2)).

Definition explore3 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new2 nil table2.

Definition table3 := snd explore3.

Definition positions3 := fst explore3.

Definition new3 := undup (msort.sort (new_ones positions3 table3)).

Definition explore4 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new3 nil table3.

Definition table4 := snd explore4.

Definition positions4 := fst explore4.

Definition new4 := undup (msort.sort (new_ones positions4 table4)).

Definition explore5 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new4 nil table4.

Definition table5 := snd explore5.

Definition positions5 := fst explore5.

Definition new5 := undup (msort.sort (new_ones positions5 table5)).

Definition explore6 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new5 nil table5.

Definition table6 := snd explore6.

Definition positions6 := fst explore6.

Definition new6 := undup (msort.sort (new_ones positions6 table6)).

Definition explore7 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new6 nil table6.

Definition table7 := snd explore7.

Definition positions7 := fst explore7.

Definition new7 := undup (msort.sort (new_ones positions7 table7)).

Definition explore8 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new7 nil table7.

Definition table8 := snd explore8.

Definition positions8 := fst explore8.

Definition new8 := undup (msort.sort (new_ones positions8 table8)).

Definition explore9 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new8 nil table8.

Definition table9 := snd explore9.

Definition positions9 := fst explore9.

Definition new9 := undup (msort.sort (new_ones positions9 table9)).

Definition explore10 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new9 nil table9.

Definition table10 := snd explore10.

Definition positions10 := fst explore10.

Definition new10 := undup (msort.sort (new_ones positions10 table10)).

Definition explore11 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new10 nil table10.

Definition table11 := snd explore11.

Definition positions11 := fst explore11.

Definition new11 := undup (msort.sort (new_ones positions11 table11)).

Definition explore12 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new11 nil table11.

Definition table12 := snd explore12.

Definition positions12 := fst explore12.

Definition new12 := undup (msort.sort (new_ones positions12 table12)).

Definition explore13 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new12 nil table12.

Definition table13 := snd explore13.

Definition positions13 := fst explore13.

Definition new13 := undup (msort.sort (new_ones positions13 table13)).

Definition explore14 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new13 nil table13.

Definition table14 := snd explore14.

Definition positions14 := fst explore14.

Definition new14 := undup (msort.sort (new_ones positions14 table14)).

Definition explore15 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new14 nil table14.

Definition table15 := snd explore15.

Definition positions15 := fst explore15.

Definition new15 := undup (msort.sort (new_ones positions15 table15)).

Definition explore16 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new15 nil table15.

Definition table16 := snd explore16.

Definition positions16 := fst explore16.

Definition new16 := undup (msort.sort (new_ones positions16 table16)).

Definition explore17 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new16 nil table16.

Definition table17 := snd explore17.

Definition positions17 := fst explore17.

Definition new17 := undup (msort.sort (new_ones positions17 table17)).

Definition explore18 :=
  bfs_aux _ _ _ bfs_find bfs_add reverse_steps new17 nil table17.

Definition table18 := snd explore18.

Definition positions18 := fst explore18.

Definition new18 := undup (msort.sort (new_ones positions18 table18)).

Definition explore19 : list (int * Z) * intmap.t Z :=
   bfs_aux _ _ _ bfs_find bfs_add reverse_steps new18 nil table18.

Definition table19 := snd explore19.

Definition positions19 := fst explore19.

Definition new19 := undup (msort.sort (new_ones positions19 table19)).

Definition explore20 :=
   bfs_aux _ _ _ bfs_find bfs_add reverse_steps new19 nil table19.

Definition all_solutions : intmap.t Z := snd explore20.

(*
Check fun p => match bfs_find all_solutions (fst p) with Some _ => false | _ => true end.

(* BUG? this Check takes way too much time. *)
Fail Timeout 2 Check (@filter (int * Z) (fun p : int * Z => 
            match bfs_find all_solutions (fst p) with Some _ => false | _ => true end)  positions18).
*)

(* Eval native_compute in hd (0, 0%Z) starting17.
118872 *)

(* Through a computation I don't want to repeat here, I know that 
  undup (msort.sort (new_ones positions18 table18)) has 136 elements, which I deem to be
  the position with longest solutions. This list contains (35033097, 2) and
   (8425497, 2) *)

(* There are no starting positions in positions18 *)

(*
Check "computing whether 20 is enough"%string.

 Time Eval native_compute in match explore20 with inl _ => true | inr _ => false end. *)

(*
Check "computing the number of needed rounds"%string.

 Eval native_compute in match explore20 with inl(_, n) => n | inr _ => 0%Z end. *)

(* this returns 19 *)

Definition all_explored_positions_count :=
  [tlength new1; tlength new2; tlength new3; tlength new4; tlength new5;
   tlength new6; tlength new7; tlength new8; tlength new9; tlength new10;
   tlength new11; tlength new12; tlength new13; tlength new14; tlength new15;
   tlength new16; tlength new17; tlength new18; tlength new19].

Definition start1 := starting_positions new1.
Definition start2 := starting_positions new2.
Definition start3 := starting_positions new3.
Definition start4 := starting_positions new4.
Definition start5 := starting_positions new5.
Definition start6 := starting_positions new6.
Definition start7 := starting_positions new7.
Definition start8 := starting_positions new8.
Definition start9 := starting_positions new9.
Definition start10 := starting_positions new10.
Definition start11 := starting_positions new11.
Definition start12 := starting_positions new12.
Definition start13 := starting_positions new13.
Definition start14 := starting_positions new14.
Definition start15 := starting_positions new15.
Definition start16 := starting_positions new16.
Definition start17 := starting_positions new17.
Definition start18 := starting_positions new18.
Definition start19 := starting_positions new19.

Definition solution_waves :=
   [tlength start1; tlength start2; tlength start3; tlength start4;
    tlength start5; tlength start6; tlength start7; tlength start8;
    tlength start9; tlength start10; tlength start11; tlength start12;
    tlength start13; tlength start14; tlength start15;
    tlength start16; tlength start17; tlength start18; tlength start19].
