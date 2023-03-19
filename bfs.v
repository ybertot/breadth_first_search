Require Import List Arith Lia.
Require Import Wellfounded.
From Equations Require Import Equations.

Section explore.

Variable (state move : Type).
Variable (state_fmap : Type).
Variable find : state_fmap -> state -> option move.
Variable add : state_fmap -> state -> move -> state_fmap.
Variable (step : state -> list (state * move)).
Variable (state_eq_dec : forall s1 s2 : state, {s1 = s2}+{s1 <> s2}).

Variable map_order : state_fmap -> state_fmap -> Prop.
Hypothesis map_order_wf : well_founded map_order.
Hypothesis add_order : forall map s v,
  find map s = None -> map_order (add map s v) map.
Hypothesis map_order_trans : forall map2 map1 map3,
  map_order map1 map2 -> map_order map2 map3 -> map_order map1 map3.

Fixpoint bfs_aux (w w2 : list (state * move))
  (settled : state_fmap) : (list (state * move) * state_fmap) :=
match w with
| (s, m) :: w' =>
  match find settled s with
  | Some _ => bfs_aux w' w2 settled
  | None => bfs_aux w' (step s ++ w2) (add settled s m)
  end
| nil => (w2, settled)
end.

Fixpoint bfs (fuel : nat) (w : list (state * move)) (settled : state_fmap) 
  (round : nat) :
  (state_fmap * nat) + (list (state * move) * state_fmap) :=
  match fuel with
  | 0 => inr (w, settled)
  | S p =>
    match bfs_aux w nil settled with
    | (nil, s) => inl (s, round)
    | (w, s) => bfs p w s (round + 1)
    end
  end.

  (* We then explain how we build a path using the database. *)
Fixpoint make_path (db : state_fmap)
(targetb : state -> bool) (play : state -> move -> option state)
(x : state) (fuel : nat) :=
match fuel with
| 0 => None
| S p =>
if targetb x then
  Some nil
else
  match find db x with
  | None => None
  | Some m =>
    match play x m with
    | Some y =>
      match make_path db targetb play y p with
      | None => None
      | Some l => Some (m :: l)
      end
   | None => None
   end
  end
end.

Lemma bfs_aux_order_trans w w2 w3 map1 map2 map3 :
  map_order map2 map1 -> bfs_aux w w2 map2 = (w3, map3) ->
  map_order map3 map1.
Proof.
revert w2 map2; induction w as [ | [a m] w Ih]; intros w2 map2.
  now simpl; intros m1m2 [= ww mm]; rewrite <- mm.
simpl.
destruct (find map2 a) as [b | ] eqn:fma.
  now apply Ih.
intros m2m1; apply Ih.
assert (m2add : map_order (add map2 a m) map2).
  now apply add_order.
apply (map_order_trans _ _ _ m2add m2m1).
Qed.

Lemma bfs_aux_order w m2 w2 map2 map3 :
  bfs_aux w nil map2 = (m2 :: w2, map3) -> map_order map3 map2.
Proof.
revert w m2 w2 map2 map3.
assert (main : forall w w2 m3 w3 map1 map2 map3,
          (w2 = nil -> map2 = map1 \/ map_order map2 map1) ->
          (w2 <> nil -> map_order map2 map1) ->
          bfs_aux w w2 map2 = (m3 :: w3, map3) -> map_order map3 map1).
  induction w as [ | [a m] w Ih]; intros w2 m3 w3 map1 map2 map3 hnil hc.
    simpl; intros [= w2q map2q].
    now rewrite <- map2q; apply hc; rewrite w2q.
  simpl; destruct (find map2 a) as [m' | ] eqn:fma.
    now apply Ih; auto.
  apply Ih; auto.
    intros catnil; apply app_eq_nil in catnil; destruct catnil as [_ it].
    apply hnil in it; destruct it as [m2eqm1 | m2m1].
      now right; rewrite m2eqm1; apply add_order; rewrite <- m2eqm1.
    right; apply map_order_trans with (2 := m2m1).
    now apply add_order.
  intros _; destruct w2.
    destruct (hnil eq_refl) as [m2eqm1 | m2m1].
      now rewrite m2eqm1; apply add_order; rewrite <- m2eqm1.
    apply map_order_trans with (2 := m2m1).      
    now apply add_order.
  apply map_order_trans with map2.
    now apply add_order.
  apply hc; discriminate.
intros w m2 w2 map2 map3; apply main.
  now left; auto.
now intros []; auto.
Qed.

Definition inspect {A : Type} (x : A) : {y : A | x = y} :=
  exist _ x eq_refl.

Definition is_nil {A : Type} (l : list A) :=
  match l with nil => true | _ :: _ => false end.

Lemma bfs_aux_orderb :
  forall (mp s : state_fmap) (w w2 : list (state * move))
     (h_aux : bfs_aux w nil mp = (w2, s))
     (hcons : is_nil w2 = false), map_order s mp.
intros mp s w w2 h_aux hcons.
destruct w2 as [ | p w2].
  discriminate hcons.
now apply (bfs_aux_order w p w2 mp s).
Qed.

Record bfs_state := 
 { fmap : state_fmap; work_list : list (state * move); count : nat }.

Definition bfs_order : bfs_state -> bfs_state -> Prop :=
  fun s1 s2 => map_order (fmap s1) (fmap s2).

Lemma bfs_wf : well_founded bfs_order.
Proof.
now apply (wf_inverse_image _ _ map_order fmap map_order_wf).
Qed.

Definition bfs_F :=
  (fun (triplet : bfs_state) 
     (this_bfs : forall y (hwf : bfs_order y triplet),
               (state_fmap * nat) + (list (state * move) * state_fmap))
     =>
     match inspect (bfs_aux (work_list triplet) nil (fmap triplet)) with
     | exist _ (w2, s) h_aux =>
       match inspect (is_nil w2) with
       | exist _ true h_nil =>
         inl(s, count triplet)
       | exist _ false h_cons =>
         let new_state := {| fmap := s; work_list := w2; count := 
                              (count triplet + 1) |} in
         this_bfs new_state (bfs_aux_orderb (fmap triplet) (fmap new_state)
                   (work_list triplet) w2 h_aux h_cons)
       end
    end).

Definition bfs' w settled count :=
  Fix bfs_wf _ bfs_F {| fmap := settled; work_list := w; count := count |}.

Lemma bfs_eq t :
  Fix bfs_wf _ bfs_F t = 
    bfs_F t (fun y _ => (Fix bfs_wf _ bfs_F y)).
Proof.
apply (fun h => Init.Wf.Fix_eq bfs_wf _ bfs_F h t).
clear t.
intros t f g fgq.
unfold bfs_F.
case (inspect (bfs_aux (work_list t) nil (fmap t))).
intros (w2, db2) h_aux.
case (inspect (is_nil w2)); intros [ | ] h_eqnil.
  reflexivity.
apply fgq.
Qed.

Lemma bfs'_eq w settled c p : bfs' w settled c = inl p ->
  bfs (S (snd p) - c) w settled c = inl p /\ (c <= snd p).
Proof.
unfold bfs'.
set (t := {| fmap := settled; work_list := w; count := c|}).
change (bfs (S (snd p) - c) w settled c) with
 (bfs (S (snd p) - (count t)) (work_list t) (fmap t) (count t)).
change (c <= snd p) with (count t <= snd p).
elim t using (well_founded_ind bfs_wf); clear t.
intros triplet Ih; rewrite bfs_eq; unfold bfs_F at 1.
destruct (inspect (bfs_aux (work_list triplet) nil (fmap triplet))) as
 [[w2 db2] h_aux].
destruct (inspect (is_nil w2)) as [[ | ] h_cons].
  intros [= pq].
  assert (fuelq : S (snd p) - count triplet = S (snd p - count triplet)).
    rewrite <- pq; simpl.
    case (count triplet); intros; lia.
  rewrite fuelq; simpl; rewrite h_aux; destruct w2; try discriminate.
  now rewrite <- pq.
intros rec_comp; apply Ih in rec_comp.
  revert rec_comp.
  simpl (count _); simpl (fmap _); simpl (work_list _).
  intros [rec_comp count_cond].
  assert (fuelq : S (snd p) - count triplet  =
          (S (S (snd p) - (count triplet + 1)))).
    lia.
  rewrite fuelq; simpl; rewrite h_aux; destruct w2; try discriminate.
  destruct (snd p) as [ | k] eqn:sndpSk; try lia.
  replace (match count triplet + 1 with 0 => S (S k) | S l => S k - l end)
      with (S (S k) - (count triplet + 1)) by now rewrite !Nat.add_succ_r; lia.
  rewrite rec_comp; split; auto; lia.
unfold bfs_order; simpl.
now apply (bfs_aux_orderb _ _ (work_list triplet) w2); auto.
Qed.

(* The following is an attempt to define bfs' using Equations, which
should do most of the proof work for us, but it fails without an error
message. *)
(*
#[local] Instance wf_map : WellFounded map_order := map_order_wf.
Equations bfs' (settled : state_fmap) (w : list (state * move))(count : nat) 
  : (state_fmap * nat) + (list (state * move) * state_fmap)
    by wf settled map_order :=
bfs' settled w count with inspect (bfs_aux w nil settled) => {
  | exist (nil, s) h => inl(s, count);
  | exist (w2, s) h => bfs' s w2 (count + 1)}.
*)
(* The function bfs' cannot be executed in Coq, but its extraction can
  be executed in OCaml. *)

End explore.

(* Instantiating the final state map to association lists. *)
Definition bfsl (state move : Type) (n : nat)
  (state_eq_dec : forall x y : state, {x = y} + {x <> y})
  (step : state -> list (state * move)) (w settled : list (state * move)) :=
  bfs state move (list (state * move)) (fun state_set state => 
                    match find (fun p => if state_eq_dec (fst p) state then true else false) state_set with
                    | None => None
                    | Some (_, m) => Some m
                    end)
        (fun sset s m => (s, m) :: sset) step n w settled.
