Require Import List.

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

Definition bfs' (w : list (state * move)) (settled : state_fmap)
  (round : nat) : (state_fmap * nat) + (list (state * move) * state_fmap).
revert w round.
elim settled using (Fix map_order_wf).
intros x bfs' w round.
case (inspect (bfs_aux w nil x)).
intros [[ | a' w'] s] h.
  exact (inl (x, round)).
apply (fun h => bfs' s h (a' :: w') (round + 1)).
now apply (bfs_aux_order w a' w'); auto.
Qed.
Print bfs'.
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
