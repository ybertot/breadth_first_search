Require Import List.

Section explore.

Variable (state move : Type).
Variable (state_fmap : Type).
Variable find : state_fmap -> state -> option move.
Variable add : state_fmap -> state -> move -> state_fmap.
Variable (step : state -> list (state * move)).
Variable (state_eq_dec : forall s1 s2 : state, {s1 = s2}+{s1 <> s2}).

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
