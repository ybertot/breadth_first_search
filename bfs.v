Require Import List.

Section explore.

Variable (state move : Type).
Variable (state_fmap : Type).
Variable find : state_fmap -> state -> option move.
Variable add : state_fmap -> state -> move -> state_fmap.
Variable (step : state -> list (state * move)).
Variable (state_eq_dec : forall s1 s2 : state, {s1 = s2}+{s1 <> s2}).

Definition bfs_aux 
  (bfs' : list (state * move) -> state_fmap -> option state_fmap)  :
  list (state * move) ->
  list (state * move) ->
  state_fmap ->
  option state_fmap :=
fix bfs_aux (w w2 : list (state * move)) (settled : state_fmap):
  option state_fmap :=
match w with
| (s, m) :: w' =>
  match find settled s with
  | Some _ => bfs_aux w' w2 settled
  | None => bfs_aux w' (step s ++ w2) (add settled s m)
  end
| nil =>
  match w2 with
  | nil => Some settled
  | _ => bfs' w2 settled
  end
end.

Fixpoint bfs (fuel : nat) (w : list (state * move)) (settled : state_fmap) :
  option state_fmap :=
  match fuel with
  | 0 => None
  | S p => bfs_aux (bfs p) w nil settled
  end.

End explore.

    
