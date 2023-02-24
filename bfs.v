Require Import List.

Section explore.

Variable (state move : Type).
Variable (step : state -> list (state * move)).
Variable (state_eq_dec : forall s1 s2 : state, {s1 = s2}+{s1 <> s2}).

Definition bfs_aux 
  (bfs' : list (state * move) -> list (state * move) ->
          option (list (state * move)))  :
  list (state * move) ->
  list (state * move) ->
  list (state * move) ->
  option (list (state * move)) :=
fix bfs_aux (w w2 settled : list (state * move)) :
  option (list (state * move)) :=
match w with
| (s, m) :: w' =>
  match find (fun p => if state_eq_dec s (fst p) then true else false) 
             settled with
  | Some _ => bfs_aux w' w2 settled
  | None => bfs_aux w' (step s ++ w2) ((s, m) :: settled)
  end
| nil =>
  match w2 with
  | nil => Some(settled)
  | _ => bfs' w2 settled
  end
end.

Fixpoint bfs (fuel : nat) (w settled : list (state * move)) :
  option (list (state * move)) :=
  match fuel with
  | 0 => None
  | S p => bfs_aux (bfs p) w nil settled
  end.

End explore.

    
