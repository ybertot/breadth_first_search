From mathcomp Require Import all_ssreflect.
Require Import bfs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section proof_context.

Variables state : eqType.
Variable move : finType.
Variables state_fmap : Type.

Variable empty : state_fmap.

Variable find : state_fmap -> state -> option move.
Variable add : state_fmap -> state -> move -> state_fmap.
Variable step : state -> list (state * move).

Variable transition : state -> move -> state.

Hypothesis find_empty : forall s, find empty s = None.
Hypothesis add_find : forall d s m, find (add d s m) s = Some m.
Hypothesis add_find2 :
  forall d s1 s2 m, s1 != s2 -> find (add d s1 m) s2 = find d s2.

(* step gives all reverse steps of transition *)
Hypothesis step_transition :
  forall s1 s2 m, transition s1 m = s2 <-> s1 \in [seq fst p | p <- step s2].
(* What we want to prove are the following facts:
  - for each position it contains, the table makes it possible to compute
    a path of shortest length to the targets,
  - the number given as second result is 2 + the maximal length of such
    shortest paths.
  To prove these two facts, we will prove similar statements about bfs_aux. *)

(* We first explain what it means to have a path from x to the set of target. *)
Fixpoint is_solution (targets : list (state * move)) (x : state)
   (l : list move) :=
  match l with
  | nil => has (fun sm => (fst sm) == x) targets
  | m :: l1 =>
   is_solution targets (transition x m) l1
  end.

(* We then explain how we build a parth using the database. *)
Fixpoint make_path (db : state_fmap) (targets : list (state * move))
   (x : state) (fuel : nat) :=
match fuel with
| 0 => None
| S p =>
  if has (fun sm => (fst sm) == x) targets then
     Some nil
  else
     match find db x with
     | None => None
     | Some m =>
       match make_path db targets (transition x m) p with
       | None => None
       | Some l => Some (m :: l)
       end
     end
end.

Definition fact1 :=
  forall targets depth t r count,
  bfs _ _ _ find add step depth targets empty count = inl(t, r) ->
  forall s l, is_solution targets s l = true ->
  exists l', make_path t targets s depth = Some l' /\
    length l' <= length l.

Definition fact2 := 
  forall targets t s r l depth depth' count,
  bfs _ _ _ find add step depth targets empty count = inl(t, r) ->
  make_path t targets s depth' = Some l ->
  is_solution targets s l = true.

Definition fact3 :=
  forall targets t r depth,
  bfs _ _ _ find add step depth targets empty 0 = inl(t, r) ->
  forall s l, is_solution targets s l = true ->
    length l + 2 <= r /\
  exists s l, is_solution targets s l = true /\
               length l + 2 = r.

Lemma make_path_step db targets x fuel:
  make_path db targets x fuel =
    match fuel with
  | 0 => None
  | S p =>
      if has (fun sm : state * move => fst sm == x) targets
      then Some nil
      else
       match find db x with
       | Some m =>
           match make_path db targets (transition x m) p with
           | Some l => Some (m :: l)
           | None => None
           end
       | None => None
       end
  end.
Proof. by case: fuel. Qed.

Lemma make_path_preserve x m s db targets depth l:
  find db s = None ->
  make_path db targets x depth = Some l ->
  make_path (add db s m) targets x depth = Some l.
Proof.
move=> dbnone.
elim: depth x l => [ | depth Ih]; first by [].
move=> x l /=.
case: ifP => exq //.
case fdbx: (find db x) => [m' | ] //.
case mpq : (make_path db targets (transition x m') depth) => [ l' | ] // [eql].
have nochange : find (add db s m) x = find db x.
  by rewrite add_find2 //; apply/eqP=> sx; move: dbnone; rewrite sx fdbx.
by rewrite nochange fdbx (Ih (transition x m') l') ?eql.
Qed.

Lemma make_path_add_length db targets s depth l :
  make_path db targets s depth = Some l ->
  make_path db targets s (S depth) = Some l.
Proof.
elim: depth s l => [ | n Ih] s l //.
rewrite 2!make_path_step.
case exq : (has _ _)=> //.
case fdbq : (find db s) => [m | ] //.
case mq : (make_path _ _ _ _)=> [l' | ] //.
by move/Ih : mq => ->.
Qed.

Definition states_included (l : list (state * move)) (t : state_fmap) :=
  forall s, s \in [seq fst p | p <-  l] -> find t s <> None.

Lemma states_included_add l t s m :
  states_included l t -> states_included l (add t s m).
Proof.
elim: l => [ | [s' m'] tl Ih] //.
move=> h s2 /h inl.
case : (eqVneq s s2) => [ss2 | sns2]; first by rewrite ss2 add_find.
by rewrite add_find2.
Qed.

Lemma add_find_none db s m s' :
   find db s' <> None -> find (add db s m) s' <> None.
Proof.
case fdbs' : (find db s') => [m' |] // _.
case: (eqVneq s s') => [sq | snq].
  by move: fdbs'; rewrite -sq add_find.
by rewrite add_find2 // fdbs'.
Qed.

Lemma bfs_aux_fact1 targets w w2 w3 db db2 depth:
   states_included targets db ->
   (forall s, find db s <> None ->
      (exists l, make_path db targets s (S depth) = Some l /\
                 is_solution targets s l = true)) ->
   (forall s m, (s, m) \in w -> find db (transition s m) <> None /\
      exists l, make_path db targets (transition s m) depth = Some l /\
                is_solution targets (transition s m) l = true) ->
   bfs_aux _ _ _ find add step w w2 db = (w3, db2) ->
   (forall s, find db2 s <> None ->
      (exists l, make_path db2 targets s (S depth) = Some l /\
                 is_solution targets s l = true)).
Proof.
elim: w w2 db => [ | [s m] w Ih] w2 db sin hypdb hypw.
  move=> [w2q /[dup] db2q <-].
  move=> s findq; case: (hypdb s findq) => [l [lq lsol]].
  by exists l.
rewrite [bfs_aux _ _ _ _ _ _ _ _ _]/=.
case fdbs: (find db s) => [m' | ]; intros bfs_auxq.
  apply: (Ih w2 db) => //.
  by move=> s2 m2 inw; apply: hypw=> /=; rewrite inE inw orbT.
move=> s2 find2q.
apply: (Ih (step s ++ w2) (add db s m) _ _ _ bfs_auxq)=> //.
    by apply: states_included_add.
  move=> s'; case: (eqVneq s s') => [sq | snq].
    move=> _.
    case: (hypw s m) => [ | trin [ls [lsq lssol]]]; first by rewrite inE eqxx.
    exists (m :: ls); split.
      rewrite /=; case: ifP=> [/hasP [ts ints /eqP tsP ] | nexq].
        have /eqP abs : find db s' <> None.
          have := sin (fst ts); rewrite tsP; apply.
          by apply/mapP; exists ts.
        by case: (negP abs); rewrite -sq fdbs.
      rewrite -sq add_find.
      by rewrite (make_path_preserve m fdbs lsq).
    by rewrite /= -sq.
  rewrite add_find2 //.
  move=> /hypdb [ls' [ls'q Pls']].
  exists ls'; split; last by [].
  by apply: make_path_preserve.
move=> s' m' inw.
have /hypw : (s', m') \in ((s, m) :: w) by rewrite inE inw orbT.
move=> [trin [ls' [ls'q ls'sol]]].
split; first by apply: add_find_none.
exists ls'; split=> //.
by apply make_path_preserve.
Qed.

Definition at_depth (n : nat) (targets : list (state * move)) (s : state) :=
  (exists2 l : list move, is_solution targets s l & size l = n) /\
  forall l, is_solution targets s l -> n <= size l.

Lemma at_depth_uniq n n' s targets : at_depth n targets s ->
  at_depth n' targets s -> n = n'.
Proof.
rewrite /at_depth=> -[[ln A B] nmin] [[ln' C D] n'min].
by apply/eqP; rewrite eqn_leq -{1}D (nmin ln') // -B (n'min ln).
Qed.

Lemma at_depth_exists s targets l :
  is_solution targets s l -> exists n, at_depth n targets s.
Proof.
suff main : forall n l, size l <= n -> is_solution targets s l ->
              exists n', at_depth n' targets s.
  by apply: (main (size l)).
elim=> [ | n Ih] {}l szl sol.
  exists 0; split; first by exists l=> //; apply/eqP; rewrite leqn0 in szl.
  by move=> ? ?; rewrite leq0n.
have [/existsP [n' /existsP [t]] | there] := boolP [exists i : 'I_n.+1,
        [exists t : {tuple i of move}, is_solution targets s t]].
  by apply: Ih; rewrite size_tuple -ltnS ltn_ord.
exists n.+1; split.
  exists l => //; move: szl; rewrite leq_eqVlt=> /orP[/eqP //| szlt].
  case/negP: there.
  by apply/existsP; exists (Ordinal szlt); apply/existsP; exists (in_tuple l).
move=> l' sol'; rewrite ltnNge; apply/negP; rewrite -ltnS=> szl'.
case/negP: there.
by apply/existsP; exists (Ordinal szl'); apply/existsP; exists (in_tuple l').
Qed.

Lemma bfs_aux_fact2 n targets (w w2 w3 : seq (state * move)) db db2:
   (forall s, find db s <> None ->
       exists2 n', at_depth n' targets s & n' <= n) ->
   (forall s, s \in [seq p.1 | p <- w] -> find db s = None ->
              at_depth n targets s) ->
   (forall s, at_depth n targets s ->
     (s \in [seq p.1 | p <- w] /\ find db s = None) \/
     ({subset step s <= w2} /\ find db s <> None)) ->
   (forall s, s \in [seq p.1 | p <- w2] ->
      exists2 n', at_depth n' targets s & n' <= S n) ->
   bfs_aux _ _ _ find add step w w2 db = (w3, db2) ->
   (forall s, s \in [seq p.1 | p <- w3] ->
      (exists2 n', at_depth n' targets s & n' <= S n)).
Proof.
elim: w w2 db => [ | [s m] w Ih] w2 db; move=> /= depth_db depthw invw invw2.
  by move=> [ <- _].
case fdbsq : (find db s) => [m0 | ].
  move=> bfs_auxq.
  apply: (Ih w2 db)=> //.
    by move=> s' s'in; apply: depthw; rewrite inE s'in orbT.
  move=> s' deps'; case: (invw s' deps'); last by tauto.
  move=> [s'in s'none]; left; split=> //.
  move: s'in; rewrite inE=> /orP[/eqP s's| ] //.
  by move: s'none; rewrite s's fdbsq.
apply: (Ih (step s ++ w2) (add db s m)) => //.
- move=> s'; case: (eqVneq s s') => [<- _ | s'ns].
    by exists n=> //; apply: depthw; rewrite // inE eqxx.
  by rewrite add_find2 //; apply: depth_db.
- move=> s' s'in; case: (eqVneq s s') => [<- | sns'].
    by rewrite add_find.
  rewrite add_find2 //; apply: depthw.
  by rewrite inE s'in orbT.
- move=> s' deps'; case: (eqVneq s s') => [<- | sns'].
    right; split; first by move=> p pin; rewrite mem_cat pin.
    by rewrite add_find.
  case: (invw _ deps') => [ | [inw2 ndb]].
    by rewrite inE eq_sym (negbTE sns') /= add_find2 //; left.
  rewrite add_find2 //; right; split; last by [].
  by move=> p pin; rewrite mem_cat; apply/orP; right; apply: inw2.
move=> s' /mapP [p + s'q]; rewrite mem_cat=> /orP[ | pinw2]; last first.
  by apply: invw2; apply/mapP; exists p.
move=> /(map_f (@fst _ _))/step_transition=> /(_ p.2); rewrite -s'q => tr'.
have := depthw s; rewrite inE eqxx /= => /(_ isT fdbsq)[[l sol sz] _].
have sol' : is_solution targets s' (p.2 :: l) by rewrite /= tr'.
have [n' /[dup] n'dep [_ n'min]]:= at_depth_exists sol'.
exists n'=> //; apply: (leq_trans (n'min _ sol'))=> /=.
by rewrite sz.
Qed.
