From mathcomp Require Import all_ssreflect.
Require Import bfs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section proof_context.

(* Variables state : eqType.*)
Variable state move : finType.
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
Hypothesis step_def : forall s, 
  step s =i [set p | transition p.1 p.2 == s].

Lemma step_transition :
 forall s1 s2,
  (exists m, transition s1 m = s2) <-> s1 \in [seq fst p | p <- step s2].
Proof.
intros s1 s2; split.
  move=>[m s1m].
  have : (s1, m) \in [set p | transition p.1 p.2 == s2] by rewrite inE s1m.
  by rewrite -step_def=> s1mstep; apply/mapP; exists (s1, m).
move=> /mapP[] p + ->; rewrite step_def inE=> /eqP trp.
by exists p.2.
Qed.

(* What we want to prove are the following facts:
  - for each position it contains, the table makes it possible to compute
    a path of shortest length to the targets,
  - the number given as second result is 2 + the maximal length of such
    shortest paths.
  To prove these two facts, we will prove similar statements about bfs_aux. *)

(* We first explain what it means to have a path from x to the set of target. *)
Fixpoint is_solution (targets : list state) (x : state)
   (l : list move) : bool :=
  match l with
  | nil => x \in targets
  | m :: l1 =>
   is_solution targets (transition x m) l1
  end.

(* we then explain what it means to be at depth n *)
Definition at_depth (targets : list state) (n : nat) : {set state} :=
  [set x |
  [exists t : {tuple n of move}, is_solution targets x t] &&
  [forall i : 'I_n, [forall t : {tuple i of move}, ~~is_solution targets x t]]].

(* TODO : rename into depth_bounded  or bounded_depth *)
Definition depth_ge (targets : list state) (n : nat) :=
  [set x | [exists l : n.-bseq move, is_solution targets x l]].

(* Definition depth_ge (targets : list state) (n : nat) :=
  [set x |
  [exists i : 'I_n.+1,
     [exists t : {tuple i of move}, is_solution targets x t]]]. *)

Lemma depth_geS (targets : list state) (n : nat) :
  depth_ge targets n.+1 = depth_ge targets n :|: at_depth targets n.+1.
Proof.
rewrite -setP=> x; apply/idP/idP.
  rewrite inE=> /existsP [] l sol.
  rewrite inE; case ngedx : (x \in depth_ge _ _) => //=.
  have [isn | insn] := eqVneq (size l) n.+1.
    rewrite inE; apply/andP; split.
      by apply/existsP; exists (tcast isn (in_tuple l)); rewrite val_tcast.
    apply /forallP=> j; apply/forallP=> u; apply/negP=> abs.
    case/negP: ngedx; rewrite inE; apply/existsP.
    exists (insub_bseq n u); rewrite insubdK //.
    (* TODO : understand why rewrite /= fails here. *)
    by rewrite -[X in is_true X]/(size u <= n) size_tuple -ltnS ltn_ord.
  case/negP: ngedx; rewrite inE; apply/existsP; exists (insub_bseq n l).
  rewrite insubdK //.
  rewrite -[X in is_true X]/(size l <= n).
  by have := size_bseq l; rewrite leq_eqVlt (negbTE insn) ltnS.
move=> tmp; rewrite inE; apply/existsP; move: tmp.
rewrite 3!inE=>/orP[/existsP[]l | /andP[+ _]].
  by exists (widen_bseq (ltnW (leqnn _)) l).
by move=> /existsP[] t sol; exists (bseq_of_tuple t).
Qed.

Lemma at_depth_sub_ge (targets : list state)(n : nat) :
  at_depth targets n \subset depth_ge targets n.
Proof.
apply/subsetP=> s; rewrite inE=> /andP[] /existsP[t sol] _.
by rewrite inE; apply/existsP; exists (bseq_of_tuple t).
Qed.

Lemma at_depthSNge (targets : list state) (n : nat) :
  at_depth targets n.+1 :&: depth_ge targets n = set0.
Proof.
apply/eqP; rewrite setI_eq0 disjoint_subset; apply/subsetP=> s.
rewrite inE=> /andP[] _ /forallP nosol.
rewrite 3!inE /=; apply/negP=>/existsP[] l.
have bnd : size l < n.+1 by rewrite ltnS size_bseq.
by have := nosol (Ordinal bnd)=> /forallP /= /(_ (in_tuple l)) /= /negbTE ->.
Qed.

Lemma at_depth_step_sub (targets : list state) (n : nat) (s : state) :
  s \in at_depth targets n -> 
      [set s' | s' \in [seq p.1 | p <- step s]] \subset
        (depth_ge targets n.+1).
Proof.
rewrite inE=>/andP[] /existsP[] t sol _; apply/subsetP=> s'; rewrite inE.
rewrite inE => /step_transition[]m trs'.
have smt : size (m :: t) <= n.+1 by rewrite /= size_tuple ltnSn.
apply/existsP; exists (Bseq smt)=> /=.
by rewrite trs'.
Qed.

Lemma at_depth_decrease targets n s m l :
  s \in at_depth targets n.+1 -> is_solution targets (transition s m) l ->
  size l = n ->
  transition s m \in at_depth targets n.
Proof.
rewrite inE=>/andP[] _ /forallP optim /= sol zl.
rewrite inE; apply/andP; split.
  by apply/existsP; exists (tcast zl (in_tuple l)); rewrite val_tcast.
apply/forallP=> i; apply/forallP=> t; apply/negP=> solt.
have zt' : i.+1 < n.+1 by rewrite ltnS.
have := optim (Ordinal zt')=> /forallP/(_ (cons_tuple m t)).
by rewrite /= -/s solt.
Qed.

Definition at_depth_step (targets : list state) (n : nat) :
  \bigcup_(s in at_depth targets n) 
     [set s' in [seq p.1 | p <- step s] | s' \notin depth_ge targets n] =
  at_depth targets n.+1.
Proof.
apply/setP=> s';apply/bigcupP/idP.
  move=>[] s sin; rewrite 2!inE=> /andP[]/[dup]s'in /mapP[]p pin s'p
   /existsP /= optim.
have : s' \in depth_ge targets n.+1.
  move: sin; rewrite inE=> /andP[] /existsP[] l sol W.
  have sl' : size (p.2 :: l) <= n.+1 by rewrite /= size_tuple.
    rewrite inE; apply/existsP; exists (Bseq sl')=> /=.
    rewrite s'p.
    by move: pin; rewrite step_def inE => /eqP ->.
  rewrite depth_geS 2!inE=> /orP[] // sn; case: optim.
  by apply/existsP.
move=> /[dup]s'in.
rewrite inE=>/andP[] /existsP[] l sol /forallP optim.
set s := transition s' (tnth l ord0).
have sols : is_solution targets s (behead l).
  by rewrite {}/s; case: l sol=> [ [ | m' l'] zl].
exists s; last first.
  have /step_transition : exists m, transition s' m = s by exists (tnth l ord0).
  move=> sin; rewrite inE sin; apply/negP; rewrite inE=> /existsP[] l2 sol2.
  have bl2 : size l2 < n.+1 by rewrite ltnS size_bseq.
  by have := optim (Ordinal bl2)=> /forallP /(_ (in_tuple l2)); rewrite sol2.
by apply: (at_depth_decrease s'in sols); rewrite size_behead size_tuple.
Qed.

Lemma depth_ge_trans targets n n' : n <= n' ->
  depth_ge targets n \subset depth_ge targets n'.
Proof.
elim: n' => [ | n' Ih]; first by rewrite leqn0=> /eqP ->.
rewrite leq_eqVlt=> /orP[/eqP -> // | ].
rewrite ltnS => /Ih {}Ih.
apply: (subset_trans Ih).
by rewrite depth_geS subsetUl.
Qed.

Lemma at_depth_uniq n n' s targets : s \in at_depth targets n ->
  s \in at_depth targets n' -> n = n'.
Proof.
wlog : n n' / n <= n'.
  move=> main; case: (leqP n n'); first by apply: main.
  by move=> /ltnW n'len depn depn'; apply/esym/(main _ _ n'len depn' depn).
rewrite leq_eqVlt=> /orP[/eqP -> // | ].
case: n' => [// | n'] /[dup] nltSn'; rewrite ltnS=> nlen'.
move/(subsetP (at_depth_sub_ge targets n)).
move/(subsetP (depth_ge_trans targets nlen'))=> dge dat.
have : s \in at_depth targets n'.+1 :&: depth_ge targets n'.
  by rewrite inE dge dat.
by rewrite at_depthSNge inE.
Qed.

Lemma at_depth_exists s targets l :
  is_solution targets s l -> exists n, s \in at_depth targets n.
Proof.
suff main : forall n l, size l <= n ->
    is_solution targets s l -> exists n', s \in at_depth targets n'.
  by apply: (main (size l)).
elim=> [ | n Ih] {}l szl sol.
  case : l szl sol => //= _ sin.
  exists 0; rewrite inE; apply/andP; split.
    by apply/existsP; exists [tuple].
  by apply/forallP=> - [].
have [/existsP [n' /existsP [t]] | there] := boolP [exists i : 'I_n.+1,
        [exists t : {tuple i of move}, is_solution targets s t]].
  by apply: Ih; rewrite size_tuple -ltnS ltn_ord.
have zl : size l = n.+1.
  move: szl; rewrite leq_eqVlt => /orP[/eqP // | szlt].
  case/negP: there; apply/existsP; exists (Ordinal szlt).
  by apply/existsP; exists (in_tuple l).
exists (size l); rewrite inE; apply/andP; split.
  by apply/existsP; exists (in_tuple l).
rewrite zl; apply/forallP=> i; move: there; rewrite negb_exists=> /forallP.
by move=> /(_ i); rewrite negb_exists.
Qed.

Lemma depth_ge_exists s targets n :
  s \in depth_ge targets n -> 
  exists2 n', s \in at_depth targets n' & n' <= n.
Proof.
rewrite inE=> /existsP [l lsol].
have [n' n'P1] := at_depth_exists lsol; exists n' => //.
apply: leq_trans (size_bseq l).
case : (leqP n' (size l)) => // lltn'.
move: n'P1; rewrite inE=> /andP[] _ /forallP /(_ (Ordinal lltn')).
by move=>/forallP /(_ (in_tuple l)); rewrite lsol.
Qed.

(* We then explain how we build a parth using the database. *)
Fixpoint make_path (db : state_fmap) (targets : list state)
   (x : state) (fuel : nat) :=
match fuel with
| 0 => None
| S p =>
  if has (fun s => s == x) targets then
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
  forall s l, is_solution [seq p.1 | p <- targets] s l = true ->
  exists l', make_path t [seq p.1 | p <- targets] s depth = Some l' /\
    length l' <= length l.

Definition fact2 := 
  forall targets t s r l depth depth' count,
  bfs _ _ _ find add step depth targets empty count = inl(t, r) ->
  make_path t [seq p.1 | p <- targets] s depth' = Some l ->
  is_solution [seq p.1 | p <- targets] s l = true.

Definition fact3 :=
  forall targets t r depth,
  bfs _ _ _ find add step depth targets empty 0 = inl(t, r) ->
  forall s l, is_solution [seq p.1 | p <- targets] s l = true ->
    length l + 2 <= r /\
  exists s l, is_solution [seq p.1 | p <- targets] s l = true /\
               length l + 2 = r.

Lemma make_path_step db targets x fuel:
  make_path db targets x fuel =
    match fuel with
  | 0 => None
  | S p =>
      if has (fun s : state => s == x) targets
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
      (exists l, make_path db [seq p.1 | p <- targets] s (S depth) = Some l /\
                 is_solution [seq p.1 | p <- targets] s l = true)) ->
   (forall s m, (s, m) \in w -> find db (transition s m) <> None /\
      exists l, make_path db [seq p.1 | p <- targets] (transition s m) depth =
            Some l /\
                is_solution [seq p.1 | p <- targets]
                       (transition s m) l = true) ->
   bfs_aux _ _ _ find add step w w2 db = (w3, db2) ->
   (forall s, find db2 s <> None ->
      (exists l, make_path db2 [seq p.1 | p <- targets] s (S depth) = Some l /\
                 is_solution [seq p.1 | p <- targets] s l = true)).
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
          by apply: sin; rewrite -tsP.
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

Lemma bfs_aux_fact1_2 targets w w2 w3 db db2 depth:
   states_included targets db ->
   (forall s, find db s <> None ->
      (exists l, make_path db [seq p.1 | p <- targets] s depth.+1 = Some l /\
                 is_solution [seq p.1 | p <- targets] s l = true)) ->
   (forall s m, (s, m) \in w -> find db (transition s m) <> None /\
      exists l, make_path db [seq p.1 | p <- targets] (transition s m)
                     depth = Some l /\
                is_solution [seq p.1 | p <- targets] (transition s m) l = true) ->
  (forall s m, (s, m) \in w2 -> find db (transition s m) <> None /\
      exists l, make_path db [seq p.1 | p <- targets]
                       (transition s m) depth.+1 = Some l /\
                is_solution [seq p.1 | p <- targets] (transition s m) l = true) ->
   bfs_aux _ _ _ find add step w w2 db = (w3, db2) ->
   forall s m, (s, m) \in w3 ->
      find db2 (transition s m) <> None /\
      exists l : seq move, make_path db2 [seq p.1 | p <- targets]
                    (transition s m) depth.+1 =
           Some l /\
            is_solution [seq p.1 | p <- targets] (transition s m) l = true.
Proof.
elim: w w2 db => [ | [s m] w Ih] w2 db sin hypdb hypw hypw2.
  by move=> [/[dup] w2q <- /[dup] db2q <-].
rewrite [bfs_aux _ _ _ _ _ _ _ _ _]/=.
case fdbs: (find db s) => [m' | ]; intros bfs_auxq.
  apply: (Ih w2 db) => //.
  by move=> s2 m2 inw; apply: hypw=> /=; rewrite inE inw orbT.
move=> s2 mv s2in.
have paths : exists l, make_path (add db s m) [seq p.1 | p <- targets]
                       s depth.+1 = Some l /\
      is_solution [seq p.1 | p <- targets] s l = true.
  case: (hypw s m) => [ | trin [ls [lsq lssol]]]; first by rewrite inE eqxx.
  exists (m :: ls); split=> //.
  rewrite /=; case: ifP=> [/hasP [ts ints /eqP tsP ] | nexq].
    have /eqP abs : find db s <> None.
      by apply: sin; rewrite -tsP.
    by case: (negP abs); rewrite fdbs.
  rewrite add_find.
  by rewrite (make_path_preserve m fdbs lsq).
apply: (Ih (step s ++ w2) (add db s m) _ _ _ _ bfs_auxq)=> //.
- by apply: states_included_add.
- move=> s'; case: (eqVneq s s') => [<- _ | snq]; first by apply: paths.
  rewrite add_find2 //.
  move=> /hypdb [ls' [ls'q Pls']].
  exists ls'; split; last by [].
  by apply: make_path_preserve.
- move=> s' m' inw.
  have /hypw : (s', m') \in ((s, m) :: w) by rewrite inE inw orbT.
  move=> [trin [ls' [ls'q ls'sol]]].
  split; first by apply: add_find_none.
  exists ls'; split=> //.
  by apply make_path_preserve.
move=> s' m'; rewrite mem_cat=> /orP[s'in_step | s'in2].
  move: s'in_step; rewrite step_def inE => /eqP ->.
  split; first by rewrite add_find.
  by apply: paths.
have [tr'in [l' [mpq l'sol]]] := hypw2 s' m' s'in2.
split; first by apply add_find_none.  
exists l'; split;[ | by []].
by apply: make_path_preserve.
Qed.

Lemma bfs_aux_included1 w w2 w3 db db2 s:
  bfs_aux _ _ _ find add step w w2 db = (w3, db2) ->
  find db2 s <> None <-> s \in [seq p.1 | p <- w] \/ find db s <> None.
Proof.
elim: w w2 db => [ | [a mv] w Ih] w2 db.
  move=> /= [_  <-].
  by rewrite in_nil; intuition done.
case: (eqVneq s a) Ih=> [-> | sna] /=.
  case fdba : (find db a) => [m | ] /[apply] ->;
       rewrite ?fdba ?add_find ?inE ?eqxx; split; intuition easy.
case fdba : (find db a) => [m | ] /[apply].
  by rewrite inE (negbTE sna).
rewrite add_find2; last by rewrite eq_sym.
by rewrite inE (negbTE sna).
Qed.

Lemma at_depth_exists_path targets n s :
  s \in at_depth targets n -> exists2 l, is_solution targets s l & size l = n.
Proof.
by rewrite inE=> /andP[] /existsP[] x sol _; exists x; rewrite ?size_tuple.
Qed.


Lemma bfs_aux_layering n targets w w2 w3 db db2:
  (forall s, find db s <> None -> s \in depth_ge targets n.+1) ->
  (forall s, s \in depth_ge targets n -> find db s <> None) ->
  (forall s p, s \in at_depth targets n -> p \in step s ->
       p \in w \/ find db p.1 <> None) ->
  (forall s, s \in at_depth targets n.+1 -> find db s <> None ->
     step s \subset w2) ->
  (forall p, p \in w -> transition p.1 p.2 \in at_depth targets n) ->
  (forall p, p \in w2 -> transition p.1 p.2 \in at_depth targets n.+1 /\
             find db (transition p.1 p.2) <> None) ->
  bfs_aux _ _ _ find add step w w2 db = (w3, db2) ->
  (forall s, find db2 s <> None <-> s \in depth_ge targets n.+1) /\
  (forall s, s \in at_depth targets n.+1 -> step s \subset w3) /\
  (forall p, p \in w3 -> transition p.1 p.2 \in at_depth targets n.+1).
Proof.
elim: w w2 db => [ | [a m] w Ih] w2 db dbSn dbn invstep stepw2 invw invw2.
  rewrite /= => -[<- <-]; split;[ | split].
  - move=> s; split;[move=> indb | ]; first by have /dbSn := indb.
    rewrite depth_geS inE=> /orP[/dbn // | sinS].
    have [m trin] : exists m, transition s m \in at_depth targets n.
      move: sinS => /[dup] atdS /at_depth_exists_path[] [ | m l] //= + /eqP.
      rewrite eqSS=> + /eqP => /at_depth_decrease /[apply] /(_ atdS) trin.
      by exists m.
    have instep : (s, m) \in step (transition s m).
      by rewrite step_def; rewrite inE eqxx.
    by have [ // | ]:= invstep (transition s m) (s, m) trin instep; tauto.
  - move=> s sinS; apply stepw2=> //.
    have [m trin] : exists m, transition s m \in at_depth targets n.
      move: sinS => /[dup] atdS /at_depth_exists_path[] [ | m l] //= + /eqP.
      rewrite eqSS=> + /eqP => /at_depth_decrease /[apply] /(_ atdS) trin.
      by exists m.
    have instep : (s, m) \in step (transition s m).
      by rewrite step_def; rewrite inE eqxx.
    by have [ // | ]:= invstep (transition s m) (s, m) trin instep; tauto.
  by move=> p pin2; have []:= invw2 _ pin2.
rewrite /=.
have invw' : forall p, p \in w -> transition p.1 p.2 \in at_depth targets n.
  by move=> p pin; apply: invw; rewrite inE pin orbT.
case fdba : (find db a)=> [mv | ].
  have invstep' : forall s p, s \in at_depth targets n ->
       p \in step s -> p \in w \/ find db p.1 <> None.
    move=> s p sin pin.
    have [pa | pna] := eqVneq p.1 a.
      by right; rewrite pa fdba.
    case: (invstep s p sin pin);[rewrite inE=> /orP[]; [ | tauto] | tauto].
    by case: p pna { pin }=> p1 p2; rewrite xpair_eqE /= => /negbTE ->.
  apply: Ih=> //.



Lemma bfs_aux_onion_property targets w w3 db db2 n:
  (forall s, find db s <> None <-> depth_ge targets s n) 

Lemma bfs_fact1 n targets db rounds:
  bfs _ _ _ find add step n targets empty 0 = inl(db, rounds) ->
  forall s, find db s <> None ->
    exists2 l,
      make_path db [seq p.1 | p <- targets] s rounds.+1 = Some l &
      is_solution [seq p.1 | p <- targets] s l = true.
Proof.
suff main :
  forall db0 k,
   (forall s, find db0 s <> None ->
    exists2 l, 
    make_path db0 targets s k+1 = Some l &
    is_solution [seq p.1 | p <- targets] s l = true) ->
    bfs _ _ _ find add step n targets db0 k = inl(db, rounds) ->
  forall s, find db s <> None ->
    exists2 l, 
    make_path db targets s rounds.+1 = Some l & is_solution [seq p.1 | p <- targets] s l = true.
  by apply: main=> s; rewrite find_empty.
elim: n targets=> [ | n Ih] targets db0 k // db_inv.
rewrite [bfs _ _ _ _ _ _ _ _ _ _]/=.
case bfs_auxq : (bfs_aux _ _ _ _ _ _ _ _ _) => [ w2 db'].
  have [w2nil | w2nnil] := eqVneq w2 [::].
    rewrite w2nil=> - [dbdef rounddef].
  have := bfs_aux_fact1.


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
have sol' : is_solution [seq p.1 | p <- targets] s' (p.2 :: l) by rewrite /= tr'.
have [n' /[dup] n'dep [_ n'min]]:= at_depth_exists sol'.
exists n'=> //; apply: (leq_trans (n'min _ sol'))=> /=.
by rewrite sz.
Qed.

Lemma bfs_aux_preserve w w2 w3 db db2 s m:
  bfs_aux _ _ _ find add step w w2 db = (w3, db2) ->
  find db s = Some m -> find db2 s = Some m.
Proof.
elim: w w2 db => [ | [a mv] w Ih] w2 db /=; first by move=> [_ <-].
case fdba: (find db a) => [mv' |]; first by apply: Ih.
move=> bfs_auxq /[dup]fdbs.
suff -> : find db s = find (add db a mv) s by apply: (Ih (step a ++ w2)).
rewrite add_find2 //.
by apply/eqP=> asq; rewrite asq fdbs in fdba.
Qed.

Lemma bfs_aux_preserve_path targets w w2 w3 db db2 s l n :
  bfs_aux _ _ _ find add step w w2 db = (w3, db2) ->
  make_path db targets s n = Some l ->
  make_path db2 targets s n = Some l.
Proof.
elim: n w w2 db s l=> [ | n Ih] w w2 db s l /= bfs_auxq; first by [].
case: ifP=> [ // | not_reached].
case fdbs : (find db s) => [mv | ]; last by [].
rewrite (bfs_aux_preserve bfs_auxq fdbs).
case mptr: (make_path _ _ _ _) => [l' | ]; last by [].
by rewrite (Ih _ _ _ _ l' bfs_auxq).
Qed.

Definition optimal_solution targets s l :=
  is_solution [seq p.1 | p <- targets] s l = true /\
  (forall l', is_solution [seq p.1 | p <- targets] s l' = true -> 
     size l <= size l').

Lemma at_depth_layers n targets w w2 s3 db db2 :
  
Lemma bfs_aux_fact3 n targets w w2 w3 db db2 :
  (forall p, p \in targets -> find db p.1 <> None) ->
  (forall s, find db s <> None ->
     (exists2 l, make_path db targets s n.+1 = Some l &
       optimal_solution targets s l) /\ 
     (forall k s' m', k.+1 < n -> at_depth k targets s ->
         transition s' m' = s -> find db s' <> None)) ->
  (forall p, p \in w ->
    exists l, [/\ make_path db targets 
                     (transition p.1 p.2) n = Some l,
                  optimal_solution targets (transition p.1 p.2) l &
                  size l < n]) ->
  bfs_aux _ _ _ find add step w w2 db = (w3, db2) ->
  (forall s, find db2 s <> None ->
     exists2 l, make_path db2 targets s n.+1 = Some l &
     optimal_solution targets s l).
Proof.
elim: w w2 db => [ | [a mv] w Ih] w2 db targetsin invdb invw.
  move=> [_ <-] s sin; move: (invdb s sin)=> [[l lP1 lP2] layering].
  by exists l.
rewrite [bfs_aux _ _ _ _ _ _ _ _ _]/=.
case fdba : (find db a) => [mv' |].
  move=> bfs_auxq s sin.
  have invw' : forall p, p \in w ->
       exists l, [/\ make_path db targets (transition p.1 p.2) n = Some l,
                     optimal_solution targets (transition p.1 p.2) l &
                     size l < n].
    (* If this proof fails, the statement of inw' should be changed. *)
    by move=> p pin; apply invw; rewrite inE pin orbT.
  have [l lP1 lP2 ] := Ih w2 db targetsin invdb invw' bfs_auxq s sin.
  by exists l.
move=> bfs_auxq s sin.
have [trl [trlP1 trlP2 trlP3]] : exists l,
           [/\ make_path db targets (transition a mv) n = Some l,
              optimal_solution targets (transition a mv) l &
              size l < n].
  rewrite -[X in transition X _]/(a, mv).1 -[X in transition _ X]/(a, mv).2.
  by apply: invw; rewrite inE eqxx.
apply: (Ih (step a ++ w2) (add db a mv)) => //.
- move=> p pin; rewrite add_find2; first by apply: targetsin.
  by apply/eqP=> ap; case: (targetsin p pin); rewrite -ap.
- move=> s' s'in.
  case: (eqVneq a s') => [as' | ans']; last first.
    move: s'in; rewrite add_find2 // => s'in.
    have [[l' l'P1 l'P2] layers] := invdb s' s'in.
    split; [exists l'=> //;apply: make_path_preserve=> //  | ].
    move=> k s2 m' kn deps2 trs2.
    case: (eqVneq a s2)=> [-> | ans2]; first by rewrite add_find.
    by rewrite add_find2 //; apply: (layers k s2 m').
  have Lay : forall k s2 m2, k.+1 < n -> at_depth k targets s2 ->
      transition s2 m2 = s' -> find (add db a mv) s2 <> None.
    move=> k s2 m2 dep2 tr2.
    case: (eqVneq a s2) => [-> | ans2]; first by rewrite add_find.
    rewrite add_find2.
  split.
    rewrite /=; case istarget : (has _ _); first by exists [::].
    exists (mv :: trl); rewrite -as'.
    rewrite add_find.
    move/(make_path_preserve mv fdba) : trlP1 => -> //.

rewrite /=; case starget: (has _ _); first by exists [::].
case fdb2s : (find db2 s) => [m | ].
have -> : find db2 s = 
exists (mv :: trl) => /=.
  case istarget : (has _ _).

exists (mv :: trl).

  simpl.
have : exists2 l, make_path (add db a mv) targets a n.+1 = Some l &
   optimal_solution targets s l.
  
case: (eqVneq s a) => [saq | sna]; last first.
  apply
