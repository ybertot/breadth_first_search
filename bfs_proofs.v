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

Variable transition : state -> move -> option state.

Hypothesis find_empty : forall s, find empty s = None.
Hypothesis add_find : forall d s m, find (add d s m) s = Some m.
Hypothesis add_find2 :
  forall d s1 s2 m, s1 != s2 -> find (add d s1 m) s2 = find d s2.

(* step gives all reverse steps of transition *)
Hypothesis step_def : forall s, 
  step s =i [set p | transition p.1 p.2 == Some s].

Lemma step_transition :
 forall s1 s2,
  (exists m, transition s1 m = Some s2) <-> s1 \in [seq fst p | p <- step s2].
Proof.
intros s1 s2; split.
  move=>[m s1m].
  have : (s1, m) \in [set p | transition p.1 p.2 == Some s2] by rewrite inE s1m.
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
    match transition x m with
      Some y => is_solution targets y l1
    | None => false
    end
  end.

(* we then explain what it means to be at depth n *)
Definition at_depth (targets : list state) (n : nat) : {set state} :=
  [set x |
  [exists t : {tuple n of move}, is_solution targets x t] &&
  [forall i : 'I_n, [forall t : {tuple i of move}, ~~is_solution targets x t]]].

Lemma at_depthP targets n s:
  reflect ((exists2 l, is_solution targets s l & size l = n) /\
           forall l, is_solution targets s l -> n <= size l)
      (s \in at_depth targets n).
Proof.
apply: Bool.iff_reflect.
split.
  move=> [[l sol zl] optim]; rewrite inE; apply/andP; split.
    by apply/existsP; exists (tcast zl (in_tuple l)); rewrite val_tcast.
  apply/forallP=> -[i iltn]; apply/forallP=> -[l' /eqP /= zl'].
  apply/negP=> abs. 
  have := optim l' abs; rewrite leqNgt=> /negP [].
  by rewrite zl'.
rewrite inE=> /andP[] /existsP[][l /= /eqP zl] sol optim.
split; first by exists l.
move=> l' sol'; rewrite leqNgt; apply/negP=> zl'.
move: optim=> /forallP /(_ (Ordinal zl')) /forallP /(_ (in_tuple l')).
by move=> /negP[] /=.
Qed.

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
    apply/at_depthP; split; first by exists l.
    move=> l' abs; rewrite ltnNge; apply/negP=> zl'.
    case/negP: ngedx; rewrite inE; apply/existsP.
    by exists (insub_bseq n l'); rewrite insubdK.
    (* TODO : understand why rewrite /= fails here.
    rewrite -[X in is_true X]/(size l' <= n). *)
  case/negP: ngedx; rewrite inE; apply/existsP; exists (insub_bseq n l).
  rewrite insubdK //.
  (* same TODO applies here *)
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
apply/subsetP=> s /at_depthP[] [l sol zl] _.
have zl' : size l <= n by rewrite zl.
(* TODO : complain that cast_bseq is useless here *)
by rewrite inE; apply/existsP; exists (widen_bseq zl' (in_bseq l)).
Qed.

Lemma at_depthSNge (targets : list state) (n : nat) :
  at_depth targets n.+1 :&: depth_ge targets n = set0.
Proof.
apply/eqP; rewrite setI_eq0 disjoint_subset; apply/subsetP=> s.
move/at_depthP=> [] _ nosol.
rewrite 3!inE /=; apply/negP=>/existsP[] l.
move/nosol; rewrite ltnNge=> /negP[].
by rewrite size_bseq.
Qed.

Lemma at_depth_decrease targets n s s' m l :
  s \in at_depth targets n.+1 ->
  transition s m = Some s' ->
  is_solution targets s' l ->
  size l = n ->
  s' \in at_depth targets n.
Proof.
move=>/at_depthP[] _ optim /= sms' sol zl.
apply/at_depthP; split; first by exists l.
move=> l' sol'.
have := optim (m :: l').
by rewrite /= sms' => /(_ sol'); rewrite ltnS.
Qed.

Definition at_depth_step (targets : list state) (n : nat) :
  \bigcup_(s in at_depth targets n) 
     [set s' in [seq p.1 | p <- step s] | s' \notin depth_ge targets n] =
  at_depth targets n.+1.
Proof.
apply/setP=> s';apply/bigcupP/idP.
  move=> [] s sin; rewrite 2!inE => /andP[]/[dup]s'in /mapP[]p pin s'p.
  move=> /existsP/= optim.
  have : s' \in depth_ge targets n.+1.
    move: sin; rewrite inE=> /andP[] /existsP[] l sol W.
    have sl' : size (p.2 :: l) <= n.+1 by rewrite /= size_tuple.
    rewrite inE; apply/existsP; exists (Bseq sl')=> /=.
    rewrite s'p.
    by move: pin; rewrite step_def inE => /eqP ->.
  by rewrite depth_geS 2!inE=> /orP[] // /existsP sn; case: optim.
move=> /[dup]s'in /at_depthP[] []l sol zl optim.
case lq : l zl => [ | mv l'] // zl.
have [s sms] : exists s, transition s' mv = Some s.
  move: sol; rewrite lq /=.
  by case: (transition s' mv) => [s | ] //; exists s.
have sols : is_solution targets s l'.
  by move: sol; rewrite lq /= sms.
exists s; last first.
  have /step_transition : exists m, transition s' m = Some s.
    by exists mv.
  move=> sin; rewrite inE sin; apply/negP; rewrite inE=> /existsP[] l2 sol2.
  by have := optim l2 sol2; rewrite ltnNge size_bseq.
by apply: (at_depth_decrease s'in sms sols); move: zl=> /= [].
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

Lemma at_depth_unique n n' s targets : s \in at_depth targets n ->
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

Lemma at_depth0 targets : targets =i at_depth targets 0.
Proof.
move=> s; rewrite inE; apply/idP/idP.
  move=> sin; apply/andP; split.
    by apply/existsP; exists [tuple].
  by apply/forallP=> - [x xlt0].
by move=>/andP[] /existsP[] t; have := tuple0 t => ->.
Qed.


Lemma at_depth_exists s targets l :
  is_solution targets s l -> exists n, s \in at_depth targets n.
Proof.
suff main : forall n l, size l <= n ->
    is_solution targets s l -> exists n', s \in at_depth targets n'.
  by apply: (main (size l)).
elim=> [ | n Ih] {}l szl sol.
  case : l szl sol => //= _ sin.
  by exists 0; rewrite -at_depth0.
have [/existsP [n' /existsP [t]] | there] := boolP [exists i : 'I_n.+1,
        [exists t : {tuple i of move}, is_solution targets s t]].
  by apply: Ih; rewrite size_tuple -ltnS ltn_ord.
have zl : size l = n.+1.
  move: szl; rewrite leq_eqVlt => /orP[/eqP // | szlt].
  case/negP: there; apply/existsP; exists (Ordinal szlt).
  by apply/existsP; exists (in_tuple l).
exists (size l).
apply/at_depthP; split; first by exists l.
move=> l' sol'; rewrite zl ltnNge; apply/negP; rewrite -ltnS => zl'.
case/negP: there; apply/existsP.
by exists (Ordinal zl'); apply/existsP; exists (in_tuple l').
Qed.

Lemma depth_ge_exists s targets n :
  s \in depth_ge targets n -> 
  exists2 n', s \in at_depth targets n' & n' <= n.
Proof.
rewrite inE=> /existsP [l lsol].
have [n' n'P1] := at_depth_exists lsol; exists n' => //.
apply: leq_trans (size_bseq l).
case : (leqP n' (size l)) => // lltn'.
by move: n'P1=> /at_depthP[] _ /(_ l lsol); rewrite leqNgt lltn'.
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
       match transition x m with
       | Some y =>
         match make_path db targets y p with
         | None => None
         | Some l => Some (m :: l)
         end
      | None => None
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

Lemma bfs_step (fuel : nat) (w : seq (state * move)) (settled : state_fmap)
   round:
   bfs _ _ _ find add step fuel w settled round =
  match fuel with
  | 0 => inr (w, settled)
  | p.+1 =>
      let (w0, s) :=
        bfs_aux state move state_fmap find add step w [::] settled in
      match w0 with
      | [::] => inl (s, round)
      | _ :: _ => bfs _ _ _ find add step p w0 s (round + 1)%coq_nat
      end
  end.
Proof. by case: fuel. Qed.

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
           match transition x m with
             Some y =>
             match make_path db targets y p with
             | Some l => Some (m :: l)
             | None => None
             end
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
case trq : (transition x m') => [y | ] //.
case mpq : (make_path db targets y depth) => [ l' | ] // [eql].
have nochange : find (add db s m) x = find db x.
  by rewrite add_find2 //; apply/eqP=> sx; move: dbnone; rewrite sx fdbx.
by rewrite nochange fdbx trq (Ih y l') ?eql.
Qed.

Lemma make_path_add_length db targets s depth l :
  make_path db targets s depth = Some l ->
  make_path db targets s depth.+1 = Some l.
Proof.
elim: depth s l => [ | n Ih] s l //.
rewrite 2!make_path_step.
case exq : (has _ _)=> //.
case fdbq : (find db s) => [m | ] //.
case trq : (transition s m) => [s' | ] //.
case mq : (make_path _ _ _ _)=> [l' | ] //.
by move/Ih : mq => ->.
Qed.

Lemma make_path_le db targets s n m l :
  n <= m -> make_path db targets s n = Some l ->
  make_path db targets s m = Some l.
Proof.
elim: m => [ | m Ih].
  by rewrite leqn0=> /eqP ->.
rewrite leq_eqVlt=> /orP[/eqP <- // | ].
rewrite ltnS.
by move=> /Ih /[apply]; apply: make_path_add_length.
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
(* Not redoing, this is just part of at_depthP *)
by rewrite inE=> /andP[] /existsP[] x sol _; exists x; rewrite ?size_tuple.
Qed.

Lemma at_depth_depth_ge_le s targets n m :
  s \in at_depth targets n -> s \in depth_ge targets m ->
  n <= m.
Proof.
by move=> sin; move/depth_ge_exists=> [] n' /(at_depth_unique sin) ->.
Qed.

Lemma at_depth_le s targets l n :
  s \in at_depth targets n -> is_solution targets s l -> n <= size l.
Proof.
move=> sin sol.
suff : s \in depth_ge targets (size l) by apply: at_depth_depth_ge_le.
by rewrite inE; apply/existsP; exists (in_bseq l).
Qed.

Lemma bfs_aux_layering n targets w w2 w3 db db2:
  (forall s, find db s <> None -> s \in depth_ge targets n.+1) ->
  (forall s, s \in depth_ge targets n -> find db s <> None) ->
  (forall s p, s \in at_depth targets n -> p \in step s ->
       p \in w \/ find db p.1 <> None) ->
  (forall s, s \in at_depth targets n.+1 -> find db s <> None ->
     step s \subset w2) ->
  (forall p, p \in w -> 
     exists2 s, transition p.1 p.2 = Some s & s \in at_depth targets n) ->
  (forall p, p \in w2 -> 
      exists2 s, transition p.1 p.2 = Some s &
             s \in at_depth targets n.+1 /\
             find db s <> None) ->
  (forall s m n, s \in at_depth targets n.+1 -> find db s = Some m ->
     exists2 s', transition s m = Some s' &
       find db s' <> None /\ s' \in at_depth targets n) ->
  bfs_aux _ _ _ find add step w w2 db = (w3, db2) ->
  (forall s, find db2 s <> None <-> s \in depth_ge targets n.+1) /\
  (forall s, s \in at_depth targets n.+1 -> step s \subset w3) /\
  (forall p, p \in w3 -> 
     exists2 s, transition p.1 p.2 = Some s & s\in at_depth targets n.+1) /\
  (forall s m n, s \in at_depth targets n.+1 -> find db2 s = Some m ->
     exists2 s', transition s m = Some s' &
       find db2 s' <> None /\ s' \in at_depth targets n).
Proof.
elim: w w2 db => [ | [a m] w Ih] w2 db dbSn dbn invstep stepw2 invw invw2 dbc.
  rewrite /= => -[<- <-]; split;[ | split; [ | split]].
  - move=> s; split;[move=> indb | ]; first by have /dbSn := indb.
    rewrite depth_geS inE=> /orP[/dbn // | sinS].
    have [m [tsm tsmq trin]] : exists m, 
       exists2 tsm, transition s m = Some tsm & tsm \in at_depth targets n.
      move: sinS => /[dup] atdS /at_depth_exists_path[] [ | m l] //= + /eqP.
      case trq: (transition s m) => [tsm | ] //.
      rewrite eqSS=> + /eqP => /at_depth_decrease /[apply] /(_ s m atdS) trin.
      by exists m, tsm => //; apply: trin.
    have instep : (s, m) \in step tsm.
      by rewrite step_def inE tsmq.
    by have [ // | ] := invstep tsm (s, m) trin instep.
  - move=> s sinS; apply stepw2=> //.
    (* TODO : check about duplication of work. *)
    have [m [tsm tsmq trin]] : exists m, 
       exists2 tsm, transition s m = Some tsm & tsm \in at_depth targets n.
      move: sinS => /[dup] atdS /at_depth_exists_path[] [ | m l] //= + /eqP.
      case trq: (transition s m) => [tsm | ] //.
      rewrite eqSS=> + /eqP => /at_depth_decrease /[apply] /(_ s m atdS) trin.
      by exists m, tsm => //; apply: trin.
    have instep : (s, m) \in step tsm.
      by rewrite step_def inE tsmq.
    by have [ // | ]:= invstep _ (s, m) trin instep.
  - by move=> p pin2; have [tp tpq tpin]:= invw2 _ pin2; exists tp; tauto.
  exact dbc.
rewrite /=.
have invw' : forall p, p \in w -> 
  exists2 s, transition p.1 p.2 = Some s & s \in at_depth targets n.
  by move=> p pin; apply: invw; rewrite inE pin orbT.
case fdba : (find db a)=> [mv | ].
  have invstep' : forall s p, s \in at_depth targets n ->
       p \in step s -> p \in w \/ find db p.1 <> None.
    move=> s p sin pin.
    have [pa | pna] := eqVneq p.1 a.
      by right; rewrite pa fdba.
    case: (invstep s p sin pin);[rewrite inE=> /orP[]; [ | tauto] | tauto].
    by case: p pna { pin }=> p1 p2; rewrite xpair_eqE /= => /negbTE ->.
  by apply: Ih.
have aSn : a \in depth_ge targets n.+1.
  have [tam trq tamd] : exists2 tam, transition a m = Some tam & 
       tam \in at_depth targets n.
    by apply: (invw (a, m)); rewrite inE eqxx.
  have /at_depth_exists_path [l sol zl]:= tamd.
  have zl' : size (m :: l) <= n.+1.
    by rewrite /= ltnS zl.
  rewrite inE; apply/existsP; exists (widen_bseq zl' (in_bseq (m :: l))).
  by rewrite /=; rewrite trq.
have aSn' : a \in at_depth targets n.+1.  
  by move: aSn; rewrite depth_geS inE=> /orP[] // /dbn [].
apply: Ih=> //.
- move=> s; have [<- _ // | ans] := eqVneq a s.
  by rewrite add_find2 //; apply: dbSn.
- move=> s sin; apply: add_find_none.
  by apply: dbn.  
- move=> s [s' m'] sin.
  have [as'q | ans'] := eqVneq a s'.
    by move=> _; right; rewrite as'q add_find.  
  move=> instep; have := invstep s _ sin instep; rewrite inE.
  rewrite xpair_eqE eq_sym (negbTE ans') /=.
  by rewrite add_find2.
- move=> s sin; have [-> _ | ans'] := eqVneq a s.
    by apply/subsetP=> x xin; rewrite mem_cat xin.
  (* TODO : complain about missing (_ \subset _ ++ _) theorems *)
  rewrite add_find2 // => fdbs; apply/subsetP=> p pin; rewrite mem_cat.
  by apply/orP; right; move: p pin; apply/subsetP/stepw2.
- move=> p; rewrite mem_cat=> /orP[ | inw2]; last first.
    have := invw2 _ inw2=> -[tp tpq [tpin1 tpdb]].
    by exists tp=> //; split=> //; apply: add_find_none.
  by rewrite step_def inE=> /eqP ->; exists a=> //; rewrite add_find.
move=> s ms n2 sin2.
case : (eqVneq a s)=> [ /[dup] asq -> | ans].
  rewrite add_find => -[<-].
  have := invw (a, m); rewrite inE eqxx => /(_ isT)[] s' tamq s'in.
  exists s'=> //; first by rewrite -asq.
  split.
    by apply/add_find_none/dbn; rewrite (subsetP (at_depth_sub_ge _ _)).
  by move: sin2; rewrite -asq=> /(at_depth_unique aSn') [] <-.
rewrite !add_find2 // => fdbs.
have [s' tsmq [fdbs' s'in2]]:= dbc _ _ _ sin2 fdbs.
exists s'=> //; split => //.
rewrite add_find2 //.
apply/eqP => as'q; case s'in2.
have fdbsN : find db s <> None by rewrite fdbs.
have n2len : n2 <= n.
  by have := at_depth_depth_ge_le sin2 (dbSn _ fdbsN); rewrite ltnS.
rewrite -as'q in s'in2.
have := at_depth_unique s'in2 aSn'.
by move: n2len=> /[swap] ->; rewrite ltnn.
Qed.

Lemma bfs_depth_main targets n' n w db db2 :
  w =i \bigcup_(s in at_depth targets n) [set x in step s] ->
  (forall s, find db s <> None <-> s \in depth_ge targets n) ->
  (forall s m n, s \in at_depth targets n.+1 -> find db s = Some m ->
     exists2 s', transition s m = Some s' &
       find db s' <> None /\ s' \in at_depth targets n) ->
  (forall k, bfs _ _ _ find add step n'.+1 w db n.+1 = inl(db2, k.+1) ->
    (forall s, find db2 s <> None <-> s \in depth_ge targets k.+1) /\
    at_depth targets k.+2 = set0 /\
  (forall s m n, s \in at_depth targets n.+1 -> find db2 s = Some m ->
     exists2 s', transition s m = Some s' &
       find db2 s' <> None /\ s' \in at_depth targets n)) /\
  (forall w2, bfs _ _ _ find add step n'.+1 w db n.+1 = inr(w2, db2) ->
   w2 =i \bigcup_(s in at_depth targets (n' + n).+1) [set x in step s] /\
   (forall s, find db2 s <> None <-> s \in depth_ge targets (n' + n).+1) /\
   (forall s m n, s \in at_depth targets n.+1 -> find db2 s = Some m ->
     exists2 s', transition s m = Some s' &
       find db2 s' <> None /\ s' \in at_depth targets n)).
Proof.
elim: n' n w db=> [ | n' Ih] n w db.
  rewrite /= => wq dbq dbc.
  case bfs_auxq: (bfs_aux _ _ _ _ _ _ _ _ _) => [w' db'].
  have inge1 : forall s, find db s <> None -> s \in depth_ge targets n.+1.
    by move=> s /dbq; rewrite depth_geS [_ \in _ :|: _]inE => ->.
  have inge : forall s, s \in depth_ge targets n -> find db s <> None.
    by move=> s; rewrite -dbq.
  have stepin:
    forall s p, s \in at_depth targets n -> p \in step s -> p \in w \/
           find db p.1 <> None.
    move=> s p sin pin; left; rewrite wq; apply/bigcupP.
    by exists s; rewrite // inE.
  have subnil : forall s, s \in at_depth targets n.+1 -> find db s <> None ->
             step s \subset nil.
    move=> s sinS; rewrite dbq => sin.
    suff : s \in set0 by rewrite inE.
    by have <- := at_depthSNge targets n; rewrite inE sin sinS.
  have trw : forall p, p \in w ->
    exists2 tp, transition p.1 p.2 = Some tp & tp \in at_depth targets n.
    move=> p; rewrite wq=> /bigcupP[s sin]; rewrite inE.
    by rewrite step_def inE=> /eqP ->; exists s.
  have trnil : 
    forall p, p \in nil -> 
       exists2 tp, transition p.1 p.2 = Some tp &
         tp \in at_depth targets n.+1 /\ find db tp <> None.
    by [].
  have [db'q [stepinS [trw' db'c]]] :=
    bfs_aux_layering inge1 inge stepin subnil trw trnil dbc bfs_auxq.
  case w'q : w' => [ | p1 w''];split; [ | discriminate | discriminate |].
    move=> k [<- <-]; split=> //.
    split; last by apply: db'c.
    apply/setP=> s; rewrite in_set0; apply/negP.
    move=> /[dup] deps /at_depth_exists_path[] l sol zl.
    case lq: l zl => [ | m l'] // [zl].
    move: sol; rewrite lq /=.
    case tsmq : (transition s m) => [tsm | ] // sol.
    have trSn := at_depth_decrease deps tsmq sol zl.
    have stepsub := stepinS _ trSn.
    have instep : (s, m) \in step tsm by rewrite step_def inE tsmq.
    suff : (s, m) \in w' by rewrite w'q.
    by rewrite (subsetP stepsub).
  rewrite -w'q=> w2 [<- <-]; split; last by [].
  move=> p; apply/idP/idP.
    move=> pin.
    have [tp tpq tpd] : exists2 tp, transition p.1 p.2 = Some tp &
                            tp \in at_depth targets n.+1.
      by apply: trw'.
    by apply/bigcupP; exists tp=> //; rewrite inE step_def inE tpq.
  move=> /bigcupP[s sin]; rewrite inE => pin.
  by rewrite (subsetP (stepinS _ sin)).
move=> wq dbq dbc.
rewrite bfs_step.
(* rewrite -[bfs _ _ _ _ _ _ _ _ _ _]/
   (let (w3, db3) := bfs_aux _ _ _ find add step w [::] db in
   match w3 with [::] => inl (db3, n.+1)
   | _ => bfs _ _ _ find add step n'.+1 w3 db3 (n.+1 + 1)%nat end). *)
case bfs_auxq: (bfs_aux _ _ _ _ _ _ _ _ _) => [w3 db3].
(* TODO : all subproofs down to trnil have to be shared with the base case:
  right now, it is a simple copy paste, adjusted for indentation. *)
have inge1 : forall s, find db s <> None -> s \in depth_ge targets n.+1.
  by move=> s /dbq; rewrite depth_geS [_ \in _ :|: _]inE => ->.
have inge : forall s, s \in depth_ge targets n -> find db s <> None.
  by move=> s; rewrite -dbq.
have stepin:
  forall s p, s \in at_depth targets n -> p \in step s -> p \in w \/
         find db p.1 <> None.
  move=> s p sin pin; left; rewrite wq; apply/bigcupP.
  by exists s; rewrite // inE.
have subnil : forall s, s \in at_depth targets n.+1 -> find db s <> None ->
           step s \subset nil.
  move=> s sinS; rewrite dbq => sin.
  suff : s \in set0 by rewrite inE.
  by have <- := at_depthSNge targets n; rewrite inE sin sinS.
have trw : forall p, p \in w -> 
   exists2 tp, transition p.1 p.2 = Some tp & tp \in at_depth targets n.
  move=> p; rewrite wq=> /bigcupP[s sin]; rewrite inE.
  by rewrite step_def inE=> /eqP ->; exists s.
have trnil : 
  forall p, p \in nil -> 
    exists2 tp, transition p.1 p.2 = Some tp & tp \in at_depth targets n.+1 /\
         find db tp <> None.
  by [].
have [db'q [stepinS [trw' db'c]]] :=
  bfs_aux_layering inge1 inge stepin subnil trw trnil dbc bfs_auxq.
have w3q : w3 =i \bigcup_(s in at_depth targets n.+1) [set x in step s].
  move=> p; apply/idP/idP.
    move=> /trw' [tp tpq trin]; apply/bigcupP; exists tp=> //.
    by rewrite inE step_def inE tpq.
  move=>/bigcupP[s sin]; rewrite inE=> pin.
  by rewrite (subsetP (stepinS _ sin)).
have [Ihl Ihr] := Ih (n.+1) w3 db3 w3q db'q db'c.
move: Ihr; rewrite ?addn1 !addnS !addSn=> Ihr.
case w3q' : w3 => [ | p3 w4]; split;[ | discriminate | | ].
- move=> k [<- <-] {k}; split=> //.
(* TODO : big duplication here. *)
  split; last by apply: db'c.
  apply/setP=> s; rewrite in_set0; apply/negP.
  move=> /[dup] deps /at_depth_exists_path[] l sol zl.
  case lq: l zl => [ | m l'] // [zl].
  move: sol; rewrite lq /=; case tsmq : (transition s m) => [tsm | ] // sol.
  have trSn := at_depth_decrease deps tsmq sol zl.
  have stepsub := stepinS _ trSn.
  have instep : (s, m) \in step tsm by rewrite step_def inE tsmq.
  suff : (s, m) \in w3 by rewrite w3q'.
  by rewrite (subsetP stepsub).
- by rewrite -w3q' PeanoNat.Nat.add_succ_r PeanoNat.Nat.add_0_r.
by rewrite -w3q' PeanoNat.Nat.add_succ_r PeanoNat.Nat.add_0_r.
Qed.

Lemma depth_ge0 targets : targets =i depth_ge targets 0.
Proof.
move=> s; rewrite inE; apply/idP/idP.
  by move=> sin; apply/existsP; exists [bseq].
by move=>/existsP[] /= l; have := bseq0 l => ->.
Qed.

Lemma at_depth_empty_le targets n m : n <= m ->
  at_depth targets n = set0 -> at_depth targets m = set0.
Proof.
move=> nm.
suff main k : at_depth targets n = set0 -> at_depth targets (k + n) = set0.
  by rewrite -(subnK nm); apply: main.
elim: k => [ | k Ih] //.
move=> /Ih {}Ih; rewrite addSn; apply/setP=> s; rewrite in_set0; apply/negP.
move=>/[dup] sinS /at_depth_exists_path[][ |m' l]//= sol [] zl.
move: sol; case tsmq : (transition s m') => [tsm' | ] // sol.
have sm'in := at_depth_decrease sinS tsmq sol zl.
by move/setP: Ih=> /(_ tsm'); rewrite in_set0=> /negP; apply.
Qed.

Lemma bfs_aux_layer0 m targets w1 db1 :
  bfs_aux _ _ _ find add step [seq (s, m) | s <- targets]
                    nil empty = (w1, db1) ->
  (forall s, find db1 s <> None -> s \in at_depth targets 0) /\
      (forall s,  s \in depth_ge targets 0 -> find db1 s <> None) /\
      (forall s p, s \in at_depth targets 0 -> p \in step s ->
        p \in w1) /\
      (forall s, s \in at_depth targets 1 -> find db1 s <> None ->
          step s \subset [::]) /\
      (forall p, p \in w1 -> 
          exists2 tp, transition p.1 p.2 = Some tp &
                   tp \in at_depth targets 0) /\
      (forall p, p \in [::] ->
        exists2 tp, transition p.1 p.2 = Some tp
           & tp \in at_depth targets 1 /\ find db1 tp <> None).
Proof.
suff main (ts : seq state) :
  forall db w2,
  (targets =i [set s in ts] :|: [set s | find db s != None]) ->
  (w2 =i \bigcup_(s in [set s | find db s != None]) [set p in step s]) ->
  bfs_aux _ _ _ find add step [seq (s, m) | s <- ts] w2 db = (w1, db1) ->
  (forall s, find db1 s <> None -> s \in at_depth targets 0) /\
      (forall s,  s \in depth_ge targets 0 -> find db1 s <> None) /\
      (forall s p, s \in at_depth targets 0 -> p \in step s ->
        p \in w1) /\
      (forall s, s \in at_depth targets 1 -> find db1 s <> None ->
          step s \subset [::]) /\
      (forall p, p \in w1 ->
          exists2 tp, transition p.1 p.2 = Some tp
              & tp \in at_depth targets 0) /\
      (forall p, p \in [::] ->
          exists2 tp, transition p.1 p.2 = Some tp &
           tp \in at_depth targets 1 /\ find db1 tp <> None).
  apply: (main targets empty [::]).
    have -> : [set s | find empty s != None] = set0.
      by apply/setP; move=> s; rewrite inE find_empty eqxx in_set0.
    by rewrite setU0=> s; rewrite inE.
  move=> s /=; rewrite in_nil; apply/esym/negP=> /bigcupP=> -[] s'.
  by rewrite inE find_empty.
elim: ts => [ | s ts Ih] db w2.
  move=> /= targetsq w2q [<- <-].
    have targetsq' : forall s, s \in targets <-> find db s <> None.
      by move=>s; split; rewrite targetsq !inE in_nil=> /eqP.
  have db0 : forall s, find db s <> None -> s \in at_depth targets 0.
    by move=> s fdbs; rewrite -at_depth0 targetsq'.
  split; first by [].
  split.
    by move=> s; rewrite -depth_ge0 targetsq'.
  split.
    move=> s p; rewrite -at_depth0 targetsq'=> /eqP sin pin.
    by rewrite w2q; apply/bigcupP; exists s; rewrite inE.
  split.
    move=> s sin1 /db0 sin; suff : s \in set0 by rewrite in_set0.
    rewrite -(at_depthSNge targets 0) inE sin1.
    by rewrite (subsetP (at_depth_sub_ge _ _)).
  split.
    move=> p; rewrite w2q=>/bigcupP[] s; rewrite inE=> /eqP/db0 sin.
    by rewrite inE step_def inE => /eqP ->; exists s.
  by [].
move=> targetsq w2q /=.
case fdbs : (find db s) => [m' | ].
  apply: Ih=> //.
  move=> s'; rewrite targetsq !inE.
  by have [-> | s'ns]  := eqVneq s' s; first rewrite fdbs !orbT.
apply: Ih.
  move=> s'; rewrite !inE targetsq !inE.
  have [-> | s'ns]  := eqVneq s' s; first by rewrite add_find !orbT.
  by rewrite add_find2 1?eq_sym.
move=> p; rewrite mem_cat; apply/idP/bigcupP.
  move=> /orP[pins | ].
    exists s; rewrite inE //; first by rewrite add_find.
  rewrite w2q=> /bigcupP[] s'; rewrite !inE=> /eqP sin pins'.
  have sns' : s != s' by apply/eqP=> ss'; case sin; rewrite -ss' fdbs.
  by exists s'; rewrite !inE ?add_find2 //; apply/eqP.
move=>[] s'; have [ss' _ | sns'] := eqVneq s s'.
  by rewrite inE ss' => ->.
rewrite !inE add_find2 // => s'in pins'.
apply/orP; right.
by rewrite w2q; apply/bigcupP; exists s'; rewrite inE.
Qed.

Lemma bfs_depth_bound m targets n db2 k:
  bfs _ _ _ find add step n.+2 
    [seq (s, m) | s <- targets] empty 0 = inl (db2, k.+1) ->
  (forall s, find db2 s <> None <-> s \in depth_ge targets k.+1) /\
  at_depth targets k.+2 = set0 /\
  (forall s m n, s \in at_depth targets n.+1 ->
  find db2 s = Some m ->
  exists2 s', transition s m = Some s' &
   find db2 s' <> None /\ s' \in at_depth targets n).
Proof.
rewrite bfs_step.
case bfs_aux0q : (bfs_aux _ _ _ _ _ _ _ _ _) => [w1 db0].
have [db0depth [depth0in [depth1in [startw2 [propw1 propw2]]]]] :=
  bfs_aux_layer0 bfs_aux0q.
case w1q: w1 => [ | e w1'].
  move=> [<- <-]; split;[ | split].
  - move=> s; split; last by move/depth0in.
    by move/db0depth; apply/subsetP/at_depth_sub_ge.
  - apply/setP=> s; rewrite in_set0; apply/negP=>/[dup] sin.
    move=> /at_depth_exists_path[] [ | m' []] /= sol zl //.
    suff : (s, m') \in w1 by rewrite w1q.
    move: sol; case tsmq : (transition s m') => [tsm' | ] // sol.
    apply: (depth1in tsm' (s, m')).
      by rewrite -at_depth0.
    by rewrite step_def inE tsmq.
  move=> s m2 n2 sin2 fdbs.
  have /db0depth : find db0 s <> None by rewrite fdbs.
  by move=> /(at_depth_unique sin2).
rewrite -w1q [(0 + 1)%coq_nat]/=.
move=> bfsq.
have w1q' : w1 =i \bigcup_(s in at_depth targets 0) [set x in step s].
  move=> p; apply/idP/idP.
    move=> /propw1 [tp tpq tr1].
    by apply/bigcupP; exists tp => //; rewrite inE step_def inE tpq.
  by move=>/bigcupP[] s /depth1in; rewrite inE=> /[apply] - [].
have db0q : forall s, find db0 s <> None <-> s \in depth_ge targets 0.
  move=> s; split; first by move=> /db0depth; apply/subsetP/at_depth_sub_ge.
  by move=> /depth0in.
have db0c : forall s m n, s \in at_depth targets n.+1 ->
  find db0 s = Some m ->
  exists2 s', transition s m = Some s' &
   find db0 s' <> None /\ s' \in at_depth targets n.
 move=> s2 m2 n2.
  move=> s2in2 s2db.
  have /db0q : find db0 s2 <> None by rewrite s2db.
  by rewrite -depth_ge0 at_depth0=> /(at_depth_unique s2in2).
have [endcase contcase] := bfs_depth_main n db2 w1q' db0q db0c.
by have := endcase _ bfsq; tauto.
Qed.

(* Lemma bfs_depth guarantees that the longest path is smaller than k.+2, but
  it may well be smaller than k.+1.  For a more precise estimate of the
  longest path length, we need to observe the last non-empty working list. *)

Lemma bfs_depth_witness m targets n db2 w :
  bfs _ _ _ find add step n [seq (s, m) | s <- targets] empty 0 =
  inr(w, db2) ->
  (forall p, p \in w -> find db2 p.1 = None -> p.1 \in at_depth targets n) /\
  ((forall p, p \in w -> find db2 p.1 <> None) -> at_depth targets n = set0).
Proof.
case: n => [ | n].
  rewrite /= => -[<- <-]; split.
    by move=> p /mapP[] s + -> //=; rewrite at_depth0.
  move=> abs.
  apply/setP; move=> s; rewrite in_set0 -at_depth0; apply/negP=> sin.
  by apply: (abs (s, m)); rewrite ?find_empty //; apply/mapP; exists s.
case: n => [ | n].
  rewrite /=; case bfs_auxq : (bfs_aux _ _ _ _ _ _ _ _ _)=> [w3 db3].
  case w3q : w3 => [ // | p' w3']; rewrite -w3q {w3q p' w3'}.
  move=> [<- <-].
  have [db3d0 [deb0db3 [step0w [dep1ndb3 [w3P _]]]]] :=
    bfs_aux_layer0 bfs_auxq.
  split.
    move=> [s ms] /= inw3 ndb3; apply/at_depthP; split.
      by exists [:: ms]; move: (w3P _ inw3)=> //= [sms ->]; rewrite at_depth0.
    move=> l sol; rewrite ltnNge leqn0 size_eq0; apply/negP=> /eqP lnil.
    by move: sol; rewrite lnil=> /=; rewrite depth_ge0=> /deb0db3[].
  move=> all0; apply/setP=> s; rewrite in_set0; apply/negP.
  move=> /[dup] sd1.
  move=>/at_depthP[][][ | m' [ | ? ?]] // /=.
  case tsmq : (transition s m') => [tsm' | ] // + _.
  have : (s, m') \in step tsm' by rewrite step_def inE tsmq.
  rewrite at_depth0=> /step0w /[apply] /all0/db3d0 /=.
  by move=> /(at_depth_unique sd1).
rewrite bfs_step.
case bfs_auxq: (bfs_aux _ _ _ _ _ _ _ _ _) => [w3 db3].
case w3q : w3 => [ | m3 w4] //; rewrite -w3q {m3 w4 w3q}.
rewrite [(0 + 1)%coq_nat]/=.
have [db3d0 [deb0db3 [step0w [dep1ndb3 [w3P _]]]]] :=
    bfs_aux_layer0 bfs_auxq.
have w1q' : w3 =i \bigcup_(s in at_depth targets 0) [set x in step s].
  move=> p; apply/idP/idP.
    move=> /w3P [] tp tpq tpin.
    apply/bigcupP; exists tp => //.
    by rewrite inE step_def inE tpq.
  by move=>/bigcupP[] s; rewrite inE; apply step0w.
have db0q : forall s, find db3 s <> None <-> s \in depth_ge targets 0.
  move=> s; split; first by move=> /db3d0; apply/subsetP/at_depth_sub_ge.
  by apply: deb0db3.
(* TODO : code duplication. *)
have db0c : forall s m n, s \in at_depth targets n.+1 ->
  find db3 s = Some m ->
  exists2 s', transition s m = Some s' &
   find db3 s' <> None /\ s' \in at_depth targets n.
 move=> s2 m2 n2.
  move=> s2in2 s2db.
  have /db0q : find db3 s2 <> None by rewrite s2db.
  by rewrite -depth_ge0 at_depth0=> /(at_depth_unique s2in2).
have [_ contcase] := bfs_depth_main n db2 w1q' db0q db0c.
move=> /contcase; rewrite addn0=> -[wq [ZZ _]].
split.
  move=> p; rewrite wq=> /bigcupP[] s sin; rewrite inE=> pin pndb.
  suff : p.1 \in depth_ge targets n.+2.
    by rewrite depth_geS inE=> /orP[] //; rewrite -ZZ pndb.
  move: sin=> /at_depth_exists_path[] l sol zl.
  move: pin; rewrite step_def inE=> /eqP trps.
  have zl' : size (p.2 :: l) <= n.+2 by rewrite /= zl.
  rewrite inE; apply/existsP=> /=; exists (Bseq zl') => /=.
  by rewrite trps.
move=> /= alldb.
apply/setP=> s; rewrite in_set0; apply/negP.
move=> /[dup]sdn2.
move=> /at_depthP[][] [ | m' l] // sol /= [zl] nshort.
have zl' : size l <= n.+1  by rewrite zl.
move: sol => /=; case tsmq : (transition s m') => [ tsm' | ] // sol.
have : tsm' \in at_depth targets n.+1.
   by have := at_depth_decrease sdn2 tsmq sol zl.
move=> /[dup] trn /(subsetP (at_depth_sub_ge targets n.+1)) trindb.
have /alldb/=/ZZ sdn1 : (s, m') \in w.
  rewrite wq; apply/bigcupP; exists tsm'=> //.
  by rewrite inE step_def inE tsmq.
suff : s \in set0 by rewrite in_set0.
by rewrite -(at_depthSNge targets n.+1); rewrite inE sdn2 sdn1.
Qed.

Lemma bfs_shiftr n w w2 k1 k2 db db2 :
  bfs _ _ _ find add step n w db k1 = inr(w2, db2) ->
  bfs _ _ _ find add step n w db k2 = inr(w2, db2).
Proof.
elim: n w db k1 k2=> [ | n Ih] w db k1 k2//=.
case: (bfs_aux _ _ _ _ _ _ _ _ _)=> [w' db'].
case w'q : w' => [ | p3 w3] //; rewrite -w'q {p3 w3 w'q}.
by apply: Ih.  
Qed.

Lemma bfs_cat n m w w2 w3 k1 k2 k3 db db2 db3:
  bfs _ _ _ find add step n w db k1 = inr(w2, db2) ->
  bfs _ _ _ find add step m w2 db2 k2 = inr(w3, db3) ->
  bfs _ _ _ find add step (n + m) w db k3 = inr(w3, db3).
Proof.
elim: n w k1 k3 db => [ | n Ih] w k1 k3 db.
  move=> /= [] <- <-; rewrite add0n.
  by apply: bfs_shiftr.
rewrite /=; case bfsaq : (bfs_aux _ _ _ _ _ _ _ _ _) => [w' db'] .
case w'q : w' => [ | p4 w4] //; rewrite -w'q {w'q p4 w4}.
by move=> cp1 cp2; have := Ih _ _ (k3 + 1)%coq_nat _ cp1 cp2.
Qed.

Lemma table_consistent_make_path N db targets :
  (forall s, find db s <> None <-> s \in depth_ge targets N) ->
  (forall s m n, s \in at_depth targets n.+1 -> find db s = Some m ->
     exists2 s', transition s m = Some s' &
       find db s' <> None /\ s' \in at_depth targets n) ->
  forall s n, n <= N -> s \in at_depth targets n ->
     exists2 l, make_path db targets s n.+1 = Some l &
      is_solution targets s l /\ size l = n.
Proof.
move=> bnd consistent /[swap]; elim => [ | n Ih] s nN.
  rewrite -at_depth0=> sin /=.
  have -> : has (eq_op^~ s) targets; last by exists [::].
  by apply/hasP; exists s.
move=> /[dup] sin1 /(subsetP (at_depth_sub_ge _ _)).
move=> /(subsetP (depth_ge_trans targets nN)) /bnd.
case fdbq : (find db s) => [ m | ] // _.
have [s' tsmq [fdbs' s'in]] := consistent _ _ _ sin1 fdbq.
have nleN : n <= N by exact: (ltnW nN).
have [l' l'q [sol' zl']] := Ih s' nleN s'in.
exists (m :: l').
  rewrite make_path_step fdbq tsmq l'q.
  case : ifP=> /hasP //.
  move=> -[] x /[swap] /eqP ->; rewrite at_depth0=> sin0.
  by have := at_depth_unique sin1 sin0.
by rewrite /= tsmq zl' sol'.
Qed.

(* This is the final theorem:
  if breadth_first_search succeeds (result of the form inl(db, k) then:
  - the number in the result is an over estimate of the maximal length
    of solutions
  - the table can be used by function make_path (which will always
    succeeds on elements of the path) to produce optimal solutions *)

Lemma bfs_make_path_optimal db targets n m k:
  bfs _ _ _ find add step n.+2 [seq (s, m) | s <- targets] empty 0 =
  inl (db, k.+1) ->
  forall s, find db s <> None ->
    [/\ s \in depth_ge targets k.+1,
    is_solution targets s (odflt [::] (make_path db targets s k.+2)) &
    forall l, is_solution targets s l ->
       size (odflt [::] (make_path db targets s k.+2)) <= size l].
Proof.
move=> bfsq.
have [dle [_ expath]] := bfs_depth_bound bfsq.
move=> s /[dup] fdbn; case fdbq : (find db s) => [ms | ] // _.
have := table_consistent_make_path dle expath.
have /dle/depth_ge_exists[ n' sin' n'le]  := fdbn.
move=> /(_ s n' n'le sin')[l lq [sol zl]].
have n'le' : n'.+1 <= k.+2 by rewrite ltnS.
rewrite (make_path_le n'le' lq) /=; split => //; first by apply/dle.
by rewrite zl=> l2 sol2; apply: (at_depth_le sin').
Qed.
