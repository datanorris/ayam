(*
ACCESS MODES:
The library defines a number of atomic operations (Clause 32) and operations on mutexes (Clause 33) that are
specially identified as synchronization operations. These operations play a special role in making assignments
in one thread visible to another. A synchronization operation on one or more memory locations is either a
consume operation, an acquire operation, a release operation, or both an acquire and release operation. A
synchronization operation without an associated memory location is a fence and can be either an acquire
fence, a release fence, or both an acquire and release fence. In addition, there are relaxed atomic operations ,
which are not synchronization operations, and atomic read-modify-write operations, which have special
characteristics. [ Note: For example, a call that acquires a mutex will perform an acquire operation on
the locations comprising the mutex. Correspondingly, a call that releases the same mutex will perform a
release operation on those same locations. Informally, performing a release operation on A forces prior side
effects on other memory locations to become visible to other threads that later perform a consume or an
acquire operation on A. “Relaxed” atomic operations are not synchronization operations even though, like
synchronization operations, they cannot contribute to data races. — end note ]
*)

Require Import List Program RelationClasses.
From hahn Require Import Hahn.

Inductive Mode := 
| mPln
| mRlx
| mCns
| mAcq
| mRel
| mAcqRel
| mSc.

Definition Loc := nat.

(* What about memory locations vs. atomic/non-atomic objects *)

Inductive Op' :=
| write (m: Mode | In m [mPln;mRlx;mRel;mAcqRel;mSc]) (l: Loc)
| read (m: Mode | In m [mPln;mRlx;mCns;mAcq;mAcqRel;mSc]) (from: Op')
| fence (m: Mode | In m [mAcq;mRel;mAcqRel;mSc])
| rmw (m: Mode | In m [mAcq;mRel;mAcqRel;mSc]) (from: Op').

Definition IsRead' (o: Op') :=
  match o with
    read _ _
  | rmw _ _ => true
  | _ => false
  end.
Definition IsWrite' (o: Op') :=
  match o with
    write _ _
  | rmw _ _ => true
  | _ => false
  end.
Definition IsFence' (o: Op') :=
  match o with
    fence _ => true
  | _ => false
  end.
Definition IsRMW' (o: Op') :=
  match o with
    rmw _ _ => true
  | _ => false
  end.

Program Definition from' (o: Op' | IsRead' o) :=
  match `o as o'
    return IsRead' o' -> Op'
  with
    write _ _
  | fence _ => _
  | read _ f
  | rmw _ f => fun _ => f
  end (proj2_sig o).

Conjecture events': Op' -> Prop.
Conjecture events'_finite: set_finite events'.

Program Fixpoint OP_WF (o: Op'): Prop :=
  ⟪ op_event: events' o ⟫ /\
  ⟪ op_reads_from_write: forall s: IsRead' o, IsWrite' (from' o) ⟫ /\
  ⟪ op_from_wf: forall s: IsRead' o, OP_WF (from' o) ⟫.

Definition Op := { o: Op' | OP_WF o }.

Definition IsRead (o: Op) := IsRead' (`o).
Definition IsWrite (o: Op) := IsWrite' (`o).
Definition IsFence (o: Op) := IsFence' (`o).
Definition IsRMW (o: Op) := IsRMW' (`o).

Definition Read := { o: Op | IsRead o }.
Definition Write := { o: Op | IsWrite o }.
Definition Fence := { o: Op | IsFence o }.
Definition ReadWrite := { o: Op | ~IsFence o }.

Definition Read_To_ReadWrite (o: Read): ReadWrite.
Proof.
  destruct o as [owf r].
  pose (owf2 := owf).
  destruct (owf) as [[]].
  all: refine (exist _ owf2 _).
  all: auto.
Defined.

Definition Write_To_ReadWrite (o: Write): ReadWrite.
Proof.
  destruct o as [owf w].
  pose (owf2 := owf).
  destruct (owf) as [[]].
  all: refine (exist _ owf2 _).
  all: auto.
Defined.

Definition mode (o: Op) :=
  match `o with
    read (exist _ m _) _
  | write (exist _ m _) _
  | fence (exist _ m _)
  | rmw (exist _ m _) _ => m
  end.

Definition IsRel (o: Op) := In (mode o) [mRel;mAcqRel;mSc].
Definition IsAcq (o: Op) := In (mode o) [mAcq;mAcqRel;mSc].

(*
Fixpoint rf_chain_length (o: Op') :=
  match o with
    write _ _
  | fence _ => 0
  | read _ f
  | rmw _ f => 1 + (rf_chain_length f)
  end.
*)

Lemma write_not_fence o: IsWrite' o -> ~IsFence' o.
Proof.
  destruct o.
  all: auto.
Qed.

Fixpoint loc' (o: Op') (WF: OP_WF o) (NF: ~IsFence' o) :=
  match o as o'
    return ~IsFence' o' -> OP_WF o' -> Loc
  with
    write _ l => fun _ _ => l
  | read _ f
  | rmw _ f => fun _ '(conj _ (conj rfw fwf)) => loc' f (fwf eq_refl) (write_not_fence f (rfw eq_refl))
  | fence _ => fun NF' WF' => match NF' eq_refl with end
  end NF WF.

Definition loc (o: ReadWrite) :=
  loc' (``o) (proj2_sig (`o)) (proj2_sig o).

Lemma sig_ext: forall T P (x y: {o: T | P o}), `x = `y -> x = y.
Proof.
  unfold proj1_sig.
  ins.
  destruct x as [x p], y as [y q].
  subst y.
  assert (p = q).
  apply proof_irrelevance.
  subst q.
  reflexivity.
Qed.

Lemma eq_dec_Op': forall o1 o2: Op', {o1 = o2} + {o1 <> o2}.
Proof.
  pose sig_ext.
  pose f_equal.
  decide equality.
  decide equality.
  all: assert (sumbool (`m = `m0) (`m <> `m0)).
  1,3,5,7: decide equality.
  destruct H.
  left; auto. right; contradict n; auto.
  destruct H0.
  left; auto. right; contradict n; auto.
  destruct H.
  left; auto. right; contradict n; auto.
  destruct H0.
  left; auto. right; contradict n; auto.
Qed.

Lemma test3: forall A: Type, well_founded (fun x y => @length A x < @length A y).
Proof.
  unfold well_founded; ins.
  assert (H : forall n a, length a < n -> Acc (fun x y => @length A x < @length A y) a).
  { induction n.
    - intros; absurd (length a < 0); auto with *.
    - intros a0 Ha. constructor 1. intros b Hb.
      apply IHn. apply PeanoNat.Nat.lt_le_trans with (length a0); auto with arith. }
  apply (H (S (length a))). auto with arith.
Defined.

Lemma test: forall A: Type, well_founded (fun x y => @length A x < @length A y).
Proof.
  unfold well_founded; ins.
  pose (n := S (length a)).
  assert (length a < n); auto.
  generalize n a H.
  clear n H.
  induction n.
  auto with *.
  constructor 1.
  intros.
  apply IHn.
  auto with *.
Qed.

Lemma test2: forall A: Type, well_founded (fun x y => @length A x < @length A y).
Proof.
  constructor 1.
  induction a.
  2: constructor 1.
  all: simpl in *; auto with *.
Qed.

(*
provide forall a, Acc r a - all elements accessible
 - reverse map a to an inductive type l such that map(l) = a?
 - induct on l, provide Acc r a in context C[l] to prove C[l] -> Acc r map(l)
   - in base case b, provide C[b] -> Acc r map(b)
     - eg there is no predecessor for map(b), all elems w/o predecessors reverse map to b
   - in other case s with predecessors p, provide Acc r map(s) with C[s] and (C[p] -> Acc r map(p))
     - if we didnt map(l) to a, Acc r a would not be rewritten to map(s) and map(p) in here
     - then this would amount to proving C[p] from C[s] which is recursively proving a contradiction in C[b], but C[l] is sound remember?
     - we prove C[p] from C[s] and then we have Acc r map(p) i.e. forall y, r y map(p) -> Acc r y
     - forall y, r y map(s) -> forall y2, r y2 y -> eg if we can prove r y2 map(p), Acc r y2
 - inductive type needs
   - map(b) an object with fixed predecessors (eg none)
   - map(s) can walk back a fixed # steps such that forall y, r y map(p) (eg 2)
   - this is impossible - do we have to define the whole dag?
     - Acc itself is like a dag
 - Dont need to map l to a single a, map to a subset of a's by introducing a constraint in context
   - prove forall a, C[l] -> Acc r a by induction, for some inductive l, C[l] expresses a constraint on a
     - top level l must be chosen so C[top] is true for a
     - top can be independent of a if C[top] is true for any a
   - forall a, C[base] -> Acc r a
     - forall a, C[base] -> forall y, r y a -> Acc r y
     - C[base] constrains a to have no predecessors, forall y, r y a -> R(base) with R(base) -> False
     - for List, base is []
     - for Acc, base is any element _:Acc r a where forall y, r y a -> False
   - (forall a, C[pred] -> Acc r a) -> forall a, C[succ] -> Acc r a:
     - Given a constrained with C[succ], predecessors of a required to be constrained with C[pred]
     - (forall b, (forall yp, r yp b -> R(pred)) -> Acc r b) ->
       forall a,
       (forall ys, r ys a -> R(succ)) ->
       forall y,
       r y a ->
       Acc r y
     - b = y, ys = y -> R(succ), (forall yp, r yp y -> R(pred)) -> Acc r y
     - prove forall a y, r y a -> R(succ) -> forall yp, r yp y -> R(pred)
     - given condition R(succ) on a y, r y a, and pred smaller than succ, prove R(pred) on yp, r yp y
   - induction predecessors are chosen from the available structurally smaller types, in the successor calc
   - So for R: forall a y (p: r y a) (l: inductive) -> Prop we need
     - forall a y p, R a y p top
     - forall a y p, R a y p base -> False
     - forall a y p succ, R a y p succ ->
         forall yp (pp: r yp y),
         exists pred (_: Predecessor(succ,pred)),
         R y yp pp pred
     - R
       - admits all a y in the biggest l
       - provably admits no a y in the smallest l
       - if it admits a y in l, it admits y yp in some inductive predecessor of l.
   - suggests a scheme to iteratively restrict the a y that it admits
     - in this case admitting a y in l means it must admit all transitive predecessor relations of y
     - because r is acyclic, predecessor relations on predecessors of a do not need to support a
       - exclude a with each step to meet the succ/pred condition
     - because Op is finite, we have a list of all possible elements in r
       - forall a _ _, R a _ _ list is inclusion of a in list
       - full list is top
       - empty list is base
       - forall a _ _ succ, R a _ _ succ, the predecessor is succ excluding a
     - need to define a list inductive type where forall a, excluding a is a predecessor
       - Acc (fun x y => lenth(x) < length(y)) findom
*)

Lemma acy_wf: forall (r: relation Op), acyclic r -> well_founded r.
Proof.
  unfold well_founded, acyclic; intros r irr.
  destruct events'_finite as [findom in_findom].
  pose (sig_ext := sig_ext _ OP_WF).
  (* pose (sig_ext2 := f_equal (@proj1_sig _ OP_WF)). *)
  assert (findom_acc: Acc (fun x y => length(x) < length(y)) findom).
  { clear in_findom.
    constructor 1; induction findom.
    2: constructor 1.
    all: simpl in *; auto with *. }
  assert (in_dom: forall o: Op, In (`o) findom).
  { intros o; destruct o as [o' wf]. { destruct o'; red in wf; desf; auto. } }
  intros.
  assert (C: forall y, r⁺ y a -> In (` y) findom).
  intros; apply in_dom.
  clear in_dom in_findom; revert a C.
  induction findom_acc; constructor 1; intros.
  assert (H1t: r⁺ y a); auto with *.
  specialize (C y H1t) as C_y.
  pose (C_y2 := C_y); apply In_split in C_y2; destruct C_y2 as [l1 [l2 Heqsplit]]; subst x.
  apply H0 with (l1 ++ l2).
  rewrite !app_length; simpl; auto with *.
  intros yp pp.
  assert (`a <> `y).
  intros ay; apply sig_ext in ay.
  subst a.
  apply irr with y.
  auto with *.
  generalize (C yp); rewrite !in_app_iff; simpl.
  intros in_or; destruct in_or as [il1 | [ eq_a | il2 ]].
  constructor 2 with y; auto.
  auto.
  apply sig_ext in eq_a; subst yp; apply irr in pp; auto with *.
  auto.
Qed.

Lemma wf_t_invariant A (r: relation A):
  well_founded r <-> well_founded r⁺.
Proof.
  split; intros WF; intros y.
  induction y using (well_founded_induction WF).
  constructor 1.
  intros x rxy.
  induction rxy.
  auto.
  apply IHrxy2; auto.
  induction y using (well_founded_induction WF).
  constructor 1.
  intros x rxy.
  apply H.
  constructor 1.
  auto.
Qed.

Lemma wf_acy A (r: relation A) (WF: well_founded r):
  acyclic r.
Proof.
  apply wf_t_invariant in WF.
  unfold acyclic, irreflexive, well_founded in *.
  intros.
  induction x using (well_founded_induction WF).
  specialize (H0 x H H).
  assumption.
Qed.

Lemma wf_not_infinite_descending A (r: relation A) (WF: well_founded r):
  forall f, ~(forall n, r (f (S n)) (f n)).
Proof.
  unfold not; intros f.
  remember (f 0) as x.
  revert f Heqx.
  specialize (WF x).
  induction WF.
  intros; subst x.
  eapply H0 with (f := fun x => f (S x)).
  eapply H1.
  auto.
  auto.
  (* refine (
      (fix rec n (a: Acc r (f n)) :=
         match a
         with
           Acc_intro _ p =>
             rec (S n) (p (f (S n)) (H n))
         end) 0 WF). *)
Qed.

(*
why is it so hard to prove that a prefix of a well-founded relation has a well founded inverse?
because its false.
 - we know r is well founded
   - for all x, r is well-founded up to x
   - meaning for all r y x we know r is well founded up to y
   - which is the statement of inductibility
     - a proposition P x is proved by induction on r if it can be proved assuming it's true for all
       y prior to x in r.
     - unrestricted fixpoints can prove anything so they must be constrained - fix p: ~sky(blue) := p
       - If the fixpoint terminates, in the base case it does not call itself, so it
         doesn't rely on itself for its own proof. Non-base cases are then proved incrementally upward.
       - It terminates if it does not take any infinite path. Requiring fixpoints to descend a
         well-founded relation is one way to achieve this.
     - In coq, fixpoints are restricted by requiring them to descend in the structure of an inductive type
       in order to invoke themselves
       - for well-founded induction on x, we want to prove P x using proofs of P y for r y x. In the base
         case there will be no such y.
       - Our fixpoint will prove P x by descending some inductive Acc r x into Acc r y for all r y x
         - fix proof_p x (a: Acc r x): P x :=
             let prior_p y ryx := proof_p y (a y ryx) in _
     - Our inductive Acc provides the minimal necessary access, and its type, forall y (r y x), forall z (r z y)
       etc. essentially exhibits a proof that there are descending chains in r, and because it's an inductive,
       a proof that these chains all terminate.
       - fix Acc r x := forall y, r x y -> Acc r y
   - How do you instantiate an inductive like Acc r x?
     - By recursion on another inductive type, proving it in an assumption context C which is provable
       at the top level:
       - if x converts to (f i) and depends on i, induct on i to prove C i -> Acc r (f i)
       - otherwise, induct on some i to prove forall x, C i x -> Acc r x
     - At each step, the context assumption is available to prove Acc for current i, and to
       induct we must provide proofs of the context assumptions for prior i from the current ones
     - For Acc, to prove forall y, r y x -> Acc r y, we can manually construct Acc r y down to some
       fixed depth, then we need inductive proofs of all predecessors.
     - If induction gives access to (prior i) -> C (prior i) -> Acc r (f (prior i)),
       - We can obtain Acc r y for all r y (f (prior i))
       - We must be able to prove that after we costruct Acc r (f i) down to a fixed depth,
         all Acc r y that we need to obtain will be for y that are r y (f (prior i))
         - Similarly, in the base case with no (prior i), then there is no such y
     - If induction gives access to (prior i) -> forall x, C (prior i) x Acc r x
       - After constructing to fixed depth, forall Acc r y we need from induction we must
         prove C (prior i) z for y = z or r y z
       - And in the base case, with no (prior i), that there is no y
     - The role of the context is to restrict the x in Acc r x so that in the base case there are no
       predecessors, at the top level it doesnt restrict x at all, and at each step it restricts x
       sufficiently that we can prove that the available Acc r y for C (prior i) y are sufficient to build Acc r x
       - E.g. inducting on list l with context (r y x -> In y l) - complete in top case, empty in base case,
         and restricting all our necessary y to be in l, we just need to prove that these y are also In y (prior l)
*)

Definition f_u x y :=
  x <> 5 /\ (x < y \/ y = 5).

Lemma wf_fu: well_founded f_u.
Proof.
  assert (forall x, x <> 5 -> Acc f_u x).
  intros x xn5.
  induction x using (well_founded_induction (Wf_nat.well_founded_ltof _ id)).
  unfold Wf_nat.ltof, id in *.
  constructor 1; intros y y0; destruct y0 as [yn5 [ylx|x5]].
  apply H; assumption.
  contradiction.
  intros x.
  constructor 1; intros y y0; destruct y0 as [yn5 _].
  apply H; assumption.
Qed.

Lemma nwf_fu_inv: ~well_founded (f_u ⨾ ⦗f_u⁻¹ 5⦘)⁻¹.
Proof.
  intros wf; set (i := 6); specialize (wf i).
  assert (i >= 6).
  constructor 1.
  induction wf.
  eapply H1.
  eexists.
  split.
  split.
  auto with *.
  left.
  constructor 1.
  split.
  reflexivity.
  split; auto with *.
  auto with *.
Qed.

Lemma imm_trans: forall (r: relation Op), strict_partial_order r -> r ≡ (immediate r)⁺.
Proof.
  intros r [irr tra].
  assert (acy: acyclic r).
    assert (t: r⁺ ⊆ r).
      intros x y rxy.
      induction rxy.
      auto.
      eapply tra; eauto.
    intros x rxx.
    apply t in rxx.
    eapply irr; eauto.
  assert (ind := well_founded_induction (acy_wf r acy)).
  eassert (ind_inv := well_founded_induction (acy_wf r⁻¹ ?[acy_inv])).
  [acy_inv]: {
    assert (H: forall x y, r⁻¹⁺ x y -> r⁺ y x).
      intros x y rxy.
      induction rxy.
      constructor 1; assumption.
      econstructor 2; eauto.
    intros x rxx.
    eapply acy; eapply (H x x); assumption.
  }
  split.
  autounfold with unfolderDb.
  intros x y; revert x.
  induction y using ind.
  intros x.
  induction x using ind_inv.
  destruct (classic (exists c, r x c /\ r c y)) as [[c [rxc rcy]]|n_imm].
  constructor 2 with c.
  apply H; auto.
  apply H0; auto.
  intros rxy; constructor 1; split; auto.
  intros c rxc rcy; apply n_imm.
  eexists; eauto.
  autounfold with unfolderDb.
  intros x y H.
  induction H.
  intuition.
  apply tra with y; auto.
Qed.

(*
SB:
Sequenced before is an asymmetric, transitive, pair-wise relation between evaluations executed by a single
thread, which induces a partial order among those evaluations.
*)

Conjecture sb: relation Op.
Conjecture sb_order: strict_partial_order sb.

(*
Do we need to model threads? 2 actions on the same thread are not "potentially concurrent" unless in a signal handler,
so if they are unsequenced and conflict it's undefined. So 2 reads to the same location, or 2 actions on different
locations, can be unsequenced.
    
Conjecture thread: Op -> nat.
Conjecture sb_same_thread: forall x y, sb x y -> thread x = thread y.
*)

(*
MO:
All modifications to a particular atomic object M occur in some particular total order, called the modification
order of M. [ Note: There is a separate order for each atomic object. There is no requirement that these can
be combined into a single total order for all objects. In general this will be impossible since different threads
may observe modifications to different objects in inconsistent orders. — end note ]
*)

Conjecture mo: relation Write.
Conjecture mo_same_loc_only: mo ≡ restr_eq_rel (loc ∘ Write_To_ReadWrite) mo.
Conjecture mo_total_order_per_loc: forall l: Loc, strict_total_order (fun x => (loc ∘ Write_To_ReadWrite) x = l) mo.

(*
RS:
A release sequence headed by a release operation A on an atomic object M is a maximal contiguous subsequence of
side effects in the modification order of M, where the first operation is A, and every subsequent operation
 — is performed by the same thread that performed A, or
 — is an atomic read-modify-write operation.
*)

Definition rs :=
  let mo' := (@proj1_sig _ _) ↑ mo in
  fun x y =>
    (⦗IsRel⦘ ⨾ mo'^?) x y /\
    forall z, mo' x z -> mo'^? z y ->
      sb x z \/ IsRMW z.

Definition rs2 :=
  let mo' := (@proj1_sig _ _) ↑ mo in
    ⦗IsRel⦘ ⨾ mo'^? \ (mo' \ sb) ⨾ ⦗set_compl IsRMW⦘ ⨾ mo'^?.

Definition rs3 :=
  let mo' := (@proj1_sig _ _) ↑ immediate mo in
    ⦗IsRel⦘ ⨾ (((mo' ⨾ ⦗IsRMW⦘)＊ ⨾ mo') ∩ sb)＊ ⨾ (mo' ⨾ ⦗IsRMW⦘)＊.

Lemma rs_rs2: rs ≡ rs2.
Proof.
  unfold rs, rs2, same_relation, inclusion, seq, minus_rel, eqv_rel, not, clos_refl, set_compl.
  all: repeat (intros; des; try split).
  1,4: exists z; auto.
  1-4: specialize (H0 z0); subst z z1; tauto.
  1,4: shelve.
  all: subst z.
  all: apply NNPP; unfold not; intros; apply H0.
  all: exists z0; split; auto; exists z0; tauto.
  Unshelve.
  all: subst z.
  all: exists x.
  all: tauto.
Qed.

Lemma rs_rs3: rs ≡ rs3.
Proof.
  unfold rs, rs3.
  autounfold with unfolderDb.
  split.
  - set (mo' := (@proj1_sig _ _) ↑ mo).
    assert (mo_mo': forall x y, mo x y <-> mo' (`x) (`y)).
      split.
      intros moxy.
      eexists; eexists; split; try split.
      1-3: eauto.
      intros moxy.
      destruct moxy as (e' & f' & moxy' & ex & fy).
      apply sig_ext in ex.
      apply sig_ext in fy.
      subst e' f'.
      auto.
    assert (mo'_mo: forall x y, mo' x y <-> exists x' y', `x' = x /\ `y' = y /\ mo x' y').
      intros x y.
      split.
      intros moxy.
      destruct moxy as (e' & f' & moxy' & <- & <-).
      eexists; esplit; try esplit; eauto.
      intros (e & f & <- & <- & moxy).
      apply mo_mo'; auto.
    assert (spo: strict_partial_order mo').
      specialize (mo_total_order_per_loc (0)).
      intros sto; destruct sto as [[irr tra]].
      split.
      intros x mxx.
      apply mo'_mo in mxx.
      destruct mxx as (e & f & ex & <- & moxy).
      apply sig_ext in ex; subst f.
      eapply irr; eauto.
      intros x y z moxy moyz.
      apply mo'_mo in moxy as (e & f & <- & <- & moxy).
      apply mo'_mo in moyz as (f' & g & ff & <- & moyz).
      apply sig_ext in ff.
      subst f'.
      apply mo_mo'.
      eapply tra; eauto.
    intros x y [[z [[xz xIsRel] moxy]] rsCond].
    subst z.
    exists x; split; auto.
    destruct moxy as [xy|(x' & y' & moxy & <- & <-)].
    eexists; esplit; rewrite clos_refl_transE.
    1, 2: left; auto.
    clear xIsRel.
    apply mo_mo' in moxy.
    apply (imm_trans mo' spo) in moxy.
    induction moxy.
    destruct H as [moxy' imm].
    pose (moxy := moxy'); apply mo'_mo in moxy; destruct moxy as (x'' & y'' & <- & <- & moxy'').
    assert (sb (`x'') (`y'') \/ IsRMW (`y'')).
      eapply rsCond.
      eexists; eexists; split; try split.
      2,3: eauto.
      auto.
      left; auto.
    destruct H.
    all: eexists; esplit; erewrite clos_refl_transE.
    right; constructor 1; split.
    eexists; esplit.
    erewrite clos_refl_transE.
    left; auto.
    eexists; eexists; split; split.
    1-5: eauto.
    intros x moxc mocy.
    eapply imm.
    eapply mo_mo'.
    apply moxc.
    eapply mo_mo'.
    auto.
    left; auto.
    left; auto.
    right; constructor 1; esplit; esplit.
    eexists; eexists; split; split.
    1-5: eauto.
    intros x moxc mocy.
    eapply imm.
    eapply mo_mo'.
    apply moxc.
    eapply mo_mo'.
    auto.
Qed.


  
(*
SW:
Certain library calls synchronize with other library calls performed by another thread. For example, an
atomic store-release synchronizes with a load-acquire that takes its value from the store (32. 4). [ Note: Except
in the specified cases, reading a later value does not necessarily ensure visibility as described below. Such a
requirement would sometimes interfere with efficient implementation. —end note ] [ Note: The specifications
of the synchronization operations define when one reads the value written by another. For atomic objects ,
the definition is clear. All operations on a given mutex occur in a single total order. Each mutex acquisition
“ reads the value written” by the last mutex release. — end note ]
*)

*)
(*
RACE:
If a side effect on a memory location (4. 4) is unsequenced relative to either another side effect on the same memory location or a
value computation using the value of any object in the same memory location, and they are not potentially
concurrent, the behavior is undefined

Two expression evaluations conflict if one of them modifies a memory location (4. 4) and the other one reads
or modifies the same memory location.

Two actions are potentially concurrent if
 — they are performed by different threads, or
 — they are unsequenced, at least one is performed by a signal handler, and they are not both performed
by the same signal handler invocation.

The execution of a program contains a data race if it contains two potentially concurrent conflicting actions ,
at least one of which is not atomic, and neither happens before the other, except for the special case for
signal handlers described below. Any such data race results in undefined behavior.
*)

(*
A conforming implementation executing a well-formed program shall produce the same observable behavior as
one of the possible executions of the corresponding instance of the abstract machine with the same program
and the same input .

The least requirements on a conforming implementation are :
— Accesses through volatile glvalues are evaluated strictly according to the rules of the abstract machine.
— At program termination, all data written into files shall be identical to one of the possible results that
execution of the program according to the abstract semantics would have produced.
— The input and output dynamics of interactive devices shall take place in such a fashion that prompting
output is actually delivered before a program waits for input. What constitutes an interactive device is
implementation-defined.

These collectively are referred to as the observable behavior of the program.

The value of an object visible to a thread T at a particular point is the initial value of the object, a value
assigned to the object by T, or a value assigned to the object by another thread, according to the rules
below.


CD:
An evaluation A carries a dependency to an evaluation B if
 — the value of A is used as an operand of B, unless :
   — B is an invocation of any specialization of std: : kill_dependency (32. 4), or
   — A is the left operand of a built - in logical AND (&&, see 8. 1 4) or logical OR ( | |, see 8. 1 5) operator, or
   — A is the left operand of a conditional (? :, see 8. 1 6) operator, or
   — A is the left operand of the built - in comma (, ) operator (8. 1 9) ;
or
 — A writes a scalar object or bit-field M, B reads the value written by A from M, and A is sequenced
before B, or
 — for some evaluation X, A carries a dependency to X, and X carries a dependency to B.
[ Note: “Carries a dependency to” is a subset of “ is sequenced before”, and is similarly strictly intra- thread.
— end note ]

DOB:
An evaluation A is dependency-ordered before an evaluation B if
 — A performs a release operation on an atomic object M, and, in another thread, B performs a consume
operation on M and reads a value written by any side effect in the release sequence headed by A, or
 — for some evaluation X, A is dependency-ordered before X and X carries a dependency to B.
[ Note: The relation “ is dependency-ordered before” is analogous to “ synchronizes with”, but uses release/ -
consume in place of release/acquire. — end note ]

ITHB:
An evaluation A inter-thread happens before an evaluation B if
 — A synchronizes with B, or
 — A is dependency-ordered before B, or
 — for some evaluation X
   — A synchronizes with X and X is sequenced before B, or
   — A is sequenced before X and X inter- thread happens before B, or
   — A inter-thread happens before X and X inter-thread happens before B.
[ Note: The “ inter-thread happens before” relation describes arbitrary concatenations of “sequenced before”,
“synchronizes with” and “dependency-ordered before” relationships, with two exceptions. The first exception
is that a concatenation is not permitted to end with “dependency-ordered before” followed by “sequenced
before”. The reason for this limitation is that a consume operation participat ing in a “dependency-ordered
before” relationship provides ordering only with respect to operations to which this consume operation
actually carries a dependency. The reason that this limitation applies only to the end of such a concatenation
is that any subsequent release operation will provide the required ordering for a prior consume operation.
The second exception is that a concatenation is not permitted to consist entirely of “sequenced before”. The
reasons for this limitation are (1) to permit “inter- thread happens before” to be transitively closed and (2)
the “happens before” relation, defined below, provides for relationships consisting entirely of “sequenced
before”. — end note ]

HB:
An evaluation A happens before an evaluation B (or, equivalently, B happens after A) if:
 — A is sequenced before B, or
 — A inter-thread happens before B.
The implementation shall ensure that no program execution demonstrates a cycle in the “happens before”
relation. [ Note: This cycle would otherwise be possible only through the use of consume operations. — end
note ]

SHB:
An evaluation A strongly happens before an evaluation B if either
 — A is sequenced before B, or
 — A synchronizes with B, or
 — A strongly happens before X and X strongly happens before B.
[ Note: In the absence of consume operations, the happens before and strongly happens before relations are
identical. S trongly happens before essentially excludes consume operations. — end note ]

VSE:
A visible side effect A on a scalar object or bit-field M with respect to a value computation B of M satisfies
the conditions:
 — A happens before B and
 — there is no other side effect X to M such that A happens before X and X happens before B.
The value of a non-atomic scalar object or bit-field M, as determined by evaluation B, shall be the value
stored by the visible side effect A. [ Note: If there is ambiguity about which side effect to a non-atomic object
or bit-field is visible, then the behavior is either unspecified or undefined. — end note ] [ Note: This states
that operations on ordinary objects are not visibly reordered. This is not actually detectable without data
races, but it is necessary to ensure that data races, as defined below, and with suitable restrictions on the use
of atomics, correspond to data races in a simple interleaved (sequentially consistent ) execution. —end note ]

COHERENCE:
The value of an atomic object M, as determined by evaluation B, shall be the value stored by some side effect
A that modifies M, where B does not happen before A. [ Note: The set of such side effects is also restricted
by the rest of the rules described here, and in particular, by the coherence requirements below. — end note ]

COHERENCE:
If an operation A that modifies an atomic object M happens before an operation B that modifies M, then
A shall be earlier than B in the modification order of M. [ Note: This requirement is known as write-write
coherence. — end note ]

COHERENCE:
If a value computation A of an atomic object M happens before a value computation B of M, and A takes
its value from a side effect X on M, then the value computed by B shall either be the value stored by X or
the value stored by a side effect Y on M, where Y follows X in the modification order of M. [ Note: This
requirement is known as read-read coherence. — end note ]

COHERENCE:
If a value computation A of an atomic object M happens before an operation B that modifies M, then A
shall take its value from a side effect X on M, where X precedes B in the modification order of M. [ Note:
This requirement is known as read-write coherence. — end note ]

COHERENCE:
If a side effect X on an atomic object M happens before a value computation B of M, then the evaluation B
shall take its value from X or from a side effect Y that follows X in the modification order of M. [ Note: This
requirement is known as write-read coherence. — end note ]

SC-PER-LOC:
[ Note: The four preceding coherence requirements effectively disallow compiler reordering of atomic operations
to a single object, even if both operations are relaxed loads. This effectively makes the cache coherence
guarantee provided by most hardware available to C++ atomic operations. — end note ]

[ Note: The value observed by a load of an atomic depends on the “happens before” relation, which depends
on the values observed by loads of atomics. The intended reading is that there must exist an association of
atomic loads with modifications they observe that, together with suitably chosen modification orders and
the “happens before” relation derived as described above, satisfy the resulting constraints as imposed here.
— end note ]



DRF:
[ Note: It can be shown
that programs that correctly use mutexes and memory_order_seq_cst operations to prevent all data races
and use no other synchronization operations behave as if the operations executed by their constituent threads
were simply interleaved, with each value computation of an object being taken from the last side effect on that
object in that interleaving. This is normally referred to as “sequential consistency”. However, this applies only
to data-race-free programs, and data-race-free programs cannot observe most program transformations that
do not change single-threaded program semantics. In fact, most single-threaded program transformations
continue to be allowed, since any program that behaves differently as a result must perform an undefined
operation. — end note ]

Two accesses to the same object of type volatile std::sig_atomic_t do not result in a data race if
both occur in the same thread, even if one or more occurs in a signal handler. For each signal handler
invocation, evaluations performed by the thread invoking a signal handler can be divided into two groups A
and B, such that no evaluations in B happen before evaluations in A, and the evaluations of such volatile
std::sig_atomic_t objects take values as though all evaluations in A happened before the execution of the
signal handler and the execution of the signal handler happened before all evaluations in B.

[ Note: Compiler transformations that introduce assignments to a potentially shared memory location that
would not be modified by the abstract machine are generally precluded by this document, since such an
assignment might overwrite another assignment by a different thread in cases in which an abstract machine
execution would not have encountered a data race. This includes implementations of data member assignment
that overwrite adjacent members in separate memory locations. Reordering of atomic loads in cases in which
the atomics in question may alias is also generally precluded, since this may violate the coherence rules.
— end note ]

[ Note: Transformations that introduce a speculative read of a potentially shared memory location may not
preserve the semantics of the C++ program as defined in this document, since they potentially introduce a
data race. However, they are typically valid in the context of an optimizing compiler that targets a specific
machine with well-defined semantics for data races. They would be invalid for a hypothetical machine that is
not tolerant of races or provides hardware race detection. — end note ]

The enumeration memory_order specifies the detailed regular (non-atomic) memory synchronization order
as defined in 4.7 and may provide for operation ordering. Its enumerated values and their meanings are as
follows :
 — memory_order_relaxed: no operation orders memory.
 — memory_order_release, memory_order_acq_rel, and memory_order_seq_cst : a store operation performs a release operation on the affected memory location.
 — memory_order_consume: a load operation performs a consume operation on the affected memory
location. [ Note: Prefer memory_order_acquire, which provides stronger guarantees than memory_-
order_consume. Implementations have found it infeasible to provide performance better than that of
memory_order_acquire. Specification revisions are under consideration. — end note ]
 — memory_order_acquire, memory_order_acq_rel, and memory_order_seq_cst : a load operation per-
forms an acquire operation on the affected memory location.

[ Note: Atomic operations specifying memory_order_relaxed are relaxed with respect to memory ordering.
Implementations must still guarantee that any given atomic access to a particular atomic object be indivisible
with respect to all other atomic accesses to that object. — end note ]

SW:
An atomic operation A that performs a release operation on an atomic object M synchronizes with an atomic
operation B that performs an acquire operation on M and takes its value from any side effect in the release
sequence headed by A.

SC:
There shall be a single total order S on all memory_order_seq_cst operations, consistent with the “happens
before” order and modification orders for all affected locations, such that each memory_order_seq_cst
operation B that loads a value from an atomic object M observes one of the following values:
 — the result of the last modification A of M that precedes B in S, if it exists, or
 — if A exists, the result of some modification of M that is not memory_order_seq_cst and that does not
happen before A, or
 — if A does not exist, the result of some modification of M that is not memory_order_seq_cst.

[ Note: Although it is not explicitly required that S include locks, it can always be extended to an order
that does include lock and unlock operations, since the ordering between those is already included in the
“happens before” ordering. — end note ]

SC-Fence:
For an atomic operation B that reads the value of an atomic object M, if there is a memory_order_seq_cst
fence X sequenced before B, then B observes either the last memory_order_seq_cst modification of M
preceding X in the total order S or a later modification of M in its modification order.

SC-Fence:
For atomic operations A and B on an atomic object M, where A modifies M and B takes its value, if there is
a memory_order_seq_cst fence X such that A is sequenced before X and B follows X in S, then B observes
either the effects of A or a later modification of M in its modification order.

SC-Fence:
For atomic operations A and B on an atomic object M, where A modifies M and B takes its value, if there are
memory_order_seq_cst fences X and Y such that A is sequenced before X, Y is sequenced before B, and X
precedes Y in S, then B observes either the effects of A or a later modification of M in its modification order.

Fence:
For atomic modifications A and B of an atomic object M, B occurs later than A in the modification order of
M if:
 — there is a memory_order_seq_cst fence X such that A is sequenced before X, and X precedes B in S, or
 — there is a memory_order_seq_cst fence Y such that Y is sequenced before B, and A precedes Y in S, or
 — there are memory_order_seq_cst fences X and Y such that A is sequenced before X, Y is sequenced
before B, and X precedes Y in S.

[ Note: memory_order_seq_cst ensures sequential consistency only for a program that is free of data races
and uses exclusively memory_order_seq_cst operations. Any use of weaker ordering will invalidate this
guarantee unless extreme care is used. In particular, memory_order_seq_cst fences ensure a total order only
for the fences themselves. Fences cannot, in general, be used to restore sequential consistency for atomic
operations with weaker ordering specifications. — end note ]

OOTA:
Implementations should ensure that no “out-of-thin-air” values are computed that circularly depend on their
own computation.
[ Note: For example, with x and y initially zero,

// Thread 1 :
r1 = y.load(memory_order_relaxed);
x.store(r1, memory_order_relaxed);
// Thread 2:
r2 = x.load(memory_order_relaxed);
y.store(r2, memory_order_relaxed);

should not produce r1 == r2 == 42, since the store of 42 to y is only possible if the store to x stores 42,
which circularly depends on the store to y storing 42. Note that without this restriction, such an execution is
possible. — end note ]

[ Note: The recommendation similarly disallows r1 == r2 == 42 in the following example, with x and y
again initially zero:

// Thread 1 :
r1 = x.load(memory_order_relaxed);
if (r1 == 42) y.store(42, memory_order_relaxed);
// Thread 2:
r2 = y.load(memory_order_relaxed);
if (r2 == 42) x.store(42, memory_order_relaxed);
— end note ]

RMW-ATOMIC:
Atomic read-modify-write operations shall always read the last value (in the modification order) written
before the write associated with the read-modify-write operation.

Implementations should make atomic stores visible to atomic loads within a reasonable amount of time.

template <class T>
T kill_dependency( T y) noexcept ;
Effects: The argument does not carry a dependency to the return value (4. 7) .
Returns: y.
*)