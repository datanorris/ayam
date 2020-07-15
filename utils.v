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