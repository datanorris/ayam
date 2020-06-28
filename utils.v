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