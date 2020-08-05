Require Import hahn.Hahn.
Require Import List.

Section Definitions.
  Variable B: Type.
  Variable R: relation B.
  Variable order_R: order _ R.

  Section Subsets.
    Variable S: B -> Prop.

    Section BaseSubset.
      Variable BS: B -> Prop.

      (*
      Definition 1.2: [Upper bounds, Lower bounds, Consistency] Let S be a subset of a partial
      order B. An element b ∈ B is an upper bound of S iff ∀s ∈ S s <= b. An element b ∈ B is a lower
      bound of S iff ∀s ∈ S b <= s. S is consistent (sometimes called bounded) iff S has an upper bound.
      An upper bound b of S is the least upper bound of S (denoted ⋂S) iff b approximates all upper
      bounds of S. A lower bound b of S is the greatest lower bound of S (denoted ⋃S) iff every lower
      bound of S approximates b.
      Remark 1.3: Upper bounds are much more important in domain theory than lower bounds.
      *)
      Definition ub b := BS b /\ forall s, S s -> R s b.
      Definition lb b := BS b /\ forall s, S s -> R b s.

      Definition consistent := exists b, ub b.

      Definition lub b := ub b /\ forall b', BS b' -> ub b' -> R b b'.
      Definition glb b := lb b /\ forall b', BS b' -> lb b' -> R b' b.
    End BaseSubset.
    
    (*
    Definition 1.4: [Directed Subset] A subset S of a partial order B is directed iff every finite
    subset of S has an upper bound in S. A directed subset of B is progressive iff it does not contain
    a maximum element. A directed subset of B is a chain iff it is totally ordered: ∀a, b ∈ Ba v b or
    b v a.
    *)

    Definition directed :=
      ~S ⊆₁ ∅ ->
      forall (S': B -> Prop),
            S' ⊆₁ S ->
            set_finite S' ->
            exists s, S s /\ forall s', S' s' -> R s' s.
    Definition progressive := directed /\ forall e, S e -> exists e', ~R e' e.
    Definition chain := is_total S R.

    Lemma chain_is_directed: chain -> directed.
    Proof.
      intros ch Snemp S' S'inc [S'list HS'list].
      destruct order_R.
      cut (exists s, S s /\ forall s', S' s' -> In s' S'list -> R s' s).
      intros (e & Se & eub).
      exists e; split; auto.
      clear HS'list.
      induction S'list.
      simpl.
      apply NNPP.
      intros nex.
      contradict Snemp.
      intros s Ss.
      apply nex.
      exists s.
      split; auto.
      intros s' Ss' f; contradiction.
      destruct IHS'list as (pm & Spm & pmub).
      destruct (classic (a = pm)).
      subst a.
      exists pm; split; auto.
      intros s' Ss' [s'pm|s'in].
      subst s'; auto.
      auto.
      destruct (classic (S' a)) as [S'a|].
      destruct (ch pm Spm a); auto.
      exists a; split; auto.
      intros s' Ss' [s'pm|s'in].
      subst s'; auto.
      eapply ord_trans; eauto.
      exists pm; split; auto.
      intros s' Ss' [s'pm|s'in].
      subst s'; auto.
      auto.
      exists pm; split; auto.
      intros s' Ss' [s'pm|s'in].
      subst s'; contradiction.
      auto.
    Qed.
    
    (* Claim 1.5: The empty set ∅ is directed. *)

    Lemma empty_set_directed: S ⊆₁ ∅ -> directed.
    Proof.
      intros Semp nSemp; contradiction.
    Qed.
  End Subsets.

  (*
  Definition 1.6: [Complete Partial Order] A complete partial order, abbreviated cpo, is a
  partial order (B, <=) such that every directed subset has a least upper bound in B.
  *)

  Definition cpo := forall S, directed S -> exists b, lub S set_full b.

  (* Claim 1.7: A cpo has a least element. *)

  Lemma cpo_least: cpo -> exists m, forall e, R m e.
  Proof.
    intros cpo'.
    unfold cpo in cpo'.
    specialize (cpo' ∅) as cnull.
    destruct cnull as [m [mub mmin]].
    apply empty_set_directed; auto.
    exists m; intros e.
    apply mmin.
    constructor.
    split.
    constructor.
    intros s c; contradiction.
  Qed.

  (*
  Definition 1.8: [Finitary Basis] A finitary basis B is a partial order (B, <=) such that B is
  countable and every finite consistent subset S ⊆ B has a least upper bound in B.

  In a fin_basis, all finite consistent subsets have least upper bounds (and its countable)
   - countable means the increasing resolution of approximation doesn't get stuck in an asymptote
     i.e. running it for long enough will get to any chosen level of approximation
   - the lub means that any finite amount of computation can be represented by a minimal approximation
     i.e. one that adds no new information, one that if you were to remove information would remove
     completed computation.
  In a cpo, all subsets for which all finite subsets are consistent have least upper bounds.
   - if the cpo is countable, is it a fin_basis?
     - If a finite consistent subset has a maximum, then all its subsets are consistent
       with it (it's directed) and it has a lub
     - Otherwise, at least one upper bound exists, and each union of the subset with an upper
       bound is directed and has a lub, but is one of these least?
   - is a fin_basis a cpo?
     - if a subset with consistent finite subsets is finite, then it is itself consistent, and
       will have a least upper bound
     - otherwise (countably infinite directed subsets), no
  *)

  Definition fin_basis :=
    exists f: B -> nat, forall b b', f b = f b' -> b = b' /\
    forall S, set_finite S ->
              consistent S set_full ->
              exists b, lub S set_full b.

  (*
  Definition 1.11: [Ideal] For finitary basis B, a subset I of B is an ideal over B iff
  • I is downward closed: e ∈ I ⇒ (∀b ∈ B,  b <= e ⇒ b ∈ I)
  • I is closed under least upper bounds on finite subsets (conjunction).
  *)

  Definition ideal (S: B -> Prop) :=
    (forall e, S e -> forall b, R b e -> S b) /\
    (forall S', S' ⊆₁ S ->
                set_finite S' ->
                forall b, lub S' set_full b -> S b).

  (*
  Definition 1.12: [Constructed Domain] Let B be a finitary basis. The domain DB determined
  by B is the partial order D, <= where D is the set of all ideals I over B and <= is the subset
  relation. We will frequently write D instead of DB.
  *)

  Definition construct_domain := ⋃₁ i ∈ ideal, fun x => x ≡₁ i.
End Definitions.

Section Definitions.
  Variable B: Set.
  Variable R: relation B.
  Variable B_fin_basis: fin_basis B R.
  Variable order_R: order _ R.
  Let D := construct_domain B R.

  (*
  Claim 1.13: The least upper bound of two ideals I1 and I2, if it exists, is found by closing
              I1 ∪ I2 to form an ideal over B.
  *)
  Lemma lub_ideals:
    forall i1 i2 i12,
      D i1 ->
      D i2 ->
      lub _ set_subset (fun s => s ≡₁ i1 \/ s ≡₁ i2) D i12 ->
      i12 ≡₁
        i1 ∪₁ i2 ∪₁
        ⋃₁ s ∈ (fun s => s ⊆₁ (i1 ∪₁ i2) /\ set_finite s),
           dom_rel (R ⨾ ⦗lub _ R s set_full⦘).
  Proof.
    pose (cons_eps := IndefiniteDescription.constructive_indefinite_description).
    destruct order_R.
    intros i1 i2 i12
           (Di1 & [i1down i1up] & i1Di1 & Di1i1)
           (Di2 & [i2down i2up] & i2Di2 & Di2i2) [[Di12 i1i2] i12min].
    match goal with |- _ ≡₁ ?G => pose (i12p := G) end.
    assert (ideal _ R i12p).
      red.
      split.
      intros e [[i1'|i2']|(se & [sei12 sefin] & b & b' & reb & -> & [_ ubb] & bmin)] bs rbse.
      left; red; left; apply Di1i1; apply i1down with e; auto.
      left; red; right; apply Di2i2; apply i2down with e; auto.
      right; exists se; repeat split; auto.
      exists b; repeat esplit; eauto.
      intros S' S'i12 S'fin b lubb.
      pose (S'i := S' ∩₁ (i1 ∪₁ i2)).
      pose (S'lub := S' ∩₁ set_compl (i1 ∪₁ i2)).
      assert (S'eq: S' ≡₁ S'i ∪₁ S'lub).
        compute; intuition.
        pose (classic (i1 x \/ i2 x)); intuition.
      assert (HS'lub: S'lub ⊆₁
                ⋃₁s ∈ fun s : B -> Prop => s ⊆₁ i1 ∪₁ i2 /\ set_finite s,
                  dom_rel (R ⨾ ⦗lub B R s set_full⦘)).
        intros s [slubs ni12]; destruct S'i12 with s; auto.
        contradiction.
      pose (S'lubsigs := fun x (hx: S'lub x) => cons_eps _ _ (HS'lub x hx)).
      pose (S'lubset := S'i ∪₁ fun x => exists e (he: S'lub e), proj1_sig (S'lubsigs e he) x).
      right; exists S'lubset; repeat split.
      intros x [sx12|(e' & he' & s'x)].
      apply sx12.
      destruct (proj2_sig (S'lubsigs e' he')) as ([s'12 s'fin] & b' & xb).
      auto.
      apply set_finite_union; split.
      assert (SiS: S'i ⊆₁ S').
        intros x [s'ix]; auto.
      rewrite SiS; auto.
      assert (S'lubfin: set_finite S'lub).
        assert (SlubS: S'lub ⊆₁ S').
          intros x [s'ix]; auto.
        rewrite SlubS; auto.
      destruct S'lubfin as [lS'lub inlS'lub].
      pose (lS'lubset := flat_map (fun e =>
        match excluded_middle_informative (S'lub e)
        with
          left he =>
            match proj2_sig (S'lubsigs e he)
            with
              conj (conj _ efin) _ =>
                match cons_eps _ _ efin
                with
                  exist _ l _ => l
                end
            end
        | right nhe => nil
        end) lS'lub).
      exists lS'lubset.
      intros x (e & he & se).
      specialize (inlS'lub e he).
      subst lS'lubset.
      induction lS'lub.
      contradiction.
      simpl.
      apply in_or_app.
      destruct inlS'lub.
      subst a.
      left.
      destruct (excluded_middle_informative (S'lub e)) as [he'|nhe].
      assert (he = he') by apply proof_irrelevance; subst he'.
      destruct (proj2_sig (S'lubsigs e he)) as ([se12 sefin] & _).
      destruct (cons_eps _ _ sefin).
      auto.
      contradiction.
      right; auto.

      unfold lS'lubset; cbn.
      simpl in s'x12.

      intuition.
      right. exists S'.

    split.
    apply i12min.
    red; red; red.
    eexists.
    split.
    2: {
      split.
      intros foo bar; eauto.
      auto.
    }
    red.
    split.
    red.
    intros e [[i1'|i2']|(se & [sei12 sefin] & b & b' & reb & -> & [_ ubb] & bmin)] bs rbse.
    left; red; left; apply Di1i1; apply i1down with e; auto.
    left; red; right; apply Di2i2; apply i2down with e; auto.
    right; exists se; repeat split; auto.
    exists b; repeat esplit; eauto.
    intros S' S'i12 S'fin b lubb.
    apply S'i12; .

  Qed.

  (*
  Claim 1.14: The domain D determined by a finitary basis B is a complete partial order.
  *)