Require Import hahn.Hahn.
Require Import List.
Require Import Program.Basics.
Open Scope program_scope.

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

   - Any single element b of B that is downnward closed to produce a tree is isomorphic to a tree in D
     - the downward closure of b is an ideal in D - since b is the maximum, it's the lub, and any lub
       found for a finite subset must be already in the closure - it must be <= b, since b is also an
       upper bound of the subset
     - the downward closure of any b' <= b is ⊆ the downward closure for b
     - note these trees can be infinite e.g. downward closing from infinity
   - any finite consistent subset of B has a least upper bound b, and its ideal is the downward closure
     of b
   - any finite inconsistent subset of B is the union of some set of finite consistent subsets which
     are pairwise inconsistent. The ideal for these subsets is the union of the ideals for the
     composing consistent subsets
     - this provides a lub in D where there wasn't one before
   - any infinite consistent subset of B has the property that all finite subsets are consistent. They
     will have a lub but it is not necessarily related to the upper bounds of the infinte subset.
     - If the infinite subset has no lub, a full recursive downnward and finite-lub closure is
       required here.
     - If the infinite subset has a maximum, then the finite subset lubs must be <= this maximum
       so a downward closure on the maximum is sufficient
     - If the infinite subset has a lub but no maximum, the full recursive closure is required and
       will not include this lub.
   - any infinite inconsistent subset of B will be the union of some finite and infinte consistent
     subsets. Their ideals must be full closed as new finite subset lubs may be added.
   - we concern ourselves with directed subsets of B
     - if they are infinite with a maximum, or finite (in which case they have a maximum), then their
       ideal is the downward closure of the maximum - this produces an isomorphic directed subset in D.
     - if they have no maximum (progressive), then because all finite subsets are consistent with
       the directed subset, their lubs must be <= some ub in the directed subset. a downward closure
       on all elements in the directed set is sufficient to produce its ideal. This is equivalent
       to the union of the ideals corresponding to each element in the directed set
   - for directed subsets of D
     - an ideal is the union of inconsistent finite & infinite operations:
       - any finite-size ideal is a union of principal ideals that are inconsistent
       - any infinite-size ideal is a union of principal ideals and progressive directed subsets of B
         that are inconsistent
     - any two ideals can be unioned and closed to find an ideal that is least upper bound to them
       (there can be no smaller ideal that includes both base ideals)
     - all sets of ideals have a lub
     - all sets of ideals closed on finite-set lubs are directed sets
     - the ideal i = B is the maximum of D
  *)

  Definition construct_domain := ⋃₁ i ∈ ideal, set_equiv i.
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

  Inductive clos_ideal (S: B -> Prop): B -> Prop :=
    ideal_base x: S x -> clos_ideal S x
  | ideal_prev x y: clos_ideal S y -> R x y -> clos_ideal S x
  | ideal_join s b: s ⊆₁ clos_ideal S -> set_finite s -> lub _ R s set_full b -> clos_ideal S b.

  Lemma ideal_clos_ideal: forall S, ideal _ R (clos_ideal S).
  Proof.
    intros S.
    split.
    intros e Se b Rbe.
    econstructor 2; eauto.
    intros S' S'S S'fin b lubb.
    econstructor 3; eauto.
  Qed.

  Lemma lub_ideals:
    forall si,
      lub _ set_subset si D (clos_ideal (⋃₁ i ∈ si, i)).
  Proof.
    intros si.
    repeat split.
    exists (clos_ideal (⋃₁ i ∈ si, i)); split.
    apply ideal_clos_ideal.
    auto.
    intros s sis x sx.
    constructor 1; exists s; auto.
    intros b' (b'' & [b''clos_down b''clos_join] & beq) [_ ubb'] x i12closx.
    induction i12closx as [x [s [sis sx]]|?|].
    eapply ubb'; eauto.
    apply beq; eapply b''clos_down; [apply beq|]; eauto.
    apply beq; eapply b''clos_join.
    2, 3: eauto.
    intros x sx; apply beq; auto.
  Qed.

  (*
  Claim 1.14: The domain D determined by a finitary basis B is a complete partial order.
  *)

  Lemma d_cpo: cpo {s: B -> Prop | D s} ((@proj1_sig _ _) ↓ set_subset).
  Proof.
    intros S Sdir.
    pose (S' := fun (s: B -> Prop) => exists ds: D s, S (exist _ s ds)).
    destruct (lub_ideals S') as [[DS'_clos S'_clos_ub] S'_clos_min].
    set (S'_clos := clos_ideal (⋃₁ i ∈ S', i)) in *.
    exists (exist _ S'_clos DS'_clos).
    repeat split.
    intros [s Ds] Ss x sx; simpl in *.
    eapply S'_clos_ub; try esplit; eauto.
    intros [b' Db'] _ [_ ubb] x bx; simpl in *.
    eapply S'_clos_min; eauto.
    split; auto.
    intros s [Ds Ss] x' sx'.
    specialize (ubb (exist _ s Ds)); unfold map_rel in ubb; simpl in *.
    apply ubb; auto.
  Qed.
End Definitions.