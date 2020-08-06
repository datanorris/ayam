Require Import hahn.Hahn.
Require Import List.
Require Import Program.
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
    inhabited B /\ (* seems to be required, cant have empty ideals, cant have empty domains *)
    (exists f: B -> nat, forall b b', f b = f b' -> b = b') /\
    forall S, set_finite S ->
              consistent S set_full ->
              exists b, lub S set_full b.

  (*
  Definition 1.11: [Ideal] For finitary basis B, a subset I of B is an ideal over B iff
  - I is downward closed: e ∈ I ⇒ (∀b ∈ B,  b <= e ⇒ b ∈ I)
  - I is closed under least upper bounds on finite subsets (conjunction).

  The conjunction closure means the conjunction must exist else it's not a valid ideal
  *)

  Definition ideal (B_fin_basis: fin_basis) (S: B -> Prop) :=
    (forall e, S e -> forall b, R b e -> S b) /\
    (forall S', S' ⊆₁ S ->
                set_finite S' ->
                exists b, lub S' set_full b /\ S b).
  
  Lemma ideal_nonempty: forall B_fin_basis S, ideal B_fin_basis S -> ~S ⊆₁ ∅.
  Proof.
    intros (_ & Bcount & Bfinlubs) S [Sdown Sjoin].
    intros Semp.
    destruct (Sjoin S) as (b & blub & Sb); auto.
    exists nil.
    intros x Sx; apply Semp in Sx; contradiction.
    apply Semp in Sb; contradiction.
  Qed.

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
   - any finite inconsistent subset of B has no least upper bound, so it cannot generate an ideal
   - any directed infinite subset of B has the property that all finite subsets are consistent. They
     will have lubs which, introduced into the ideal, must in turn have lubs pairwise with all other
     elements in the ideal.
     - Introduced lubs must be less than some other element in the ideal, or greater than all other
       elements in the ideal (a maximum). The ideal remains directed.
     - If the ideal has a maximum, then the finite subset lubs must be <= this maximum, so a downward
       closure on the maximum is sufficient to generate the ideal
     - If the ideal has no maximum, it's a progressive directed set. It may have upper bounds in B
       (and maybe a least one) which can generate a superset of the ideal by downward closure.
   - any undirected infinite subset of B will have a finite subset inconsistent with respect to the
     undirected subset, and therefore cannot generate an ideal unless the infinite subset can be closed
     to become directed.
   - for directed subsets of B
     - if they are infinite with a maximum, or finite (in which case they have a maximum), then their
       ideal is the downward closure of the maximum - this produces an isomorphic directed subset in D
       (a principal ideal).
     - if they have no maximum (progressive), then because all finite subsets are consistent with
       the directed subset, their lubs (in B) must be <= some ub in the directed subset. a downward closure
       on all elements in the directed set is sufficient to produce its ideal. This is equivalent
       to the union of the principal ideals corresponding to each element in the directed set
   - for directed subsets of D
     - an ideal is a principal ideal or a fully closed progressive directed subset of B (union of
       principal ideals of a progressive directed subset of B)
     - if any two ideals have a lub, then the closure over their union is an ideal and indeed their
       lub in D.
     - in directed sets of ideals, all their finite subsets have upper bounds, and therefore can be
       closed to be made ideal-consistent. Therefore the union of the set is a valid ideal, and is
       the lub.
  *)

  Definition construct_domain := ideal.
End Definitions.

Section Definitions.
  Variable B: Set.
  Variable R: relation B.
  Variable B_fin_basis: fin_basis B R.
  Variable order_R: order _ R.
  Let D := construct_domain B R B_fin_basis.

  (*
  Claim 1.13: The least upper bound of two ideals I1 and I2, if it exists, is found by closing
              I1 ∪ I2 to form an ideal over B.
  *)

  Inductive clos_ideal (S: B -> Prop): B -> Prop :=
    ideal_base x: S x -> clos_ideal S x
  | ideal_prev x y: clos_ideal S y -> R x y -> clos_ideal S x
  | ideal_join s b: s ⊆₁ clos_ideal S -> set_finite s -> lub _ R s set_full b -> clos_ideal S b.

  Lemma lub_ideals:
    forall si ilub,
      lub _ set_subset si D ilub ->
      ilub ≡₁ clos_ideal (⋃₁ i ∈ si, i).
  Proof.
    intros si ilub [[ilubD ilubub] ilubmin].
    destruct (ilubD) as [ilub'_down ilub'_join].
    match goal with |- _ ≡₁ ?G => set (sic := G) end.
    assert (sic_ilub: sic ⊆₁ ilub).
      intros x sicx.
      induction sicx as [x (s & sis & sx)|b e sice IHsice rbe|S' b S'sic S'ilub S'fin blub].
      eapply ilubub; eauto.
      eapply ilub'_down; eauto.
      edestruct ilub'_join as (x & xlub & ilub'x).
      2: eauto.
      intros x sx.
      auto.
      assert (bx: b = x).
        destruct blub as [ubb bmin], xlub as [ubx xmin].
        cut (R b x).
        cut (R x b).
        intros rxb rbx.
        destruct order_R.
        apply ord_antisym; auto.
        apply xmin; auto; constructor.
        apply bmin; auto; constructor.
      subst x.
      auto.
    assert (ideal_sic: D sic).
      repeat split.
      intros e sice b rbe.
      econstructor 2; eauto.
      intros S' S'sic S'fin.
      destruct (ilub'_join S') as (x & lubx & ilubx).
      eapply set_subset_trans; [eapply set_subset_trans|]; eauto.
      auto.
      exists x; split; auto.
      econstructor 3; eauto.
    split; auto.
    apply ilubmin.
    auto.
    split.
    auto.
    intros s sis x sx.
    constructor 1; exists s; auto.
  Qed.

  (*
  Claim 1.14: The domain D determined by a finitary basis B is a complete partial order.
   - Prove any directed subset has a lub
   - The lub will be the union of the directed subset's sets
     - it will be an ideal
     - it will be least under ⊆
   - It's an ideal because
     - it will be downward closed because each point in the union is from an ideal and
       already downward closed
     - it will be fixed-subset lub closed because any finite set of points from
       any (necessarily finite) set of sets in the union will have a least upper bound by
       their inclusion in the upper bound of the sets, by definition of ideal,
       which exists in the union by guarantee of the directed set
  *)

  Lemma d_cpo: cpo {s: B -> Prop | D s} ((@proj1_sig _ _) ↓ set_subset).
  Proof.
    destruct order_R.
    pose (cons_eps := IndefiniteDescription.constructive_indefinite_description).
    intros S Sdir.
    pose (BFB := B_fin_basis); destruct BFB as ([Bone] & Bcountable & Bleast & Bleastmin').
    instantiate (1 := ∅).
    exists nil; intros x contra; contradiction.
    exists Bone; split.
    constructor.
    intros x contra; contradiction.
    clear Bone.
    assert (Bleastmin: forall b, R Bleast b).
      intros b.
      destruct Bleastmin' as [[_ ?] bmin].
      apply bmin; hnf; repeat split; auto.
      intros s contra; contradiction.
    clear Bleastmin'.
    assert (DBleast: D (eq Bleast)).
      split.
      intros e <- b rbb.
      eapply ord_antisym; eauto.
      intros S' S'Bleast S'fin.
      exists Bleast; repeat split.
      intros s S's.
      apply S'Bleast in S's.
      subst s.
      apply ord_refl.
      intros b' _ ubb'.
      auto.
    destruct (classic (S ⊆₁ ∅)) as [Semp|Sinhab].
    exists (exist _ (eq Bleast) DBleast).
    repeat split.
    intros s Ss; apply Semp in Ss; contradiction.
    intros [b' Db'] _ [_ ubb'].
    destruct (Db') as [Db'down Db'join].
    intros x <-; simpl.
    eapply Db'down.
    apply ideal_nonempty in Db'.
    assert (b: exists b, b' b).
      apply NNPP; intros nex; apply Db'.
      intros b bb'.
      apply nex.
      exists b; auto.
    destruct b as [b bb]; eauto.
    auto.
    assert (s: exists s, S s).
      apply NNPP; intros nex; apply Sinhab.
      intros s Ss.
      apply nex.
      exists s; auto.
    destruct s as [[Sone DSone] SSone].
    assert (s: exists s, Sone s).
      apply NNPP; intros nex; eapply ideal_nonempty.
      apply DSone.
      intros s Ss.
      apply nex.
      exists s; auto.
    destruct s as [Sone' SSone'].
    pose (S' := fun (s: B -> Prop) => exists ds: D s, S (exist _ s ds)).
    set (S'_clos := ⋃₁ i ∈ S', i).
    assert (DS'_clos: D S'_clos).
      repeat split.
      intros e (s' & [Ds' Ss'] & s'e) b rbe.
      exists s'.
      repeat esplit; eauto.
      destruct Ds' as [s'down s'join].
      eapply s'down; eauto.
      intros S'' S''sic [S''list inS''list].
      destruct (classic (S'' ⊆₁ ∅)) as [S''null|S''inhab].
      exists Bleast.
      repeat esplit; hnf; auto.
      intros s Ss.
      exfalso; eapply S''null; eauto.
      eauto.
      destruct DSone as [DSonedown DSonejoin].
      eapply DSonedown; eauto.
      unshelve evar (SS''list: list (B -> Prop)).
        refine (flat_map (fun x =>
          match excluded_middle_informative (S'' x)
          with
            left sx => ` (cons_eps _ _ (S''sic x sx)) :: nil
          | right _ => nil
          end) S''list).
      assert (S''x_to_set: forall x, S'' x -> exists s, s x /\ In s SS''list).
        intros x S''x.
        pose (S''x' := S''x); apply inS''list in S''x'.
        clear inS''list; subst SS''list.
        induction S''list.
        contradiction.
        destruct S''x' as [->|inS''list].
        destruct (cons_eps _ _ (S''sic x S''x)) as (s & S's & sx) eqn:seq.
        exists s.
        split; simpl; auto.
        apply in_app_l.
        destruct (excluded_middle_informative (S'' x)) as [S''x2|nS''x]; simpl.
        assert (S''x = S''x2) by apply proof_irrelevance; subst.
        rewrite seq; left; auto.
        contradiction.
        destruct IHS''list as (s & sx & sin); auto.
        exists s; split; auto.
        simpl; apply in_app_r; auto.
      assert (SS''list_S': (flip (@In _)) SS''list ⊆₁ S').
        intros s inSS''.
        clear inS''list S''x_to_set.
        induction S''list.
        simpl in SS''list; destruct inSS''.
        apply in_app_or in inSS''; destruct inSS'' as [sina|sinS''list].
        clear IHS''list.
        destruct (excluded_middle_informative (S'' a)) as [S''a|nS''a].
        destruct sina; try contradiction.
        subst s.
        match goal with |- S' (` ?G) => pose (s_cond := proj2_sig G) end.
        destruct s_cond as [[Ds Ss] Sa].
        exists Ds; auto.
        contradiction.
        apply IHS''list; auto.
      assert (SS''list_S: (@proj1_sig _ _) ↓₁ (flip (@In _)) SS''list ⊆₁ S).
        intros [s Ds] SS''list_s.
        hnf in SS''list_s; simpl in SS''list_s.
        apply SS''list_S' in SS''list_s as [Ds' Ss].
        assert (Ds = Ds') by apply proof_irrelevance; subst; auto.
      apply Sdir in SS''list_S; auto.
      destruct SS''list_S as [[SS''ub [SS''ubdown SS''ubjoin]] [S_S''ub SS''ubub]].
      eexists (flat_map (fun s =>
        match excluded_middle_informative (D s)
        with
          left ds => exist _ s ds :: nil
        | right _ => nil
        end) SS''list).
      intros [x dx] SS''x.
      hnf in SS''x; simpl in SS''x.
      clear SS''list_S' S''x_to_set.
      induction SS''list; auto.
      simpl.
      destruct SS''x.
      subst a.
      apply in_app_l.
      destruct (excluded_middle_informative (D x)).
      assert (d = dx) by apply proof_irrelevance; subst; simpl; auto.
      contradiction.
      apply in_app_r; auto.
      destruct (SS''ubjoin S'') as (b & blub & SS''ubb).
      intros x S''x.
      destruct (S''x_to_set x) as (s & sx & sSS''list); auto.
      destruct (SS''list_S' s) as [Ds Ss]; auto.
      specialize (SS''ubub (exist _ s Ds)).
      unfold set_map, map_rel, flip in SS''ubub; simpl in SS''ubub.
      apply SS''ubub; auto.
      exists S''list; auto.
      exists b; split; auto.
      exists SS''ub; split; auto.
      exists (conj SS''ubdown SS''ubjoin); auto.
    exists (exist _ S'_clos DS'_clos).
    repeat split.
    intros [s Ds] Ss x sx.
    simpl in *.
    exists s; split; auto.
    exists Ds; auto.
    intros [s Ds] _ [_ sub].
    unfold map_rel in sub |- *; simpl in *.
    intros s' (s'' & [Ds'' Ss''] & s''s').
    eapply sub; eauto.
  Qed.
End Definitions.