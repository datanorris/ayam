Require Import hahn.Hahn.
Require Import List.
Require Import Program.
Require Import PropExtensionality.
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

   - Any single element b of B that is downward closed to produce a tree is isomorphic to a tree in D
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
  Variable B: Type.
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

  Lemma fin_basis_least: exists b, lb _ R set_full set_full b.
  Proof.
    pose (BFB := B_fin_basis); destruct BFB as ([Bone] & Bcountable & Bleast & Bleastmin').
    instantiate (1 := ∅).
    exists nil; intros x contra; contradiction.
    exists Bone; split.
    constructor.
    intros x contra; contradiction.
    clear Bone.
    exists Bleast.
    repeat split.
    intros b _.
    destruct Bleastmin' as [[_ ?] bmin].
    apply bmin; hnf; repeat split; auto.
    intros s' contra; contradiction.
  Qed.

  Lemma constructed_domain_least:
    let cons_eps := IndefiniteDescription.constructive_indefinite_description in
    let Bleast := cons_eps _ _ fin_basis_least in
    let Dleast := (eq (`Bleast)) in
    D Dleast /\ lb _ set_subset D set_full Dleast.
  Proof.
    intros.
    destruct order_R.
    destruct Bleast as [b [foo blb]]; simpl in *.
    repeat split; auto.
    intros e <- b' rbb.
    eapply ord_antisym; eauto.
    intros s sdleast _.
    exists b; repeat split; auto.
    intros b' sb'.
    apply sdleast in sb'; compute in sb'; subst; auto.
    intros s Ds b' <-.
    apply NNPP.
    intros contra.
    apply (ideal_nonempty _ R B_fin_basis s); auto.
    intros s' ss'; apply contra.
    destruct Ds as [dsdown _].
    eapply dsdown; eauto.
  Qed.

  Lemma directed_set_lub: forall (s: _ -> Prop) sone,
    s sone ->
    directed {x: B -> Prop | D x} (@proj1_sig _ _ ↓ set_subset) s ->
    let s_union := (⋃₁i ∈ s, `i) in
    exists ds: D s_union, lub _ (@proj1_sig _ _ ↓ set_subset) s set_full (exist _ s_union ds).
  Proof.
    pose (cons_eps := IndefiniteDescription.constructive_indefinite_description).
    destruct order_R.
    intros s [sone Dsone] ssone ds s_union.
    destruct Dsone as [DSonedown DSonejoin].
    destruct constructed_domain_least as [DDleast [_ bDleast]].
    fold cons_eps in DDleast, bDleast.
    destruct (cons_eps _ _ fin_basis_least) as [Bleast [foo bBleast]]; simpl in *.
    clear foo.
    lapply ds; clear ds.
    intros ds.
    assert (DSunion: D s_union).
      repeat split.
      intros e ([s' Ds'] & Ss' & s'e) b rbe.
      exists (exist _ s' Ds').
      repeat esplit; simpl in *; eauto.
      destruct Ds' as [s'down s'join].
      eapply s'down; eauto.
      intros S'' S''sic [S''list inS''list].
      destruct (classic (S'' ⊆₁ ∅)) as [S''null|S''inhab].
      exists Bleast.
      repeat esplit; eauto.
      intros s' Ss'.
      exfalso; eapply S''null; eauto.
      simpl; apply bDleast; split; auto.
      unshelve evar (SS''list: list (B -> Prop)).
        refine (flat_map (fun x =>
          match excluded_middle_informative (S'' x)
          with
            left sx => (`` (cons_eps _ _ (S''sic x sx))) :: nil
          | right _ => nil
          end) S''list).
      assert (S''x_to_set: forall x, S'' x -> exists s, s x /\ D s /\ In s SS''list).
        intros x S''x.
        pose (S''x' := S''x); apply inS''list in S''x'.
        clear inS''list; subst SS''list.
        induction S''list.
        contradiction.
        destruct S''x' as [->|inS''list].
        destruct (cons_eps _ _ (S''sic x S''x)) as ([s' Ds'] & S's & sx) eqn:seq.
        exists (s').
        split; [|split]; simpl in *; auto.
        apply in_app_l.
        destruct (excluded_middle_informative (S'' x)) as [S''x2|nS''x]; simpl.
        assert (S''x = S''x2) by apply proof_irrelevance; subst.
        rewrite seq; left; auto.
        contradiction.
        destruct IHS''list as (s' & sx & dx & sin); auto.
        exists s'; split; [|split]; auto.
        simpl; apply in_app_r; auto.
      assert (SS''list_S: (@proj1_sig _ _) ↓₁ (flip (@In _)) SS''list ⊆₁ s).
        intros [s' Ds'] SS''list_s'.
        hnf in SS''list_s'; simpl in SS''list_s'.
        clear inS''list S''x_to_set.
        induction S''list.
        simpl in SS''list; destruct SS''list_s'.
        apply in_app_or in SS''list_s'; destruct SS''list_s' as [sina|sinS''list].
        clear IHS''list.
        destruct (excluded_middle_informative (S'' a)) as [S''a|nS''a].
        destruct sina; try contradiction.
        subst s'.
        match goal with |- s (exist _ (` ` ?G) _) => pose (val := G) end.
        destruct (proj2_sig val) as [Ss Sa].
        fold val.
        assert (H: forall A P (e1 e2: {x: A | P x}), `e1 = `e2 -> e1 = e2).
          intros A P [] [].
          simpl; intros <-.
          f_equal.
          apply proof_irrelevance.
        rewrite H with (e2 := `val); auto.
        contradiction.
        apply IHS''list; auto.
      pose (ls := SS''list_S).
      apply ds in ls as [[SS''ub [SS''ubdown SS''ubjoin]] [S_S''ub SS''ubub]].
      destruct (SS''ubjoin S'') as (b & blub & SS''ubb).
      intros x S''x.
      destruct (S''x_to_set x) as (s' & sx & ds' & sSS''list); auto.
      specialize (SS''ubub (exist _ s' ds')).
      unfold set_map, map_rel, flip in SS''ubub; simpl in SS''ubub.
      apply SS''ubub; auto.
      exists S''list; auto.
      exists b; split; auto.
      unshelve eexists (exist _ SS''ub _); split; auto.
      eexists (flat_map (fun s =>
        match excluded_middle_informative (D s)
        with
          left ds => exist _ s ds :: nil
        | right _ => nil
        end) SS''list).
      intros [x dx] SS''x.
      hnf in SS''x; simpl in SS''x.
      clear S''x_to_set ls SS''list_S.
      induction SS''list; auto.
      simpl.
      destruct SS''x.
      subst a.
      apply in_app_l.
      destruct (excluded_middle_informative (D x)).
      assert (d = dx) by apply proof_irrelevance; subst; simpl; auto.
      contradiction.
      apply in_app_r; auto.
    exists DSunion.
    repeat split.
    intros s' Ss x sx.
    simpl in *.
    exists s'; split; auto.
    intros s' _ [_ sub].
    unfold map_rel in sub |- *; simpl in *.
    intros b (bs & sbs & bsb).
    eapply sub; eauto.
    auto.
    intros []; eauto.
  Qed.

  Lemma d_cpo: cpo {s: B -> Prop | D s} ((@proj1_sig _ _) ↓ set_subset).
  Proof.
    pose (cons_eps := IndefiniteDescription.constructive_indefinite_description).
    destruct order_R.
    intros S Sdir.
    destruct constructed_domain_least as [DDleast [_ bDleast]].
    fold cons_eps in DDleast, bDleast.
    destruct (cons_eps _ _ fin_basis_least) as [Bleast [foo bBleast]]; simpl in *.
    clear foo.
    destruct (classic (S ⊆₁ ∅)) as [Semp|Sinhab].
    exists (exist _ _ DDleast).
    repeat split.
    intros s Ss; apply Semp in Ss; contradiction.
    intros [b' Db'] _ [_ ubb'].
    destruct (Db') as [Db'down Db'join].
    intros x <-; simpl.
    eapply Db'down; eauto.
    apply bDleast; auto.
    assert (s: exists s, S s).
      apply NNPP; intros nex; apply Sinhab.
      intros s Ss.
      apply nex.
      exists s; auto.
    destruct s as [Sone SSone].
    destruct (directed_set_lub S Sone SSone); auto.
    eexists; eauto.
  Qed.

  (*
  Definition 1.15: [Principal Ideals] For finitary basis B = [B, <=], the principal ideal determined
  by b ∈ B, is the ideal Ib such that Ib = {b' ∈ B | b' <= b}.
  *)

  Definition principal_ideal (b: B) := R⁻¹ b.

  Lemma ideal_principal_ideal: forall b, ideal B R B_fin_basis (principal_ideal b).
  Proof.
    intros b.
    split; unfold transp.
    intros e Reb e' Re'e.
    destruct order_R.
    eapply ord_trans; eauto.
    intros s sR sfin.
    destruct B_fin_basis as (foo & bar & slub).
    destruct (slub s) as [b' b'lub]; auto.
    exists b; split; hnf; auto.
    exists b'; split; auto.
    destruct b'lub as [b'ub bmin].
    apply bmin; repeat split; auto.
  Qed.

  (*
  Definition 1.24: [Isomorphic Partial Orders] Two partial orders A and B are isomorphic,
  denoted A ≈ B, iff there exists a one-to-one onto function m : A → B that preserves the approximation ordering:
  ∀a, b ∈ A, a <= b ⇐⇒ m(a) <= m(b).
  *)

  Definition isomorphic (_: order _ R) B' (R': relation B') (order_R': order _ R') (f: B -> B') :=
    (forall a b, f a = f b -> a = b) /\
    (forall b', exists b, f b = b') /\
    (forall a b, R a b <-> R' (f a) (f b)).

  Lemma order_proj: forall A (R: relation A) (order_R: order _ R) P,
    order {x: A | P x} (@proj1_sig _ _ ↓ R).
  Proof.
    clear R B B_fin_basis order_R D.
    intros A R order_R P.
    destruct order_R.
    split.
    intros [x Px]; compute; auto.
    intros [x Px] [y Py] [z Pz] rxy ryz; compute; eauto.
    intros [x Px] [y Py] rxy ryx; compute in rxy, ryx |- *.
    apply subset_eq; simpl.
    eauto.
  Qed.

  Lemma order_subset: forall A,
    order (A -> Prop) set_subset.
  Proof.
    intros A.
    split; auto with *.
    intros a b ab ba.
    apply functional_extensionality.
    intros x.
    apply propositional_extensionality.
    split; auto.
  Qed.

  Lemma order_proj_subset: forall A P,
    order {x: A -> Prop | P x} (@proj1_sig _ _ ↓ set_subset).
  Proof.
    intros A P.
    apply order_proj.
    apply order_subset.
  Qed.

  (*
  Theorem 1.16: The principal ideals over a finitary basis B form a finitary basis under the subset
  ordering.
  *)

  Lemma fin_basis_iso: forall B' R' order_R' f,
    isomorphic order_R B' R' order_R' f ->
    fin_basis _ R'.
  Proof.
    pose (cons_eps := IndefiniteDescription.constructive_indefinite_description).
    clear D.
    intros B' R' order_R' B_to_B' (B_to_B'_inj & B_to_B'_sur & B_to_B'_prsv).
    destruct B_fin_basis as ([Binhab] & [Bcountf Bcountf_spec] & Bfinjoinclosed).
    pose (B'_to_B := fun b' => let (b, _) := cons_eps _ _ (B_to_B'_sur b') in b).
    repeat split.
    auto.
    unshelve eexists.
    intros b.
    apply (Bcountf (B'_to_B b)).
    simpl.
    intros b b' bcounteq.
    specialize (Bcountf_spec _ _ bcounteq) as beq.
    unfold B'_to_B in beq.
    repeat match type of beq with context [cons_eps _ _ ?V] => destruct (cons_eps _ _ V) as [? <-] end.
    subst x0; auto.
    intros s [slist inslist] [b' [_ ubb']].
    destruct (Bfinjoinclosed (B_to_B' ↓₁ s)) as [b [[_ bub] bmin]].
    exists (map B'_to_B slist).
    intros x sbx.
    apply in_map_iff.
    exists (B_to_B' x).
    unfold B'_to_B.
    repeat match goal with |- context [cons_eps _ _ ?V] => destruct (cons_eps _ _ V) end.
    apply B_to_B'_inj in e; subst.
    split; auto.
    exists (B'_to_B b').
    repeat split; auto.
    intros b'' sb''.
    apply B_to_B'_prsv.
    unfold B'_to_B.
    repeat match goal with |- context [cons_eps _ _ ?V] => destruct (cons_eps _ _ V) as [? <-] end.
    apply ubb'; auto.
    exists (B_to_B' b).
    repeat split.
    intros b'' sb''.
    destruct (B_to_B'_sur b'') as [b''' <-].
    apply B_to_B'_prsv.
    apply bub; auto.
    intros b'' _ [_ ubb''].
    destruct (B_to_B'_sur b'') as [b''' <-].
    apply B_to_B'_prsv.
    apply bmin; repeat split.
    intros b'' sb''.
    apply B_to_B'_prsv.
    eapply ubb''; eauto.
  Qed.

  Lemma iso_principal_ideals:
    isomorphic order_R {i: _ | exists b, i = principal_ideal b } _ (order_proj_subset _ _)
      (fun p => exist _ (principal_ideal p) (ex_intro _ p eq_refl)).
  Proof.
    destruct order_R.
    repeat split; unfold map_rel; simpl.
    intros a b abeq.
    apply subset_eq in abeq; simpl in *.
    eapply ord_antisym.
    apply (f_equal (flip apply a)) in abeq; compute in abeq; rewrite <- abeq; auto.
    apply (f_equal (flip apply b)) in abeq; compute in abeq; rewrite abeq; auto.
    intros [i [p ->]].
    exists p; simpl; auto.
    intros rab x rxa.
    unfold principal_ideal, transp in *; eauto.
    intros rarb.
    unfold principal_ideal, transp in *; eauto.
  Qed.

  Lemma principal_ideals_fin_basis:
    fin_basis {i: _ | exists b, i = principal_ideal b } (@proj1_sig _ _ ↓ set_subset).
  Proof.
    apply (fin_basis_iso _ _ _ _ iso_principal_ideals).
  Qed.

  (*
  Definition 1.17: [Finite Elements] An element e of a cpo D = [D, <=] is finite iff for every
  directed subset S of D, e = ⋃S implies e ∈ S. The set of finite elements in a cpo D is denoted D0

  Seems necessary to exclude empty set here.
  *)

  Definition el_finite :=
    fun (cpo_d: cpo B R) (e: B) =>
      forall s, ~s ⊆₁ ∅ -> directed _ R s -> lub _ R s set_full e -> s e.
End Definitions.

Section Definitions.
  Variable B: Type.
  Variable R: relation B.
  Variable B_fin_basis: fin_basis B R.
  Variable order_R: order _ R.
  Let D := construct_domain B R B_fin_basis.

  (*
  Theorem 1.18: An element of the domain D of ideals determined by a finitary basis B is finite
  iff it is principal.
  *)

  Lemma finite_principal:
    el_finite _ _ (d_cpo B R B_fin_basis order_R) =
    (fun x => exists e, x = principal_ideal _ R e) ∘ (@proj1_sig _ _).
  Proof.
    pose (cons_eps := IndefiniteDescription.constructive_indefinite_description).
    fold D.
    apply functional_extensionality.
    intros [e [Dedown Dejoin]].
    apply propositional_extensionality.
    split.
    intros efin.

    pose (dirS :=
     fun '(exist _ s Ds: {s: B -> Prop | D s}) => exists i, e i /\ principal_ideal _ R i ≡₁ s).

    unshelve epose (es := efin _ _ _ _); repeat split.

    apply dirS.
    destruct (constructed_domain_least _ R B_fin_basis) as [Dv lbv]; auto.
    intros dirSnull; unshelve eapply dirSnull.
    apply (exist _ _ Dv).

    fold cons_eps in Dv, lbv |- *.
    match goal with |- dirS (exist _ (eq (` ?G)) _) => destruct G as [Bleast [foo bBleast]] end.
    exists Bleast; repeat split; auto.
    unshelve eassert (e_nonempty := ideal_nonempty _ R B_fin_basis e _).
    split; auto.
    destruct (classic (exists x, e x)) as [[x ex]|enull].
    apply Dedown with x; auto.
    contradict e_nonempty; intros x ex.
    contradict enull; eauto.
    intros x pix; simpl in *.
    destruct order_R; eapply ord_antisym; eauto.
    intros x <-; simpl in *.
    destruct order_R; apply ord_refl.
    intros nnull S' dirSS' S'fin.
    pose (Ss'_to_prin :=
      fun  '(exist _ s' Ds as s) (ss: S' s) =>
        ` (cons_eps _ _ (dirSS' s ss))).
    pose (S'prins := fun p =>
      exists s ss, p = Ss'_to_prin s ss).
    destruct (Dejoin S'prins) as (b & lubb & eb).
    intros p [[sp Dsp] [S'sp ->]].
    unfold Ss'_to_prin.
    match goal with |- e (` ?G) => destruct G as (p' & ep' & pipsp) end.
    simpl; auto.
    destruct S'fin as [S'list inS'list].
    exists (flat_map (fun s =>
      match excluded_middle_informative (S' s)
      with
        left ss => Ss'_to_prin s ss :: nil
      | right _ => nil
      end) S'list).
    intros p [[s Ds] [S's ->]].
    simpl.
    specialize (inS'list _ S's).
    induction S'list.
    contradiction.
    destruct inS'list.
    subst a.
    simpl.
    apply in_app_l.
    destruct (excluded_middle_informative (S' (exist _ s Ds))).
    assert (s0 = S's) by apply proof_irrelevance; subst s0.
    simpl; left; auto.
    contradiction.
    apply in_app_r; auto.
    unshelve eexists.
    exists (principal_ideal _ R b).
    apply ideal_principal_ideal; auto.
    repeat split.
    exists b; auto.
    intros s' S's' v s'v.
    simpl.
    destruct lubb as [[_ ubb] bmin].
    pose (b' := Ss'_to_prin _ S's').
    destruct order_R; apply ord_trans with b'.
    unfold b', Ss'_to_prin in b' |- *.
    destruct s' as [s' Ds'].
    match goal with |- R v (` ?G) => destruct G as (p & ep & pps') end; simpl in *.
    destruct pps' as [pps'1 pps'2].
    specialize (pps'2 _ s'v); auto.
    apply ubb.
    exists s', S's'; auto.
    intros [s Ds] (i & ei & pis1 & pis2) v sv; simpl in *.
    eapply Dedown; eauto.
    specialize (pis2 _ sv); auto.
    intros b' _ [_ ubb'] v ev; simpl in *.
    unshelve evar (vprin: {s: B -> Prop | D s}).
    exists (principal_ideal _ R v).
    apply ideal_principal_ideal; auto.
    apply (ubb' vprin).
    simpl.
    exists v; auto.
    simpl; destruct order_R; apply ord_refl.

    destruct es as (i & ei & pie).
    exists i; simpl.
    auto.
    apply functional_extensionality.
    intros x.
    apply propositional_extensionality.
    split; apply pie.

    intros [p ppi] ds dsinhab dsdir lubdsi.
    simpl in *.
    destruct (classic (exists x, ds x)) as [[x dsx]|dsnull].
    destruct (directed_set_lub _ R B_fin_basis order_R _ _ dsx dsdir) as [Dsunion sunionlub].
    pose (sunion := ⋃₁i ∈ ds, ` i).
    fold D in Dsunion, sunionlub.
    assert (i_sunion: e ≡₁ sunion).
      destruct lubdsi as [[_ ubi] imin], sunionlub as [[_ ubsunion] sunionmin].
      unshelve eassert (i_sunion := imin (exist _ _ Dsunion) _ _); repeat split; eauto.
      unshelve eassert (sunion_i := sunionmin (exist _ _ (conj Dedown Dejoin)) _ _); repeat split; eauto.
    assert (sunion_p: sunion p).
      apply i_sunion.
      subst e.
      destruct order_R; apply ord_refl.
    destruct sunion_p as ([ps Dps] & dsps & psp).
    simpl in *.
    assert (ps_i: ps ≡₁ e).
      split.
      destruct lubdsi as [[_ ubi] imin].
      intros x'.
      unshelve eassert (ps_i := ubi (exist _ _ Dps) _ _); repeat split; eauto.
      eapply set_subset_trans; [subst e|].
      intros x' Rx'p.
      destruct Dps as [psdown psjoin].
      eapply psdown; eauto.
      auto.
    assert (ps_i_eq: ps = e).
      apply functional_extensionality.
      intros x'.
      apply propositional_extensionality.
      split; subst e; apply ps_i.
    subst ps.
    assert (Dps = (conj Dedown Dejoin)) by apply proof_irrelevance; subst Dps; auto.
    contradict dsinhab; intros x dsx; apply dsnull; eauto.
  Qed.

  (*
  Theorem 1.19: Let D be the domain determined by a finitary basis B.
  For any I ∈ D, I = ⋃{I' ∈ D, el_finite I' | I' ⊆ I}.
  *)

  Lemma ideal_join_principals: forall i, D i ->
    i ≡₁ ⋃₁pi ∈ @proj1_sig _ _ ↑₁ el_finite _ _ (d_cpo B R B_fin_basis order_R) ∩₁
                flip set_subset i,
            pi.
  Proof.
    destruct finite_principal as [fin_prin prin_fin].
    intros i [Didown Dijoin].
    split.
    intros v iv.
    pose (p := principal_ideal _ R v).
    assert (Dp := ideal_principal_ideal _ R B_fin_basis order_R v).
    pose (p' := exist _ p Dp).
    unshelve epose (p'fin := prin_fin _ _).
    apply p'.
    exists v.
    simpl; auto.
    exists (`p').
    repeat esplit; eauto; simpl.
    intros v' pv'.
    apply Didown with v; auto.
    destruct order_R; apply ord_refl.
    intros v (s & (([s' Ds] & s'fin & ss) & si) & sv).
    simpl in *; subst s'.
    unfold flip in si.
    auto.
  Qed.

  (*
  Definition 1.20: [Partial and Total Elements] Let B be a partial order. An element b ∈ B
  is partial iff there exists an element b' ∈ B such that b <> b' and b <= b'. An element b ∈ B is total
  iff for all b' ∈ B, b <= b' implies b = b'.
  *)

  Definition el_partial b := exists b', b <> b' /\ R b b'.
  Definition el_total b := forall b', R b b' -> b = b'.
End Definitions.

Section Definitions.
  Variable B: Type.
  Variable R: relation B.
  Variable B_fin_basis: fin_basis B R.
  Variable order_R: order _ R.
  Let D := construct_domain B R B_fin_basis.

  Lemma flip_iso:
    forall B' (R': relation B') (order_R': order _ R') (f: B -> B')
      (iso: isomorphic B R order_R B' R' order_R' f),
        let cons_eps := IndefiniteDescription.constructive_indefinite_description in
        let '(conj _ (conj iso_sur _)) := iso in
        isomorphic B' R' order_R' B R order_R
          (fun x =>
            let (x', _) := cons_eps _ _ (iso_sur x) in
            x').
  Proof.
    intros B' R' order_R' B_to_B' (B_to_B'_inj & B_to_B'_sur & B_to_B'_prsv).
    intros cons_eps.
    match goal with |- isomorphic _ _ _ _ _ _ ?F => set (B'_to_B := F) end.
    repeat split.
    intros a b.
    unfold B'_to_B.
    repeat match goal
      with |- context [ cons_eps _ _ (B_to_B'_sur ?V) ] =>
        destruct (cons_eps _ _ (B_to_B'_sur V)) as [? <-]
    end.
    intros; subst; auto.
    intros b.
    exists (B_to_B' b).
    unfold B'_to_B.
    repeat match goal
      with |- context [ cons_eps _ _ (B_to_B'_sur ?V) ] =>
        destruct (cons_eps _ _ (B_to_B'_sur V))
    end.
    auto.
    intros rab; apply B_to_B'_prsv.
    unfold B'_to_B.
    repeat match goal
      with |- context [ cons_eps _ _ (B_to_B'_sur ?V) ] =>
        destruct (cons_eps _ _ (B_to_B'_sur V)) as [? <-]
    end.
    auto.
    unfold B'_to_B.
    repeat match goal
      with |- context [ cons_eps _ _ (B_to_B'_sur ?V) ] =>
        destruct (cons_eps _ _ (B_to_B'_sur V)) as [? <-]
    end.
    intros rab; apply B_to_B'_prsv; auto.
  Qed.
End Definitions.
  
Section Definitions.
  Variable B: Type.
  Variable R: relation B.
  Variable B_fin_basis: fin_basis B R.
  Variable order_R: order _ R.
  Let D := construct_domain B R B_fin_basis.

  (*
  Theorem 1.25: Let D be the domain determined by a finitary basis B. D0 forms a finitary basis B' under
  the approximation ordering ⊆ (restricted to D0). Moreover, the domain E determined by the finitary basis
  B' is isomorphic to D.
  *)

  Lemma domain_finite_iso:
    forall
      B' (R': relation B') (order_R': order _ R')
      (f: B -> B')
      (b_cpo: cpo _ R)
      (b'_cpo: cpo _ R'),
      isomorphic B R order_R B' R' order_R' f ->
      exists b'fin_spec: (forall x, el_finite _ _ b'_cpo (f (` x))),
        isomorphic {x: B | el_finite _ _ b_cpo x} _ (order_proj _ _ order_R _)
                  {x: B' | el_finite _ _ b'_cpo x} _ (order_proj _ _ order_R' _)
                  (fun x => exist _ _ (b'fin_spec x)).
  Proof.
    pose (cons_eps := IndefiniteDescription.constructive_indefinite_description).
    clear B_fin_basis D.
    revert B R order_R.
    match goal with |-
      forall (a: ?A) (b: ?B) (c: ?C)
            (d: ?D) (e: ?E) (f: ?F)
            (g: ?G) (h: ?H) (i: ?I)
            (j: ?J), @ex ?T _ =>
      assert (B_to_B'_spec:
        forall (a: A) (b: B) (c: C)
               (d: D) (e: E) (f: F)
               (g: G) (h: H) (i: I)
               (j: J), T)
    end.
      intros B R order_R B' R' order_R' B_to_B' b_cpo b'_cpo (B_to_B'_inj & B_to_B'_sur & B_to_B'_prsv).
      pose (B'_to_B := fun b' => let (b, _) := cons_eps _ _ (B_to_B'_sur b') in b).
      intros [v vfin] s s_inhab sdir slub; simpl in *.
      unshelve eassert (vfin' := vfin _ _ _ _).
      apply (B_to_B' ↓₁ s).
      intros s'_inhab; apply s_inhab; intros s' ss'; apply s'_inhab with (B'_to_B s').
      simpl; unfold B'_to_B, set_map, set_collect.
      match goal with |- context [ cons_eps _ _ ?V ] => destruct (cons_eps _ _ V) as [v' <-] end.
      auto.
      intros s'_inhab S' S's' S'fin.
      destruct sdir with (B_to_B' ↑₁ S') as (b & svib & ubb); auto.
      intros x' (y & sy & <-); apply S's'; auto.
      destruct S'fin as [S'list inS'list].
      exists (map B_to_B' S'list).
      intros x' (x'' & S'x'' & <-).
      specialize (inS'list x'' S'x'').
      apply in_map; auto.
      exists (B'_to_B b).
      simpl; unfold B'_to_B, set_map, set_collect.
      match goal with |- context [ cons_eps _ _ ?V ] => destruct (cons_eps _ _ V) as [v' <-] end.
      split; compute; auto.
      intros s'' S's''.
      apply B_to_B'_prsv.
      apply ubb.
      eexists; eauto.
      destruct slub as [[_ ubv] lubv].
      repeat split.
      intros s' ss'.
      apply B_to_B'_prsv; auto.
      intros b' _ ubb'.
      apply B_to_B'_prsv.
      apply lubv.
      constructor.
      repeat split.
      intros b'' sb''.
      destruct (B_to_B'_sur b'') as [b''' <-].
      apply B_to_B'_prsv.
      eapply ubb'.
      auto.
      auto.
    
    intros B R order_R B' R' order_R' B_to_B' b_cpo b'_cpo (B_to_B'_inj & B_to_B'_sur & B_to_B'_prsv).
    pose (B'_to_B := fun b' => let (b, _) := cons_eps _ _ (B_to_B'_sur b') in b).
    unshelve eexists.
    unshelve eapply B_to_B'_spec; eauto.
    red; auto.
    repeat split.
    intros [a afin] [b bfin] [=abeq].
    apply B_to_B'_inj in abeq.
    subst; apply subset_eq; auto.
    intros [b' b'fin].
    unshelve eexists.
    unshelve eexists.
    2: unshelve eapply (B_to_B'_spec _ _ _ _ _ _ _ _ _
                 (flip_iso _ _ _ _ _ _ _ (conj B_to_B'_inj (conj B_to_B'_sur B_to_B'_prsv)))); auto.
    eexists; eauto.
    fold cons_eps; simpl.
    apply subset_eq; simpl.
    match goal with |- context [ cons_eps _ _ ?V ] => destruct (cons_eps _ _ V) as [v' <-] end.
    auto.
    1,2: destruct a as [a afin], b as [b bfin].
    1,2: unfold map_rel; simpl.
    1,2: apply B_to_B'_prsv.
  Qed.

  Lemma domain_finite_domain:
    let D0 := @proj1_sig _ _ ↑₁ el_finite _ _ (d_cpo B R B_fin_basis order_R) in
    exists D0_fin_basis: fin_basis {s: _ | D0 s} (@proj1_sig _ _ ↓ set_subset),
      let D' := (construct_domain _ _ D0_fin_basis) in
      (exists f_spec: (forall x, D0
          (principal_ideal _ R x)),
        isomorphic B R order_R
                  {s: _ | D0 s} _ (order_proj_subset _ _)
                  (fun x => exist _ _ (f_spec x)))
      /\
      (exists f_spec: (forall x, D'
          (proj1_sig (P := D0) ↓₁ ⋃₁p ∈ (`x), set_equiv (principal_ideal _ R p))),
        isomorphic {s: _ | D s} _ (order_proj_subset _ _)
                  {s: _ | D' s} _ (order_proj_subset _ _)
                  (fun x => exist _ _ (f_spec x))).
  Proof.
    pose (cons_eps := IndefiniteDescription.constructive_indefinite_description).
    intros D0.
    fold D in D0.
    destruct (principal_ideals_fin_basis _ _ B_fin_basis order_R) as ([D0'inhab] & D0'count & D0'closed).
    pose (fin_prin := finite_principal _ _ B_fin_basis order_R).
    fold D in fin_prin.
    unshelve evar (D0'_to_D0: {i : B -> Prop | exists b : B, i = principal_ideal B R b} -> {i: _ | D0 i}).
      intros [i ipb].
      exists i.
      red.
      rewrite fin_prin.
      hnf; simpl.
      unshelve eexists.
      exists i.
      destruct ipb as [b ->].
      apply ideal_principal_ideal; auto.
      split; auto.
    unshelve evar (D0_to_D0': {i: _ | D0 i} -> {i : B -> Prop | exists b : B, i = principal_ideal B R b}).
      intros [i D0i].
      exists i.
      destruct D0i as ([i' Di'] & ipb & <-).
      rewrite fin_prin in ipb; hnf in ipb; simpl in ipb |- *.
      auto.

    (* D0_fin_basis *)
    match goal with |- @ex ?A _ => assert (D0_fin_basis: A) end.
    repeat split.
    auto.
    destruct D0'count as [f finj].
    exists (f ∘ D0_to_D0').
    intros b b' bb'eq.
    specialize (finj (D0_to_D0' b) (D0_to_D0' b')).
    lapply finj.
    intros bb'eq'.
    destruct b as [b D0b], b' as [b' D0b'].
    apply subset_eq in bb'eq'; simpl in bb'eq'.
    subst b'; apply subset_eq; auto.
    auto.
    intros S [S'list inS'list] S'cons.
    destruct (D0'closed (D0'_to_D0 ↓₁ S)).
    exists (map D0_to_D0' S'list).
    intros x Sx.
    apply in_map_iff.
    exists (D0'_to_D0 x).
    split.
    destruct x as [x D0x].
    apply subset_eq; simpl.
    auto.
    apply inS'list; auto.
    hnf.
    destruct S'cons as [b [_ ubb]].
    exists (D0_to_D0' b).
    repeat split.
    intros s Ss v sv.
    destruct b as [b D0b].
    eapply ubb; eauto.
    destruct s; simpl in *; auto.
    exists (D0'_to_D0 x).
    destruct H as [[_ ubx] xmin].
    repeat split.
    intros s Ss v sv.
    destruct x; unfold map_rel in ubx; simpl in *.
    apply ubx with (D0_to_D0' s); destruct s; auto.
    hnf; simpl in *.
    let Sst := type of Ss in match goal with |- ?V => assert (V = Sst) end.
    f_equal.
    apply subset_eq; simpl.
    auto.
    rewrite H; auto.
    intros b' _ [_ ubb'] v xv.
    specialize (xmin (D0_to_D0' b') I).
    destruct b'; unfold map_rel in xmin; simpl in *.
    eapply xmin.
    repeat split.
    intros s Ss v' sv'; simpl in *.
    apply (ubb' (D0'_to_D0 s)); auto.
    destruct s; auto.
    destruct x; auto.
    exists D0_fin_basis.

    intros D'.

    assert (D0_prin: forall b, D0 (principal_ideal _ R b)).
      unshelve eexists.
      exists (principal_ideal _ R b).
      apply ideal_principal_ideal; auto.
      simpl; split; auto.
      apply prin_fin; unfold compose; simpl.
      exists b; auto.
    pose (B_to_D0_1 := fun b => exist _ _ (D0_prin b)).
    
    (* B to D0 isomorphism *)
    match goal with |- ?A /\ _ =>
      assert (B_to_D0_iso: A); [|split; auto;
        destruct B_to_D0_iso as (B_to_D0_spec & B_to_D0_inj & B_to_D0_sur & B_to_D0_prsv)]
    end.
    exists D0_prin.
    repeat split.
    intros a b [=ab].
    destruct order_R.
    unfold principal_ideal in ab. 
    assert (abv: forall v, R⁻¹ a v = R⁻¹ b v).
      rewrite ab.
      reflexivity.
    compute in abv.
    apply ord_antisym.
    rewrite <- abv; auto.
    rewrite abv; auto.
    intros [s [[s' Ds'] [s'fin <-]]].
    destruct (fin_prin _ s'fin) as [b spb].
    simpl in *.
    exists b.
    assert (principal_ideal B R b = s').
      apply functional_extensionality.
      intros x.
      apply propositional_extensionality.
      split; apply spb.
    subst s'.
    f_equal.
    apply proof_irrelevance.
    compute; intros rab x rxa.
    destruct order_R; eapply ord_trans; eauto.
    compute; intros xab.
    apply xab; destruct order_R; auto.

    assert (D0_prin = B_to_D0_spec) by apply proof_irrelevance; subst D0_prin.

    (* D to D' in D' *)
    match goal with |- @ex ?P _ => assert (D_to_D'_spec: P) end.
      intros [s [Dsdown Dsjoin]].
      repeat split; simpl.
      intros [s' D0s'] (p & sp & s'pp) [sl [[s'' Ds''] [s''fin <-]]] sls'.
      unfold set_map, map_rel in sls' |- *; simpl in *.
      specialize (fin_prin _ s''fin) as [b' s''pb]; simpl in *.
      exists b'; split; auto.
      eapply Dsdown; eauto.
      apply s'pp.
      apply sls'.
      apply s''pb.
      destruct order_R; apply ord_refl.
      intros S' S's S'fin; simpl in *.
      pose (s'find := fun v S'v => proj1_sig (cons_eps _ _ (S's v S'v))).
      pose (s' := fun b => exists v S'v, b = s'find v S'v).
      destruct (Dsjoin s') as (b & [[_ ubb] bmin] & sb).
      intros b' (v & v's & ->).
      unfold s'find.
      match goal with |- s (` ?G) => destruct G as (b' & sb & pbv) end.
      simpl; auto.
      destruct S'fin as [S'list inS'list].
      unshelve eexists.
      clear inS'list.
      induction S'list.
      apply [].
      destruct (excluded_middle_informative (S' a)) as [S'a|].
      constructor 2; [|apply IHS'list]; clear IHS'list.
      apply (s'find a S'a).
      apply IHS'list.
      intros b (v & S'v & ->).
      specialize (inS'list _ S'v).
      induction S'list.
      contradiction.
      destruct inS'list.
      subst a.
      simpl.
      destruct (excluded_middle_informative (S' v)); simpl.
      left; f_equal; apply proof_irrelevance.
      contradiction.
      simpl.
      destruct (excluded_middle_informative (S' a)); simpl.
      right; auto.
      auto.
      exists (B_to_D0_1 b).
      repeat split.
      intros [s'' D0s'']; unfold map_rel; simpl.
      intros S's'' v s''v.
      destruct (S's _ S's'') as (b' & sb' & s''pb'); simpl in *.
      apply s''pb' in s''v.
      destruct order_R; eapply ord_trans; eauto.
      apply ubb.
      exists _, S's''.
      unfold s'find; simpl.
      match goal with |- _ = ` ?G => destruct G as (b'' & sb'' & s''pb'') end.
      simpl.
      destruct order_R; eapply ord_antisym.
      apply s''pb''; apply s''pb'; apply ord_refl.
      apply s''pb'; apply s''pb''; apply ord_refl.
      intros [b' [[b'' Db''] [b''fin <-]]] _ [_ ubb']; unfold map_rel; simpl in *.
      destruct (fin_prin _ b''fin) as [b' b''pb']; simpl in *.
      intros v rvb.
      apply b''pb'.
      destruct order_R; eapply ord_trans; eauto.
      apply bmin.
      constructor.
      split.
      constructor.
      intros lb ([s'lb [[s'lb' Ds'lb'] [s'lb'fin <-]]] & S'lb & ->).
      specialize (ubb' _ S'lb); unfold map_rel in ubb'; simpl in *.
      unfold s'find; simpl.
      match goal with |- R (` ?G) _ => destruct G as (b''' & sb''' & foo) end; simpl.
      destruct (fin_prin _ s'lb'fin) as [foo' bar']; simpl in *.
      apply b''pb'.
      apply ubb'.
      apply foo.
      destruct order_R; apply ord_refl.
      exists b; auto.

    (* D to D' isomorphism *)
    exists D_to_D'_spec.
    pose (D_to_D'_1 := fun b => exist _ _ (D_to_D'_spec b)).
    repeat split.
    intros [a Da] [b Db] [=ab].
    cut (a = b).
    intros; subst.
    f_equal; apply proof_irrelevance.
    cut (a ≡₁ b).
    intros ab'.
    apply functional_extensionality;
    intros x;
    apply propositional_extensionality.
    split; apply ab'.
    (*
    match goal with
      |- ?A = ?B =>
        set (a' := D_to_D'_1 A) in *;
        set (b' := D_to_D'_1 B) in *;
        set (D'a' := (D_to_D'_spec A));
        set (D'b' := (D_to_D'_spec B))
    end.
    pose (aprin := ideal_join_principals _ _ B_fin_basis order_R _ Da).
    pose (bprin := ideal_join_principals _ _ B_fin_basis order_R _ Db).
    pose (a'prin := ideal_join_principals _ _ D0_fin_basis (order_proj_subset _ _) _ D'a').
    pose (b'prin := ideal_join_principals _ _ D0_fin_basis (order_proj_subset _ _) _ D'b').
    fold D in aprin, bprin.
    fold D' in a'prin, b'prin.
    simpl in *.
    rewrite aprin.
    rewrite bprin.
    split; intros v.
    intros [pa [[[[a'' Da''] [a''fin <-]] paa] pav]]; simpl in *.
    apply fin_prin in a''fin as [a''p a''prin]; simpl in *.
    *)
    split; intros pa apa.
    1,2: apply (f_equal (flip apply (B_to_D0_1 pa))) in ab.
    1,2: unfold flip, apply, B_to_D0_1, D_to_D'_1, set_map, set_bunion in ab; simpl in ab.
    match type of ab with ?A = _ => assert (ex_b: A) end.
    3: match type of ab with _ = ?A => assert (ex_b: A) end.
    1,3: exists pa; auto.
    rewrite ab in ex_b.
    2: rewrite <- ab in ex_b.
    1,2: destruct ex_b as [pb [bpb pbpa]].
    1,2: destruct (B_to_D0_inj pa pb); auto.
    1,2: apply subset_eq; simpl.
    1,2: apply functional_extensionality.
    1,2: intros x.
    1,2: apply propositional_extensionality.
    1,2: split; apply pbpa.

    intros [a' D'a'].
    assert (Da: D (fun b => a' (B_to_D0_1 b))).
      destruct D'a' as [D'a'down D'a'join].
      split.
      intros b a'b v rvb'.
      eapply D'a'down; eauto.
      intros x rxv; simpl in *.
      destruct order_R; eapply ord_trans; eauto.
      intros S' S'f' S'fin.
      specialize (D'a'join (fun s => let (b, _) := cons_eps _ _ (B_to_D0_sur s) in S' b)).
      destruct D'a'join as (b' & [[_ ubb'] b'min] & a'b').
      intros s.
      destruct (cons_eps _ _ (B_to_D0_sur s)).
      intros S'x; apply S'f' in S'x.
      subst; apply S'x.
      destruct S'fin as [S'list inS'list].
      exists (map B_to_D0_1 S'list).
      intros s.
      destruct (cons_eps _ _ (B_to_D0_sur s)).
      intros S'x; apply inS'list in S'x.
      subst.
      fold (B_to_D0_1 x); apply in_map; auto.
      destruct (B_to_D0_sur b') as [b <-].
      exists b; repeat split; auto.
      intros v S'v.
      specialize (ubb' (B_to_D0_1 v)).
      destruct (cons_eps _ _ (B_to_D0_sur (B_to_D0_1 v))).
      apply B_to_D0_inj in e; subst.
      specialize (ubb' S'v).
      hnf in ubb'; simpl in *.
      apply ubb'.
      destruct order_R; apply ord_refl.
      intros v _ [_ ubv].
      specialize (b'min (B_to_D0_1 v)).
      apply b'min; simpl in *.
      constructor.
      split.
      constructor.
      intros s.
      destruct (cons_eps _ _ (B_to_D0_sur s)).
      subst.
      intros S'x; apply ubv in S'x.
      intros v' rvx; simpl in *.
      destruct order_R; eapply ord_trans; eauto.
      destruct order_R; apply ord_refl.
    exists (exist _ _ Da).
    apply subset_eq; simpl.
    unfold D_to_D'_1; simpl.
    apply functional_extensionality.
    intros [pa D0pa].
    apply propositional_extensionality.
    split.
    intros [pab [a'pab foo]].
    simpl in *.
    match goal with _: a' ?A |- a' ?B => assert (heq: A = B) end.
    apply subset_eq; simpl.
    apply functional_extensionality; intros x.
    apply propositional_extensionality.
    split; apply foo.
    rewrite <- heq; auto.
    intros a'pa.
    hnf; simpl in *.
    destruct (B_to_D0_sur (exist _ _ D0pa)) as [b beq].
    change (fun s => D0 s) with D0 in *.
    rewrite <- beq in a'pa.
    exists b; split; auto.
    apply subset_eq in beq; simpl in *.
    subst; auto.
    1,2: destruct a as [a Da], b as [b Db].
    1,2: intros lab.
    1,2: hnf in lab |- *; unfold D_to_D'_1 in lab |- *; simpl in *.
    intros [x D0x] (b' & ab' & xpb'); hnf; simpl in *.
    exists b'; split; auto.
    intros x ax.
    destruct (lab (B_to_D0_1 x)) as (b' & bb' & b'px'); destruct (B_to_D0_1 x) as [x' D0x'] eqn:xb.
    exists x; split; auto; simpl.
    apply subset_eq in xb; simpl in *.
    subst; auto.
    apply subset_eq in xb; simpl in *; subst x'.
    destruct (B_to_D0_inj b' x).
    apply subset_eq; simpl.
    apply functional_extensionality.
    intros x'.
    apply propositional_extensionality.
    split; apply b'px'.
    auto.

    (*
    D to D' of S is the set of downward closures of elements in S.
      proj1_sig (P:=D0) ↓₁ (⋃₁p ∈ `d, set_equiv (principal_ideal B R p))
    injectivity:
      D' of a = D' of b ->
      {i: ∃p ∈ a, i = (<= p)} = {i: ∃p ∈ b, i = (<= p)} ->
      ∀pa ∈ a, ∃pb ∈ b, (<= pa) = (<= pb) ->
      ∀pa ∈ a, ∃pb ∈ b, pa = pb ->
      ∀pa ∈ a, pa ∈ b ->
      a = b
    surjectivity:
      D' a' ->
      a' = {si: ∃i ∈ D0, i ∈ a' /\ si ⊆D0 i} -> (by joinprin)
      ∀pa' ∈ a', ∃i, D0 i /\ i ∈ a' /\ pa' ⊆D0 i ->
      ∀pa' ∈ a', ∃b, i := (<= b), i ∈ a' /\ pa' ⊆D0 i -> (B_to_D0_1, sur)
      ∀pa' ∈ a', ∃b, (<= b) ∈ a' /\ pa' ⊆D0 (<= b) ->
      ∀pa' ∈ a', ∃p b ∈ B, (<= b) ∈ a' /\ (<= p) ⊆D0 (<= b) /\ pa' = (<= p) ->
      ∀pa' ∈ a', ∃p b ∈ B, (<= b) ∈ a' /\ p <= b /\ pa' = (<= p) ->
      ∀pa' ∈ a', ∃p b ∈ B, b ∈ {b': (<= b') ∈ a'} /\ p <= b /\ pa' = (<= p) ->
      ∀pa' ∈ a', ∃p ∈ {v: ∃b ∈ B, b ∈ {b': (<= b') ∈ a'} /\ v <= b}, pa' = (<= p) ->
      {i: ∃p ∈ {v: ∃b ∈ B, b ∈ {b': (<= b') ∈ a'} /\ v <= b}, i = (<= p)} = a' -> 
      a := {v: ∃b ∈ B, b ∈ {b': (<= b') ∈ a'} /\ v <= b}, {i: ∃p ∈ a, i = (<= p)} = a' -> 
      ∃ a, D a /\ {i: ∃p ∈ a, i = (<= p)} = a' -> (by joinprin)
      ∃ a, D a /\ D_to_D'_1 a = a' 
    *)
  Qed.

  (*
  The preceding theorem justifies the following comprehensive definition for domains.
  Definition 1.26: [Domain] A cpo D = (D, <=) is a domain iff
    • D0 forms a finitary basis under the approximation ordering <= restricted to D0, and
    • D is isomorphic to the domain E determined by D0

  In other words, a domain is a partial order that is isomorphic to a constructed domain.
  *)

  Definition domain (cpoB: cpo B R) := 
    let B0 := {s: _ | el_finite _ _ cpoB s} in
    exists
      B0_fin_basis: fin_basis B0 (@proj1_sig _ _ ↓ R),
      let D := {s: _ | construct_domain _ _ B0_fin_basis s} in
      exists
        B_to_D: B -> D,
        isomorphic B R order_R
                   D _ (order_proj_subset _ _)
                   B_to_D.
End Definitions.

Section Definitions.
  Variable B: Type.
  Variable R: relation B.
  Variable B_fin_basis: fin_basis B R.
  Variable order_R: order _ R.
  Let D := construct_domain B R B_fin_basis.

  Corollary domain_iso_constructed_domain:
    forall cpoB,
      domain B _ order_R cpoB <->
      exists B' R' (order_R': order _ R') B'_fin_basis B'_to_D',
        isomorphic B R order_R
                   {s: _ | construct_domain B' R' B'_fin_basis s} _ (order_proj_subset _ _)
                   B'_to_D'.
  Proof.
    clear B_fin_basis D.
    pose (cons_eps := IndefiniteDescription.constructive_indefinite_description).
    intros cpoB.
    split.
    intros [B0_fin_basis B_iso].
    exists _, _, (order_proj _ R order_R _), B0_fin_basis.
    auto.
    intros (D0 & RD0 & order_RD0 &
            D0_fin_basis &
            B_to_D & B_to_D_inj & B_to_D_sur & B_to_D_prsv).
    
    destruct (domain_finite_iso
      B R order_R
      _ _ (order_proj_subset _ _)
      _ cpoB (d_cpo _ _ D0_fin_basis order_RD0)
      (conj B_to_D_inj (conj B_to_D_sur B_to_D_prsv))) as
      (B0_to_D0_spec & B0_to_D0_inj & B0_to_D0_sur & B0_to_D0_prsv).

    set (D := construct_domain _ _ D0_fin_basis) in *.
    pose (D0_to_D := fun v =>
      exist D _ (ideal_principal_ideal _ _ D0_fin_basis order_RD0 v)).
    unshelve evar (D_to_B_1: {x: _ | D x} -> B).
      intros v.
      destruct (cons_eps _ _ (B_to_D_sur v)) as [b b_to_d].
      apply b.
    red.

    pose (principal_ideals_fin_basis _ _ B'_fin_basis order_R').

    destruct B_fin_basis as (Binhab & Bcount & Bclosed).
    repeat split.
    destruct (cons_eps _ _ (fin_basis_least _ _ B_fin_basis)) as [Bleast [_ Bleastmin]].
    unshelve eexists; auto.
    intros sBleast sinhab dirsBleast [[_ ubsBleast] lubsBleast].
    destruct (classic (exists v, sBleast v)) as [[v sBleastv]|nv].
    specialize (ubsBleast _ sBleastv).
    specialize (Bleastmin v I).
    assert (v = Bleast).
    destruct order_R; eapply ord_antisym; eauto.
    subst; auto.
    contradict sinhab; intros v sBleastv; apply nv.
    eexists; eauto.
    destruct Bcount as [Bcount Bcountinj].
    exists (Bcount ∘ (@proj1_sig _ _)).
    intros [b bf] [b' b'f]; unfold compose; simpl.
    intros counteq.
    apply subset_eq; simpl.
    auto.
    intros S Sfin Scons.
    edestruct (Bclosed (@proj1_sig _ _ ↑₁ S)) as [b [[_ ubb] lubb]].
    destruct Sfin as [Slist inSlist].
    exists (map (@proj1_sig _ _) Slist).
    intros x ([x' x'f] & Sx & <-).
    specialize (inSlist _ Sx).
    apply in_map; auto.
    destruct Scons as [b [_ ubb]].
    exists (`b).
    split.
    constructor.
    intros s ([s' s'f] & Ss & <-); simpl in *.
    apply ubb in Ss; hnf in Ss; simpl in *.
    auto.



    edestruct dirsBleast; eauto.
    exists (Bleast :: nil).
    intros x sBleastx.
    apply lubsBleast in 
    apply ubsB

    split.
     unshelve eexists.
    exists B'_fin_basis.
  Qed.

  Corollary domain_constructed_domain:
    domain {s: _ | D s} _ (order_proj_subset _ _) (d_cpo _ _ B_fin_basis order_R).
  Proof.
    destruct (domain_finite_domain _ R B_fin_basis order_R) as [D0_fin_basis D_iso].
    red.
    fold D in D0_fin_basis, D_iso |- *.
    exists D0_fin_basis.
  Qed.

  
  let D0 := @proj1_sig _ _ ↑₁ el_finite _ _ (d_cpo B R B_fin_basis order_R) in
  exists D0_fin_basis: fin_basis {s: _ | D0 s} (@proj1_sig _ _ ↓ set_subset),
    let D' := (construct_domain _ _ D0_fin_basis) in
    isomorphic {s: _ | D s} _ (order_proj_subset _ _)
               {s: _ | D' s} _ (order_proj_subset _ _).

  (*
  To conclude this section, we state some closure properties on D to provide more intuition about
  the approximation ordering.
  Theorem 1.27: Let D the the domain determined by a finitary basis B. For any subset S of D,
  the following properties hold:
  1. T
  S ∈ D and T
  S = uS .
  2. if S is directed, then S
  S ∈ D and S
  S =
  F
  S .
  *)
End Definitions.