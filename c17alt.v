
Definition rs2 :=
let mo' := (`mo)%rel in
  ⦗IsRel⦘ ⨾ mo'^? \ (mo' \ sb^⋈) ⨾ ⦗set_compl IsRMW⦘ ⨾ mo'^?.

Definition rs3 :=
let mo' := (` (immediate mo))%rel in
fun x =>
  (⦗eq x⦘ ⨾ ⦗IsRel⦘ ⨾ (((mo' ⨾ ⦗IsRMW⦘)＊ ⨾ mo') ⨾ ⦗sb^⋈ x⦘)＊ ⨾ (mo' ⨾ ⦗IsRMW⦘)＊) x.

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
all: autounfold with unfolderDb.
set (mo' := (`mo)%rel).
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
assert (spo: strict_partial_order mo).
  specialize (mo_total_order_per_loc (0)).
  intros sto; apply sto.
assert (spo': strict_partial_order mo').
  destruct spo as [irr tra].
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
split.
- intros x y [[z [[xz xIsRel] moxy]] rsCond].
  subst z.
  eexists; split; try split; auto;
    eexists; split; try split; auto.
  destruct moxy as [xy|(x' & y' & moxy & <- & <-)].
  eexists; esplit; rewrite clos_refl_transE.
  1, 2: left; auto.
  clear xIsRel.
  apply mo_mo' in moxy.
  apply (imm_trans mo' spo') in moxy.
  set (base := x') in rsCond at 2 3.
  fold base.
  unfold base at 3.
  assert (base_x: (`base) = (`x') \/
                  mo' (`base) (`x') /\ (sb^⋈ (`base) (`x') \/
                                        IsRMW (`x'))).
    constructor 1; auto.
  clearbody base.
  induction moxy.
  destruct H as [moxy' imm].
  pose (moxy := moxy'); apply mo'_mo in moxy; destruct moxy as (x'' & y'' & <- & <- & moxy'').
  assert (sb^⋈ (`base) (`y'') \/ IsRMW (`y'')).
    eapply rsCond.
    eexists; eexists; split; try split.
    2,3: eauto.
    auto.
    destruct base_x as [bx|[mobx]].
    apply sig_ext in bx; subst x''; auto.
    apply mo'_mo in mobx; destruct mobx as (e & f & e1 & e2 & mobx).
    apply sig_ext in e1; subst e.
    apply sig_ext in e2; subst f.
    left; auto.
  destruct H, base_x as [bx|[mobx [x_sb|x_rmw]]].
  1-6: eexists; esplit; erewrite clos_refl_transE.

  (* base = x, sb x y*)
  right; econstructor 1; esplit.
  eexists; esplit.
  erewrite clos_refl_transE; esplit.
  left; auto.
  eexists; eexists; split; split.
  1-5: eauto.
  intros c moxc mocy.
  eapply imm.
  1-2: eapply mo_mo'; eauto.
  auto.
  left; auto.

  (* mo base x, sb base x, sb base y*)
  right; econstructor 1; eexists; esplit; try erewrite clos_refl_transE; try esplit.
  1, 2: eexists; try esplit; try esplit; try esplit;
    try erewrite clos_refl_transE; try left; try esplit.
  3,4,5: eauto.
  auto.
  intros c moxc mocy.
  eapply imm.
  1-2: eapply mo_mo'; eauto.
  left; auto.

  (*  mo base x, isrmw x, sb base y*)
  right; econstructor 1; eexists; esplit; try erewrite clos_refl_transE; try esplit.
  1, 2: eexists; try esplit; try esplit; try esplit;
    try erewrite clos_refl_transE; try left; try esplit.
  3,4,5: eauto.
  auto.
  intros c moxc mocy.
  eapply imm.
  1-2: eapply mo_mo'; eauto.
  left; auto.

  (* base = x, isrmw y *)
  left; auto.
  right; econstructor 1; esplit; eexists; esplit; try eexists; try esplit; try esplit;
    try esplit.
  1-3: auto.
  intros c moxc mocy.
  eapply imm.
  1-2: eapply mo_mo'; eauto.

  (* mo base x, sb base x, isrmw y *)
  left; auto.
  right; econstructor 1; eexists; esplit; try erewrite clos_refl_transE; try esplit.
  1, 2: eexists; try esplit; try esplit; try esplit;
    try erewrite clos_refl_transE; try left; try esplit.
  1-3: eauto.
  intros c moxc mocy.
  eapply imm.
  1-2: eapply mo_mo'; eauto.

  (* mo base x, isrmw x, isrmw y *)
  left; auto.
  right; econstructor 1; eexists; esplit; try erewrite clos_refl_transE; try esplit.
  1, 2: eexists; try esplit; try esplit; try esplit;
    try erewrite clos_refl_transE; try left; try esplit.
  1-3: eauto.
  intros c moxc mocy.
  eapply imm.
  1-2: eapply mo_mo'; eauto.

  apply imm_trans in moxy1.
  apply mo'_mo in moxy1 as (e & f & <- & <- & moxy1).
  apply mo_mo' in moxy1.
  apply imm_trans in moxy2.
  apply mo'_mo in moxy2 as (e' & f' & ef & fz & moxy2).
  apply sig_ext in ef.
  subst e' z.
  apply mo_mo' in moxy2.

  eassert (s1 := IHmoxy1 ?[f] ?[g]).
  [f]: {
    intros z' (e'' & f'' & moef & ee & fz) [fz'|(e''' & f''' & moef' & ez & fy)].
    all: subst z'.
    all: apply sig_ext in ee.
    apply sig_ext in fz'.
    subst e'' f''.
    apply rsCond.
    eexists; eexists; esplit; try esplit.
    1-4: eauto.
    apply sig_ext in ez.
    apply sig_ext in fy.
    subst e'' e''' f'''.
    apply rsCond.
    eexists; eexists; esplit; try esplit.
    2-3: eauto.
    auto.
    right.
    eexists; eexists; esplit; try esplit.
    2-3: eauto.
    apply spo with f; auto.
    apply mo_mo'; auto.
  }
  [g]: {
    apply base_x.
  }
  eassert (s2 := IHmoxy2 ?[f]).
  [f]: {
    intros z' (e'' & f'' & moef & ee' & fz) [fz'|(e''' & f''' & moef' & ez & fy)].
    all: subst z'.
    all: apply sig_ext in ee'.
    apply sig_ext in fz'.
    2: apply sig_ext in ez; apply sig_ext in fy.
    all: subst e'' f''.
    apply rsCond.
    eexists; eexists; esplit; try esplit.
    2-3: eauto.
    apply mo_mo'; apply spo' with (`f); auto.
    left; auto.
    subst f'''.
    apply rsCond.
    eexists; eexists; esplit; try esplit.
    2-3: eauto.
    apply mo_mo' in moef.
    apply mo_mo'.
    apply spo' with (`f); auto.
    right.
    eexists; eexists; esplit; try esplit.
    2-3: eauto.
    auto.
  }
  2-3: auto.

  destruct s1 as [e' [s11 s12]].
  apply clos_refl_transE in s11.
  apply clos_refl_transE in s12.
  destruct s11 as [ee|s11], s12 as [ef|s12].
  1-3: subst e'.
  apply sig_ext in ef.
  subst f.
  exfalso; revert moxy1; apply spo'.

  all: lapply s2; clear s2.
  1,3,5: intros s2.
  1-3: destruct s2 as [e'' [s21 s22]].
  1-3: apply clos_refl_transE in s21.
  1-3: apply clos_refl_transE in s22.
  1-3: destruct s21 as [ee|s21], s22 as [ef|s22].
  1-3,5-7,9-11: subst e''.
  1,4,7: apply sig_ext in ef.
  1-3: subst f.
  1-3: exfalso; revert moxy2; apply spo'.

  (* left: rmw. right: rmw *)
  eexists; esplit; apply clos_refl_transE.
  left; auto.
  right; econstructor 2.
  apply s12.
  apply s22.

  (* left: rmw. right: sb *)
  eexists; esplit; apply clos_refl_transE.
  2: left; auto.
  right.
  apply t_step_rt in s21 as [e' [[y'' [[e'' [s21p (p & p' & [mopp ppimm] & xe & yy)]] [ey sbb]]] s21]].
  subst e' e'' y''.
  apply clos_refl_transE in s21p; destruct s21p as [pp|s21p].
  apply sig_ext in pp; subst p.
  1-2: apply clos_refl_transE in s21; destruct s21 as [pp|s21].
  1,3: apply sig_ext in pp; subst p'.
  econstructor 1; repeat esplit.
  apply clos_refl_transE; right; apply s12.
  1-3: auto.
  econstructor 1; repeat esplit.
  apply clos_refl_transE; right; econstructor 2.
  apply s12.
  apply s21p.
  1-3: auto.
  econstructor 2.
  econstructor 1; repeat esplit.
  apply clos_refl_transE; right.
  apply s12.
  apply mopp.
  1-3: auto.
  econstructor 2.
  2: apply s21.
  econstructor 1; repeat esplit.
  apply clos_refl_transE; right; econstructor 2.
  apply s12.
  apply s21p.
  1-3: auto.

  (* left: sb. right: rmw *)
  eexists; esplit; apply clos_refl_transE; right.
  apply s11.
  apply s22.

  (* left: sb. right: sb *)
  eexists; esplit; apply clos_refl_transE.
  right; econstructor 2.
  apply s11.
  apply s21.
  auto.

  (* left: sb;rmw. right: rmw *)
  eexists; esplit; apply clos_refl_transE.
  right.
  apply s11.
  right.
  econstructor 2.
  apply s12.
  apply s22.
  
  (* left: sb;rmw. right: sb *)
  apply t_step_rt in s21 as [e''' [[y'' [[e'' [s21p (p & p' & [mopp ppimm] & xe & yy)]] [ey sbb]]] s21]].
  subst e''' e'' y''.
  apply clos_refl_transE in s21p; destruct s21p as [pp|s21p].
  apply sig_ext in pp; subst p.
  1-2: apply clos_refl_transE in s21; destruct s21 as [pp|s21].
  1,3: apply sig_ext in pp; subst p'.
  1-4: eexists; esplit; eapply clos_refl_transE.
  2,4,6,8: left; auto.
  1-4: right; econstructor 2.
  apply s11.
  econstructor 1; repeat esplit.
  apply clos_refl_transE; right; apply s12.
  1-3: auto.
  apply s11.
  econstructor 1; repeat esplit.
  apply clos_refl_transE; right; econstructor 2.
  apply s12.
  apply s21p.
  1-3: auto.
  2: apply s21.
  econstructor 2.
  apply s11.
  econstructor 1; repeat esplit.
  apply clos_refl_transE; right.
  apply s12.
  1-3: auto.
  2: apply s21.
  econstructor 2.
  apply s11.
  econstructor 1; repeat esplit.
  apply clos_refl_transE; right; econstructor 2.
  apply s12.
  apply s21p.
  1-3: auto.

  (* left: rmw. right: sb;rmw *)
  apply t_step_rt in s21 as [e''' [[y'' [[e' [s21p (p & p' & [mopp ppimm] & xe & yy)]] [ey sbb]]] s21]].
  subst e''' e' y''.
  apply clos_refl_transE in s21p; destruct s21p as [pp|s21p].
  apply sig_ext in pp; subst p.
  1-2: apply clos_refl_transE in s21; destruct s21 as [pp|s21].
  1,3: subst e''.
  1-4: eexists; esplit; eapply clos_refl_transE.
  right; econstructor 1; repeat esplit.
  apply clos_refl_transE; right.
  apply s12.
  apply mopp.
  1-2: auto.
  right; apply s22.
  right; econstructor 1; repeat esplit.
  apply clos_refl_transE; right; econstructor 2.
  apply s12.
  apply s21p.
  apply mopp.
  1-2: auto.
  right; apply s22.
  right; econstructor 2.
  2: apply s21.
  econstructor 1; repeat esplit.
  apply clos_refl_transE; right.
  apply s12.
  apply mopp.
  1-2: auto.
  right; apply s22.
  right; econstructor 2.
  2: apply s21.
  econstructor 1; repeat esplit.
  apply clos_refl_transE; right; econstructor 2.
  apply s12.
  apply s21p.
  1-3: auto.
  right; apply s22.
  
  (* left: sb. right: sb;rmw *)
  eexists; esplit; apply clos_refl_transE; right.
  econstructor 2.
  apply s11.
  apply s21.
  apply s22.

  (* left: sb;rmw. right: sb;rmw *)
  apply t_step_rt in s21 as [e''' [[y'' [[e'''' [s21p (p & p' & [mopp ppimm] & xe & yy)]] [ey sbb]]] s21]].
  subst e''' e'''' y''.
  apply clos_refl_transE in s21p; destruct s21p as [pp|s21p].
  apply sig_ext in pp; subst p.
  1-2: apply clos_refl_transE in s21; destruct s21 as [pp|s21].
  1,3: subst e''.
  1-4: eexists; esplit; eapply clos_refl_transE.
  right; econstructor 2.
  apply s11.
  econstructor 1; repeat esplit.
  apply clos_refl_transE; right.
  apply s12.
  apply mopp.
  1-2: auto.
  right; apply s22.
  right; econstructor 2.
  apply s11.
  econstructor 1; repeat esplit.
  apply clos_refl_transE; right; econstructor 2.
  apply s12.
  apply s21p.
  apply mopp.
  1-2: auto.
  right; apply s22.
  right; econstructor 2.
  2: apply s21.
  econstructor 2.
  apply s11.
  econstructor 1; repeat esplit.
  apply clos_refl_transE; right.
  apply s12.
  apply mopp.
  1-2: auto.
  right; apply s22.
  right; econstructor 2.
  2: apply s21.
  econstructor 2.
  apply s11.
  econstructor 1; repeat esplit.
  apply clos_refl_transE; right; econstructor 2.
  apply s12.
  apply s21p.
  1-3: auto.
  right; apply s22.

  apply t_rt_step in s12 as [p [_ [p' [_ [pf rmwf]]]]].
  subst p'.
  destruct base_x as [be | [mobe]].
  apply sig_ext in be; subst base.
  right; split.
  auto.
  right; auto.
  right; split.
  apply spo' with (`e); auto.
  right; auto.

  apply t_rt_step in s11 as [p [_ [p' [_ [pf sbf]]]]].
  subst p'.
  destruct base_x as [be | [mobe]].
  apply sig_ext in be; subst base.
  right; split.
  auto.
  auto.
  right; split.
  apply spo' with (`e); auto.
  auto.

  apply t_rt_step in s12 as [p [_ [p' [_ [pf rmwf]]]]].
  subst p'.
  destruct base_x as [be | [mobe]].
  apply sig_ext in be; subst base.
  right; split.
  auto.
  right; auto.
  right; split.
  apply spo' with (`e); auto.
  right; auto.

- assert (tot_mo:
    forall x i c,
      mo'^⋈ x i -> mo'^⋈ x c ->
      i <> c -> mo' i c \/ mo' c i). {
    intros x i c moxi moxc inc.
    destruct moxi as [moxi|moxi], moxc as [moxc|moxc].
    all: apply mo'_mo in moxi as (e & f & xx & yy & moxi).
    all: apply mo'_mo in moxc as (e' & f' & xx' & yy' & moxc).
    all: subst c i x.
    all: try apply sig_ext in xx'.
    all: try apply sig_ext in yy'.
    all: try subst e.
    all: try subst f.
    all: apply mo_same_loc_only in moxi.
    all: apply mo_same_loc_only in moxc.
    all: destruct moxi as [moxi xi], moxc as [moxc xc].
    1,2: rewrite xi in xc; clear xi.
    3,4: rewrite <- xi in xc; clear xi.
    1,3: destruct (mo_total_order_per_loc ((loc ∘ Write_To_ReadWrite) f')) as [_ tot].
    3,4: destruct (mo_total_order_per_loc ((loc ∘ Write_To_ReadWrite) e')) as [_ tot].
    all: edestruct tot.
    2,7,12,17: reflexivity.
    1,5,9,13: try apply xc; try apply (eq_sym xc).
    all: apply mo_mo' in moxi.
    all: apply mo_mo' in moxc.
    1,4,7,10: intros conn; apply inc; apply f_equal; auto.
    all: apply mo_mo' in H.
    all: eauto.
  }
  intros x y [x' [[xz xx] [x'' [[xz' xisrel] [z [xzsb zyrmw]]]]]].
  subst x' x''.
  clear xx.
  remember x as base.
  replace base in xzsb at 1 |-.
  assert (mo_rmw_mo:
    let imo' := (` (immediate mo))%rel in
      (imo' ⨾ ⦗IsRMW⦘)⁺ ⊆ mo' \ (mo' ⨾ ⦗set_compl IsRMW⦘ ⨾ mo'^?)). {
    clear x y z xisrel Heqbase xzsb zyrmw.
    intros imo' x y xyrmw.
    induction xyrmw.
    destruct H as [z' ((x'' & y'' & (moxy & xyimm) & <- & <-) & <- & yrmw)].
    split.
    apply mo_mo'; auto.
    intros (z & moxz & z'' & [<- zrmw] & [->|mozy]).
    auto.
    apply mo'_mo in moxz as (x' & z' & xx & <- & moxz).
    apply mo'_mo in mozy as (z'' & y' & zz & yy & mozy).
    apply sig_ext in xx.
    apply sig_ext in yy.
    apply sig_ext in zz.
    subst x'' y'' z''.
    eapply xyimm; eauto.
    destruct IHxyrmw1 as [moxy yrmw].
    destruct IHxyrmw2 as [moyz zrmw].
    split.
    eapply spo'; eauto.
    intros (y' & moxy' & z'' & [<- allrmw] & [->|moyz']).
    apply zrmw; esplit; esplit.
    2: esplit; esplit.
    3: left; auto.
    2: esplit; eauto.
    auto.
    destruct (classic (y = y')) as [<-|yneq].
    apply yrmw; esplit; esplit.
    2: esplit; esplit.
    3: left; auto.
    2: esplit; eauto.
    auto.
    destruct (tot_mo x y y'); unfold clos_sym; auto.
    apply zrmw; esplit; esplit.
    2: esplit; esplit.
    3: right.
    2: esplit; eauto.
    1-2: eauto.
    apply yrmw; esplit; esplit.
    2: esplit; esplit.
    3: right.
    2: esplit; eauto.
    1-2: eauto.
  }
  assert (mo_sb_mo:
    let imo' := (` (immediate mo))%rel in
      (((imo' ⨾ ⦗IsRMW⦘)＊ ⨾ imo') ⨾ ⦗sb^⋈ base⦘)⁺ ⊆
      mo' \ (mo' ⨾ ⦗set_compl (IsRMW ∪₁ sb^⋈ base)⦘ ⨾ mo'^?)). {
    clear x y z xisrel Heqbase xzsb zyrmw.
    intros imo' x y xyrmw.
    induction xyrmw.
    destruct H as [z' [[z'' [zrmw (z & y' & [moxy imm] & <- & <-)]] [<- zsb]]].
    apply clos_refl_transE in zrmw as [->|zrmw].
    split.
    apply mo_mo'; auto.
    intros (e & moxy' & z'' & [<- allrmw] & [->|moyz']).
    apply allrmw.
    right; auto.
    apply mo'_mo in moxy' as (z' & e' & xx & <- & moxy').
    apply mo'_mo in moyz' as (e'' & y'' & zz & yy & moyz').
    apply sig_ext in xx.
    apply sig_ext in yy.
    apply sig_ext in zz.
    subst z' e'' y''.
    eapply imm; eauto.
    lapply (mo_rmw_mo x (`z)).
    intros (z' & moxz).
    split.
    eapply spo'.
    apply z'.
    apply mo_mo'; auto.
    intros (e & moxy' & z'' & [<- allrmw] & [->|moyz']).
    apply allrmw.
    right; auto.
    destruct (classic (e = `z)) as [->|yneq].
    apply moxz; esplit; esplit.
    2: esplit; esplit.
    3: left; auto.
    2: esplit; eauto.
    2: intros nrmw; apply allrmw; left; auto.
    auto.
    destruct (tot_mo x e (`z)); unfold clos_sym; auto.
    apply moxz; esplit; esplit.
    2: esplit; esplit.
    3: right.
    2: esplit; eauto.
    apply moxy'.
    intros nrmw; apply allrmw; left; auto.
    auto.
    apply mo'_mo in H as (z'' & e' & xx & <- & H).
    apply mo'_mo in moyz' as (e'' & y'' & zz & yy & moyz').
    apply sig_ext in xx.
    apply sig_ext in yy.
    apply sig_ext in zz.
    subst e'' y'' z''.
    eapply imm; eauto.
    auto.
    destruct IHxyrmw1 as [moxy yrmw].
    destruct IHxyrmw2 as [moyz zrmw].
    split.
    eapply spo'; eauto.
    intros (y' & moxy' & z'' & [<- allrmw] & [->|moyz']).
    apply zrmw; esplit; esplit.
    2: esplit; esplit.
    3: left; auto.
    2: esplit; eauto.
    auto.
    destruct (classic (y = y')) as [<-|yneq].
    apply yrmw; esplit; esplit.
    2: esplit; esplit.
    3: left; auto.
    2: esplit; eauto.
    auto.
    destruct (tot_mo x y y'); unfold clos_sym; auto.
    apply zrmw; esplit; esplit.
    2: esplit; esplit.
    3: right.
    2: esplit; eauto.
    1-2: eauto.
    apply yrmw; esplit; esplit.
    2: esplit; esplit.
    3: right.
    2: esplit; eauto.
    1-2: eauto.
  }
  apply clos_refl_transE in xzsb.
  apply clos_refl_transE in zyrmw.
  destruct xzsb as [<-|xzsb], zyrmw as [<-|zyrmw].

  all: repeat try esplit.
  all: auto.
  1,3,5,7: intros z' (e & f & moxy & ee & ff) [<-|(e' & f' & moyz & ff' & gg)].
  1-8:subst base z'.

  apply sig_ext in ff; subst e.
  exfalso; eapply spo; eauto.

  subst x.
  apply sig_ext in ff'; subst e'.
  apply sig_ext in gg; subst e.
  exfalso; eapply spo; eapply spo; eauto.

  subst x.
  lapply (mo_rmw_mo (`e) (`f)).
  intros (moef & allzyrmw).
  apply NNPP; intros nrmw.
  apply allzyrmw.
  esplit; esplit.
  eauto.
  esplit; esplit.
  esplit; eauto.
  intros nrmw2; apply nrmw; auto.
  left; auto.
  auto.

  subst x y.
  apply sig_ext in ff'; subst e'.
  lapply (mo_rmw_mo (`e) (`f')).
  intros (moef & allzyrmw).
  apply NNPP; intros nrmw.
  apply allzyrmw.
  esplit; esplit.
  eapply mo_mo'; eauto.
  esplit; esplit.
  esplit; eauto.
  intros nrmw2; apply nrmw; auto.
  right; eapply mo_mo'; eauto.
  auto.
  
  subst x.
  lapply (mo_sb_mo (`e) (`f)).
  intros (moef & allxzsb).
  apply NNPP; intros nrmw.
  apply allxzsb.
  esplit; esplit.
  eauto.
  esplit; esplit.
  esplit; eauto.
  intros [nrmw2|nrmw2]; apply nrmw; auto.
  left; auto.
  auto.

  subst x z.
  apply sig_ext in ff'; subst e'.
  lapply (mo_sb_mo (`e) (`f')).
  intros (moef & allxzsb).
  apply NNPP; intros nrmw.
  apply allxzsb.
  esplit; esplit.
  eapply mo_mo'; eauto.
  esplit; esplit.
  esplit; eauto.
  intros [nrmw2|nrmw2]; apply nrmw; auto.
  right; eapply mo_mo'; eauto.
  auto.

  subst x.
  lapply (mo_sb_mo (`e) z).
  intros (moez & allxzsb).
  lapply (mo_rmw_mo z (`f)).
  intros (mozf & allzyrmw).
  apply NNPP; intros nrmw.
  apply allzyrmw.
  esplit; esplit.
  eauto.
  esplit; esplit.
  esplit; eauto.
  intros nrmw2; apply nrmw; auto.
  left; auto.
  1-2: auto.

  subst x y.
  apply sig_ext in ff'; subst e'.
  lapply (mo_sb_mo (`e) z).
  intros (moez & allxzsb).
  lapply (mo_rmw_mo z (`f')).
  intros (mozf & allzyrmw).
  apply NNPP; intros nrmw.
  destruct (classic (`f = z)) as [<-|neq].

  apply allxzsb.
  esplit; esplit.
  eauto.
  esplit; esplit.
  esplit; eauto.
  intros [nrmw2|nrmw2]; apply nrmw; auto.
  left; auto.

  destruct (tot_mo (`e) z (`f)); unfold clos_sym; auto.
  left; apply mo_mo'; auto.
  apply allzyrmw.
  esplit; esplit.
  eauto.
  esplit; esplit.
  esplit; eauto.
  intros nrmw2; apply nrmw; auto.
  right; apply mo_mo'; auto.

  apply allxzsb.
  esplit; esplit.
  eapply mo_mo'; eauto.
  esplit; esplit.
  esplit; eauto.
  intros [nrmw2|nrmw2]; apply nrmw; auto.
  right; auto.
  1-2: auto.

  right.
  lapply (mo_rmw_mo x y).
  intros (moxy & allzyrmw).
  apply mo'_mo in moxy as (z' & e' & <- & <- & moxy).
  eauto.
  auto.

  right.
  lapply (mo_sb_mo x z).
  intros (moxz & allxzsb).
  apply mo'_mo in moxz as (z' & e' & <- & <- & moxy).
  eauto.
  auto.

  right.
  lapply (mo_rmw_mo z y).
  intros (mozy & allzyrmw).
  apply mo'_mo in mozy as (z' & f' & <- & <- & mozy).
  lapply (mo_sb_mo x (`z')).
  intros (moxz & allxzsb).
  apply mo'_mo in moxz as (e' & z'' & <- & yy & moxz).
  apply sig_ext in yy; subst z''.
  cut (mo e' f').
  intros moef; eauto.
  eapply spo; eauto.
  1-2: auto.
Qed.
