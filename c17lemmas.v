Lemma sw_acy: acyclic sw.
Proof.
  destruct (mo_total_order_per_loc 0) as [spo _].
  assert (sw⁺ ⊆ (`mo)^?%rel ⨾ rf).
    intros x y swxy.
    induction swxy.
    destruct H as (x' & [<- xrel] & e & ers & y' & yrf & [-> yacq]).
    esplit; esplit.
    2: eauto.
    destruct ers as [<-|[(x' & [<- xrel2] & moxe) _]].
    left; auto.
    auto.
    destruct IHswxy1 as (e & moxe & rfy).
    destruct IHswxy2 as (f & moyf & rfz).
    destruct (rfy) as (eiw & yir & _).
    destruct moyf as [<-|moyf].
    
    destruct (rfz) as (yiw & zir & _).
    assert (yrmw: IsRMW y).
      unfold IsRead in yir.
      unfold IsWrite in yiw.
      unfold IsRMW.
      destruct (`y).
      1-4: compute in yir, yiw; try discriminate yir; try discriminate yiw.
      reflexivity.
    lapply (rmw_atomic e y).
    intros moey.
    esplit; esplit.
    2: apply rfz.
    right.
    destruct moey as (e' & f' & [moey _] & <- & <-).
    destruct moxe as [->|(d' & e'' & moxe & <- & ff)].
    repeat esplit; auto.
    apply sig_ext in ff; subst e''.
    repeat esplit.
    apply spo with e'; auto.
    esplit; esplit; eauto.
    esplit; eauto.

    destruct moyf as (e' & f' & moyf & <- & <-).
    assert (yrmw: IsRMW (`e')).
      destruct e' as [e' yiw].
      unfold IsRead in yir.
      unfold IsWrite in yiw.
      unfold IsRMW.
      simpl in *.
      clear moyf.
      destruct (`e').
      1-4: compute in yir, yiw; try discriminate yir; try discriminate yiw.
      reflexivity.
    lapply (rmw_atomic e (`e')).
    intros moey.
    esplit; esplit.
    2: apply rfz.
    right.
    destruct moey as (e'' & f'' & [moey _] & <- & ff).
    apply sig_ext in ff; subst f''.
    destruct moxe as [->|(d' & e''' & moxe & <- & ff)].
    repeat esplit.
    apply spo with e'; auto.
    apply sig_ext in ff; subst e'''.
    repeat esplit.
    apply spo with e'; auto.
    apply spo with e''; auto.
    esplit; esplit; eauto.
    esplit; eauto.
  intros x rxx.
  apply H in rxx.
  destruct rxx as (e & moxe & rfx).
  destruct moxe as [<-|(e' & f' & moey & <- & <-)].
  apply rf_acy with x; constructor 1; auto.
  assert (yrmw: IsRMW (`e')).
    destruct e' as [e' yiw].
    destruct rfx as [_ [yir _]].
    unfold IsRead in yir.
    unfold IsWrite in yiw.
    unfold IsRMW.
    simpl in *.
    clear moey.
    destruct (`e').
    1-4: compute in yir, yiw; try discriminate yir; try discriminate yiw.
    reflexivity.
  lapply (rmw_atomic (`f') (`e')).
  intros (e'' & f'' & [mofe _] & ee & ff).
  apply sig_ext in ee; subst e''.
  apply sig_ext in ff; subst f''.
  apply spo with e'; apply spo with f'; auto.
  esplit; esplit; eauto.
  esplit; eauto.
Qed.