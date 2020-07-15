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

Declare Scope relation_scope.

Require Import List Program RelationClasses.
From hahn Require Import Hahn.

Notation " `↑ r " := ((@proj1_sig _ _) ↑ r) (at level 30): function_scope.
Notation " `↓ r " := ((@proj1_sig _ _) ↓ r) (at level 30) : function_scope.
Notation " `↑₁ s " := ((@proj1_sig _ _) ↑₁ s) (at level 30) : function_scope.
Notation " `↓₁ s " := ((@proj1_sig _ _) ↓₁ s) (at level 30) : function_scope.

Delimit Scope function_scope with rel.

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

Inductive Mode := 
| mPln
| mRlx
| mCns
| mAcq
| mRel
| mAcqRel
| mSc.

(*
My interpretation of atomic/non-atomic interactions in current standard:
 - Atomic objects have non-atomic initialization followed by atomic operations
 - Non-atomic objects don't have atomic operations
 - Multiple objects can coexist in a memory location, causing races

INIT:

The value of an object visible to a thread T at a particular point is the initial value of the object, a value
assigned to the object by T, or a value assigned to the object by another thread, according to the rules
below.

Variables with static storage duration are initialized as a consequence of program initiation. Variables with
thread storage duration are initialized as a consequence of thread execution. Within each of these phases of
initiation, initialization occurs as follows.

Together, zero-initialization and constant initialization are called static initialization;
all other initialization is dynamic initialization.

All static initialization strongly happens before (4.7.1) any dynamic initialization. [ Note: The dynamic
initialization of non-local variables is described in 6.6.3; that of local static variables is described in
9.7. — end note ]

I model this as
 - all objects can have atomic/non-atomic operations
 - every read must have a corresponding write - initializations are provided as writes
*)

Definition Loc := nat.
Definition Thread := nat.

Inductive Op' :=
| write (uid: nat) (t: Thread) (m: Mode | In m [mPln;mRlx;mRel;mAcqRel;mSc]) (l: Loc)
| read (uid: nat) (t: Thread) (m: Mode | In m [mPln;mRlx;mCns;mAcq;mAcqRel;mSc]) (from: Op')
| fence (uid: nat) (t: Thread) (m: Mode | In m [mAcq;mRel;mAcqRel;mSc])
| rmw (uid: nat) (t: Thread) (m: Mode | In m [mPln;mAcq;mRel;mAcqRel;mSc]) (from: Op').

Definition IsRead' (o: Op') :=
  match o with
    read _ _ _ _
  | rmw _ _ _ _ => true
  | _ => false
  end.
Definition IsWrite' (o: Op') :=
  match o with
    write _ _ _ _
  | rmw _ _ _ _ => true
  | _ => false
  end.
Definition IsFence' (o: Op') :=
  match o with
    fence _ _ _ => true
  | _ => false
  end.
Definition IsRMW' (o: Op') :=
  match o with
    rmw _ _ _ _ => true
  | _ => false
  end.

Program Definition from' (o: Op' | IsRead' o) :=
  match `o as o'
    return IsRead' o' -> Op'
  with
    write _ _ _ _
  | fence _ _ _ => _
  | read _ _ _ f
  | rmw _ _ _ f => fun _ => f
  end (proj2_sig o).

Definition thread' (o: Op') :=
match o with
  read _ t _ _
| write _ t _ _
| fence _ t _
| rmw _ t _ _ => t
end.

Definition mode' (o: Op') :=
  match o with
    read _ _ (exist _ m _) _
  | write _ _ (exist _ m _) _
  | fence _ _ (exist _ m _)
  | rmw _ _ (exist _ m _) _ => m
  end.

Definition IsAtomic' (o': Op') := mode' o' <> mPln.

Conjecture events': Op' -> Prop.
Conjecture events'_finite: set_finite events'.

Program Fixpoint OP_WF (o: Op'): Prop :=
  ⟪op_event: events' o⟫ /\
  ⟪op_reads_from_write: forall s: IsRead' o, IsWrite' (from' o)⟫ /\
  ⟪op_from_wf': forall s: IsRead' o, OP_WF (from' o)⟫.

Definition loc'
  (o: Op')
  (NF: ~IsFence' o)
  (wf: OP_WF o): Loc.
Proof.
  pose (truth_hurts :=
    fun (P: true = true -> Type)
        (f: forall e: true = true, P e) =>
        f eq_refl).
  induction o.
  apply l.
  2: contradict NF; reflexivity.
  all: destruct wf as (ev & rfw%truth_hurts & fwf%truth_hurts).
  all: apply IHo; destruct o; auto.
Defined.

Definition Op := { o: Op' | OP_WF o }.

Definition thread (o: Op) :=
  thread' (`o).

Definition mode (o: Op) :=
  mode' (`o).

Definition IsAtomic (o: Op) := IsAtomic' (`o).
Definition IsRead (o: Op) := IsRead' (`o).
Definition IsWrite (o: Op) := IsWrite' (`o).
Definition IsFence (o: Op) := IsFence' (`o).
Definition IsRMW (o: Op) := IsRMW' (`o).

Definition Read := { o: Op | IsRead o }.
Definition Write := { o: Op | IsWrite o }.
Definition Fence := { o: Op | IsFence o }.
Definition ReadWrite := { o: Op | ~IsFence o }.

Definition AR2RW (o: Read): ReadWrite.
Proof.
  destruct o as [owf r].
  exists owf.
  destruct owf as [[]].
  all: repeat split; auto.
Defined.

Definition AW2RW (o: Write): ReadWrite.
Proof.
  destruct o as [owf w].
  exists owf.
  destruct owf as [[]].
  all: repeat split; auto.
Defined.

Lemma AW2RW_inj: forall x y, AW2RW x = AW2RW y -> x = y.
Proof.
  intros x y axay.
  apply (f_equal (@proj1_sig _ _)) in axay.
  apply sig_ext.
  destruct x as [[[] xwf] xw], y as [[[] ywf] yw]; auto.
Qed.

Lemma AR2RW_inj: forall x y, AR2RW x = AR2RW y -> x = y.
Proof.
  intros x y axay.
  apply (f_equal (@proj1_sig _ _)) in axay.
  apply sig_ext.
  destruct x as [[[] xwf] xw], y as [[[] ywf] yw]; auto.
Qed.

Definition IsPln (o: Op) := mode o = mPln.
Definition IsCns (o: Op) := mode o = mCns.
Definition IsRel (o: Op) := In (mode o) [mRel;mAcqRel;mSc].
Definition IsAcq (o: Op) := In (mode o) [mAcq;mAcqRel;mSc].
Definition IsSC (o: Op) := mode o = mSc.

(*
Program Fixpoint loc' (o: Op') (WF: OP_WF o) (NF: ~IsFence' o) :=
  match o as o'
    return ~IsFence' o' -> OP_WF o' -> Loc
  with
    write _ l => fun _ _ => l
  | read _ f
  | rmw _ f => fun _ '(conj _ (conj rfw fwf)) => loc' f _ _
  | fence _ => fun NF' WF' => !(NF' eq_refl)
  end NF WF.
Next Obligation.
  apply fwf; auto.
Qed.
Next Obligation.
  destruct f; auto.
  discriminate (rfw eq_refl).
Qed.
Next Obligation.
  apply fwf; auto.
Qed.
Next Obligation.
  destruct f; auto.
  discriminate (rfw eq_refl).
Qed.
*)

Program Definition loc (o: ReadWrite) :=
  loc' (``o) _ _.
Next Obligation.
  destruct o as [[o wf] nf]; auto.
Defined.
Next Obligation.
  destruct o as [[o wf] nf]; auto.
Defined.

Program Definition from (o: Read): Write :=
  from' (``o).
Next Obligation. (* IsRead' (``o) *)
  case (o) as [[o' wf] r]; auto.
Defined.
Next Obligation. (* OP_WF (from' (``o)) *)
  case (o) as [[[] (wf' & atom & fwf)]].
  all: apply fwf.
Defined.
Next Obligation. (* IsWrite (from' (``o)) *)
  pose (o' := ``o).
  destruct o as [[[] wf] ir].
  all: destruct wf as (ev & rfw & fwf).
  all: unfold IsAtomic in *; simpl in ir, o' |- *.
  1,3: discriminate ir.
  all: specialize (rfw eq_refl) as rfw_.
  all: specialize (fwf eq_refl) as fwf_.
  all: assumption.
Defined.

Lemma from_eq: forall x p1 p2, from' (exist _ x p1) = from' (exist _ x p2).
Proof.
  intros x p1 p2.
  assert (H: p1 = p2) by apply proof_irrelevance.
  rewrite H; auto.
Qed.

Lemma from_eq_loc: forall x: Read, loc (AR2RW x) = loc (AW2RW (from x)).
Proof.
  assert (H: forall x p1 p2 p3 p4, loc' x p1 p3 = loc' x p2 p4).
    intros.
    f_equal; apply proof_irrelevance.
  intros [[[] (ev & rfw & fwf)] xir]; try discriminate xir.
  all: unfold loc, loc' at 1; cbv - [loc'].
  all: apply H.
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

(*
SB:
Sequenced before is an asymmetric, transitive, pair-wise relation between evaluations executed by a single
thread, which induces a partial order among those evaluations.
*)

Conjecture sb: relation Op.
Conjecture sb_order: strict_partial_order sb.
Conjecture sb_same_thread: funeq thread sb.

(*
Do we need to model threads? 2 actions on the same thread are not "potentially concurrent" unless in a signal handler,
so if they are unsequenced and conflict it's undefined. So 2 reads to the same location, or 2 actions on different
locations, can be unsequenced.
*)

(*
MO:
All modifications to a particular atomic object M occur in some particular total order, called the modification
order of M. [ Note: There is a separate order for each atomic object. There is no requirement that these can
be combined into a single total order for all objects. In general this will be impossible since different threads
may observe modifications to different objects in inconsistent orders. — end note ]

Can we include non-atomic objects in this? Are mo constraints implied by visible side effect?
*)

Conjecture mo: relation Write.
Conjecture mo_same_loc_only: funeq (loc ∘ AW2RW) mo.
Conjecture mo_total_order_per_loc: forall l: Loc, strict_total_order ((loc ∘ AW2RW) ↓₁ eq l) mo.

(*
RS:
A release sequence headed by a release operation A on an atomic object M is a maximal contiguous subsequence of
side effects in the modification order of M, where the first operation is A, and every subsequent operation
 — is performed by the same thread that performed A, or
 — is an atomic read-modify-write operation.
*)

(* for non-release writes *)
Definition rs_fence :=
  fun x y =>
    (⦗`↓₁ IsAtomic⦘ ⨾ mo^?) x y /\
    forall z, mo x z -> mo^? z y ->
      thread (`x) = thread (`z) \/ IsRMW (`z).

Definition rs := ⦗`↓₁ IsRel⦘ ⨾ rs_fence.

(*
READ FROM
*)

Program Definition rf: relation ReadWrite :=
  fun w r => 
    exists (ir: IsRead (`r)), w = AW2RW (from (`r)).
Next Obligation.
  destruct r as [[]]; auto.
Defined.

Lemma rf_write: forall x y, rf x y -> IsWrite (`x).
Proof.
  intros x y [xir rfxy].
  do 2 apply (f_equal (@proj1_sig _ _)) in rfxy; cbn in rfxy.
  destruct y as [[[] (ev & rfw & fwf)]]; try discriminate.
  all: specialize (rfw eq_refl) as rfw'; cbn in rfw', rfxy.
  all: unfold IsWrite.
  all: subst from0; assumption.
Qed.

Lemma rf_eq_loc: forall x y, rf x y -> loc x = loc y.
Proof.
  intros x y [yir rfxy].
  subst x; symmetry.
  assert (y = AR2RW (exist _ (`y) yir)).
    apply sig_ext; reflexivity.
  replace y at 1.
  assert (yeq: forall o1 o2, exist (fun x => IsRead x) (`y) yir = (exist _ (exist _ (``y) o1) o2)).
    intros o1 o2.
    do 2 apply sig_ext; simpl.
    reflexivity.
  rewrite <- yeq.
  apply from_eq_loc.
Qed.

(*
RMW-ATOMIC:
Atomic read-modify-write operations shall always read the last value (in the modification order) written
before the write associated with the read-modify-write operation.
*)

Conjecture rmw_atomic: `↑ rf ⨾ ⦗IsRMW⦘ ⊆ `↑ (immediate mo).

(* rf is made acyclic by our inductive definition *)

Lemma rf_acy: acyclic rf.
Proof.
  assert (d:
    forall x y, rf⁺ x y ->
      rf x y \/ exists (ir: IsRead (`y)), rf⁺ x (AW2RW (from (exist _ (`y) ir)))).
    intros x y rxy.
    induction rxy.
    left; auto.
    right.
    destruct IHrxy2 as [(ir & ryz)|[ir ryz]].
    assert (zeq: exist (fun o : Op' => OP_WF o) (`` z) (rf_obligation_1 z ir) = `z).
      apply sig_ext.
      auto.
    assert (zeq2:
      exist _
        (exist (fun o : Op' => OP_WF o) (`` z) (rf_obligation_1 z ir))
        (rf_obligation_2 z ir) =
      exist _
        (`z)
        (eq_rect _ (fun x => IsRead x) (rf_obligation_2 z ir) _ zeq)).
      apply sig_ext.
      apply sig_ext.
      auto.
    assert (ryz2 := eq_rect _ (fun x => y = AW2RW (from x)) ryz _ zeq2).
    hnf in ryz2.
    rewrite ryz2 in rxy1.
    eexists; eauto.
    exists ir.
    constructor 2 with y; auto.
  intros x rxx.
  remember rxx as rxy.
  remember x as y in rxy at 2.
  clear Heqy Heqrxy.
  destruct y as [[y wf] yrw].
  induction y.

  specialize (d _ _ rxy) as [(ir & deq)|(ir & rxf)].
  1,2: discriminate ir.

  specialize (d _ _ rxy) as [(ir & deq)|(ir & rxf)].
  unfold from, from' in deq; simpl in deq.
  eapply IHy.
  replace x in rxx at 2.
  eauto.
  unfold from, from' in rxf; simpl in rxf.
  eapply IHy.
  eauto.

  specialize (d _ _ rxy) as [(ir & deq)|(ir & rxf)].
  1,2: discriminate ir.

  specialize (d _ _ rxy) as [(ir & deq)|(ir & rxf)].
  unfold from, from' in deq; simpl in deq.
  eapply IHy.
  replace x in rxx at 2.
  eauto.
  unfold from, from' in rxf; simpl in rxf.
  eapply IHy.
  eauto.
Qed.

(* in the C++ standard rf is acyclic due to rmw_atomic *)

Lemma rf_acy_by_rmw: acyclic rf.
Proof.
  assert (rfmo: forall x y, rf⁺ x y -> IsWrite (`x) /\ ((`↑ mo) (`x) (`y) \/ ~IsWrite (`y))).
    intros x y rxy.
    induction rxy as [x y rxy|x e y rxe [xiw [(x' & e' & moxe & xx & ee)|enw]]
                                    rey [eiw [(e'' & y' & moey & ee' & yy)|ynw]]].
    assert (xiw := rf_write _ _ rxy).
    split; [assumption|].
    set (y' := y).
    destruct (rxy) as [yir _], y as [[[]]]; try discriminate.
    1-2: cbn in yir |- *.
    1-2: auto.
    destruct (rmw_atomic (`x) (`y')) as (x' & y'' & [moxy imm] & xx & yy).
    do 3 esplit; eauto.
    left; repeat esplit; eauto.
    1-4: try contradiction; split; auto.
    rewrite <- ee' in ee; apply sig_ext in ee; subst e''.
    left; repeat esplit.
    eapply (mo_total_order_per_loc 0).
    3-4: eauto.
    1-2: eauto.
  intros x rxx.
  specialize (rfmo _ _ rxx) as [xiw [(x' & x'' & moxx & xx & xx')|xnw]].
  rewrite <- xx' in xx; apply sig_ext in xx; subst x''.
  eapply (mo_total_order_per_loc 0); eauto.
  contradiction.
Qed.

(*
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

Assume the operator conditions are modelled as chain of read-froms
*)

Definition cd := (rf ∩ (`↓ sb))⁺.

(*
DOB:
An evaluation A is dependency-ordered before an evaluation B if
 — A performs a release operation on an atomic object M, and, in another thread, B performs a consume
operation on M and reads a value written by any side effect in the release sequence headed by A, or
 — for some evaluation X, A is dependency-ordered before X and X carries a dependency to B.
[ Note: The relation “ is dependency-ordered before” is analogous to “ synchronizes with”, but uses release/ -
consume in place of release/acquire. — end note ]
*)

Definition dob := AW2RW ↑ rs ⨾ rf ⨾ ⦗`↓₁ IsCns⦘ ⨾ cd^?.

(*
SW_FENCE:
This section introduces synchronization primitives called fences. Fences can have acquire semantics, release
semantics, or both. A fence with acquire semantics is called an acquire fence. A fence with release semantics
is called a release fence.

A release fence A synchronizes with an acquire fence B if there exist atomic operations X and Y, both
operating on some atomic object M, such that A is sequenced before X, X modifies M, Y is sequenced before
B, and Y reads the value written by X or a value written by any side effect in the hypothetical release
sequence X would head if it were a release operation.

A release fence A synchronizes with an atomic operation B that performs an acquire operation on an atomic
object M if there exists an atomic operation X such that A is sequenced before X, X modifies M, and B
reads the value written by X or a value written by any side effect in the hypothetical release sequence X
would head if it were a release operation.

An atomic operation A that is a release operation on an atomic object M synchronizes with an acquire fence
B if there exists some atomic operation X on M such that X is sequenced before B and reads the value
written by A or a value written by any side effect in the release sequence headed by A.

SW:
Certain library calls synchronize with other library calls performed by another thread. For example, an
atomic store-release synchronizes with a load-acquire that takes its value from the store (32. 4). [ Note: Except
in the specified cases, reading a later value does not necessarily ensure visibility as described below. Such a
requirement would sometimes interfere with efficient implementation. —end note ] [ Note: The specifications
of the synchronization operations define when one reads the value written by another. For atomic objects ,
the definition is clear. All operations on a given mutex occur in a single total order. Each mutex acquisition
“ reads the value written” by the last mutex release. — end note ]

SW:
An atomic operation A that performs a release operation on an atomic object M synchronizes with an atomic
operation B that performs an acquire operation on M and takes its value from any side effect in the release
sequence headed by A.
*)

Definition sw :=
  ⦗IsRel⦘ ⨾ (⦗IsFence⦘ ⨾ sb)^? ⨾ `↑ rs_fence ⨾ `↑ rf ⨾ ⦗IsAtomic⦘ ⨾ (sb ⨾ ⦗IsFence⦘)^? ⨾ ⦗IsAcq⦘.

(*
ITHB:
An evaluation A inter-thread happens before an evaluation B if
 — A synchronizes with B, or
 — A is dependency-ordered before B, or
 — for some evaluation X
   — A synchronizes with X and X is sequenced before B, or
   — A is sequenced before X and X inter- thread happens before B, or
   — A inter-thread happens before X and X inter-thread happens before B.

Definition is structurally recursive so requires an inductive type.
But how to prove its acyclicity in the absence of a structural definition?
Should not matter - an instance of ithhb is well-founded but that doesnt prove the whole relation is
*)

Inductive ithb (x y: Op): Prop :=
  ithb_sw (r: sw x y)
| ithb_dob (r: (`↑ dob) x y)
| ithb_sw_sb (r: (sw ⨾ sb) x y)
| ithb_sb_ithb (r: (sb ⨾ ithb) x y)
| ithb_ithb_ithb (r: (ithb ⨾ ithb) x y).

Fixpoint ithb_my_ind
    (P : Op -> Op -> Prop)
    (sw_rec: forall x y, sw x y -> P x y)
    (dob_rec: forall x y, (`↑ dob) x y -> P x y)
    (swsb_rec: forall x y, (sw ⨾ sb) x y -> P x y)
    (sbithb_rec: forall x y e,
      sb x e ->
      ithb e y ->
      P e y ->
      P x y)
    (ithbithb_rec: forall x y e,
      ithb x e ->
      ithb e y ->
      P x e ->
      P e y ->
      P x y)
    (x y : Op)
    (i: ithb x y):
    P x y :=
  let rec := ithb_my_ind P sw_rec dob_rec swsb_rec sbithb_rec ithbithb_rec in
  match i
  with
    ithb_sw _ _ r => sw_rec x y r
  | ithb_dob _ _ r => dob_rec x y r
  | ithb_sw_sb _ _ r => swsb_rec x y r
  | ithb_sb_ithb _ _ (ex_intro _ e (conj rxe rey)) => sbithb_rec x y e rxe rey (rec e y rey)
  | ithb_ithb_ithb _ _ (ex_intro _ e (conj rxe rey)) => ithbithb_rec x y e rxe rey(rec x e rxe) (rec e y rey)
  end.

(*
[ Note: The “ inter-thread happens before” relation describes arbitrary concatenations of “sequenced before”,
“synchronizes with” and “dependency-ordered before” relationships, with two exceptions. The first exception
is that a concatenation is not permitted to end with “dependency-ordered before” followed by “sequenced
before”. The reason for this limitation is that a consume operation participating in a “dependency-ordered
before” relationship provides ordering only with respect to operations to which this consume operation
actually carries a dependency. The reason that this limitation applies only to the end of such a concatenation
is that any subsequent release operation will provide the required ordering for a prior consume operation.
The second exception is that a concatenation is not permitted to consist entirely of “sequenced before”. The
reasons for this limitation are (1) to permit “inter- thread happens before” to be transitively closed and (2)
the “happens before” relation, defined below, provides for relationships consisting entirely of “sequenced
before”. — end note ]

This is a constraint on the construction of the path in sb ∪ dob ∪ sw.
- Define the union and its transitive closure outside Prop
- Express it's construction as a list
- Define relations on the construction of the transitive closure
  - relations on indices of the list

Rather more difficult than anticipated.
*)

Inductive clos_trans_t {A : Type} (R : A -> A -> Type) (x : A) : A -> Type :=
	t_step_t : forall y : A, R x y -> clos_trans_t R x y
| t_trans_t : forall y z : A, clos_trans_t R x y -> clos_trans_t R y z -> clos_trans_t R x z.

Lemma ithb_alt
  (tc_to_l :=
    fun {A} {r: A -> A -> Type} {x} {y} (rxyp: clos_trans_t r x y) =>
      (fix f {x} {y} (rxy: clos_trans_t r x y) :=
        match rxy with
          t_step_t _ _ y rxy => [existT (fun '(x, y) => r x y) (x, y) rxy] 
        | t_trans_t _ _ e y rxe rey => f rxe ++ f rey
        end) _ _ rxyp)
  (list_rel :=
    fun {A} {r: A -> A -> Type}
        (f: forall {x} {y}, r x y -> Prop)
        (l: list {xy: A*A & let (x, y) := xy in r x y})
        n o =>
      n < length l /\
      S n = o /\
      match nth_error l n with
        Some (existT _ (x, y) rxy) =>
          f rxy
      | None => False
      end)
  (ithb_r := fun x y => let dobc := `↑ dob in {sb x y} + {sw x y} + {dobc x y})
  (is_sb := list_rel
    (fun x y (rxy: ithb_r x y) =>
       match rxy with
        inleft (left _) => True
       | _ => False
       end))
  (is_dob := list_rel
    (fun x y (rxy: ithb_r x y) =>
       if rxy then False else True)):
  ithb ≡
    fun x y =>
      exists rxy: clos_trans_t ithb_r x y,
        let l := tc_to_l rxy in
        let lsb := is_sb l in
        let ldob := is_dob l in
        let lstart n := n = O in
        let lend n := n = (length l) in
        ldob ⨾ lsb⁺ ⨾ ⦗lend⦘ ∪
        ⦗lstart⦘ ⨾ lsb⁺ ⨾ ⦗lend⦘ ⊆ ∅₂.
Proof.
  assert (len_1: forall A r x y rxy, length (tc_to_l A r x y rxy) >= 1).
    intros A r f g rxy.
    induction rxy; simpl; auto with *.
    rewrite app_length.
    auto with *.

  assert (sb_lt: forall x y l, (is_sb l)⁺ x y -> x < y).
    intros f g l' rfg.
    induction rfg as [f g (lfl & sfg & fval)|].
    destruct g; simpl in sfg; auto with *.
    auto with *.

  assert (is_sb_ext:
    forall l1 l2 f g,
      f < g ->
      g > length l1 ->
      (is_sb (l1 ++ l2))⁺ f g ->
      (is_sb l2)⁺ (f - length l1) (g - length l1)).
    intros l1 l2.
    induction l1.
    intros f g fc gc sbfg.
    simpl in fc, gc, sbfg |- *; auto with *.
    do 2 rewrite PeanoNat.Nat.sub_0_r.
    assumption.
    intros f g fc gc sbfg.
    destruct g; [eauto with *|].
    simpl in fc, gc, sbfg |- *.
    destruct f.
    apply (IHl1 0); auto with *.
    2: apply (IHl1 f); auto with *.
    apply t_step_rt in sbfg as (f & (len0 & s0f & val0) & [->|sbfg]%clos_refl_transE); auto with *.
    subst f.
    clear len0 gc fc val0.
    set (f := 0) in |- *.
    set (f' := 1) in sbfg.
    assert (ff: f' = S f) by auto.
    remember (S g) as g' eqn: gg in sbfg.
    clearbody f f'.
    2: clear fc gc.
    2: remember (S f) as f' eqn: ff in sbfg.
    2: remember (S g) as g' eqn: gg in sbfg.
    1-2: revert f g ff gg.
    1-2: induction sbfg as [f' g' (flen & sfg & fval)|f' z' g' sbfg1 IHsbfg1 sbfg2 IHsbfg2].
    1-4: intros f g ff gg.
    1-4: subst f' g'.
    1,3: constructor 1; repeat split; auto with *.
    1-2: destruct z'; [apply sb_lt in sbfg1|]; auto with *.
    1-2: econstructor 2; [apply IHsbfg1|apply IHsbfg2]; eauto.

  split.
  intros x y rxy.
  induction rxy as
    [x y rxy|
     x y rxy|
     x y (e & rxe & rey)|
     x y e rxe rey [IHrey IHrey_cond]|
     x y e rxe rey [IHrxe IHrxe_cond] [IHrey IHrey_cond]]
    using ithb_my_ind; unshelve esplit.
  constructor 1; left; right; auto.
  constructor 1; right; auto.
  econstructor 2; constructor 1; left; [right|left]; eauto.
  econstructor 2; [constructor 1; left; left|]; eauto.
  econstructor 2; eauto.

  1-5: intros l lsb ldob lstart lend n o.
  1-3: intros [(f & ldobnf & g & lsbfo & [-> endo])|(f & [<- startn] & g & lsbno & [-> endo])];
    compute in endo; [|compute in startn].
  1,3,5: destruct ldobnf as (lnl & snf & nval).
  1-2: apply sb_lt in lsbfo.
  1-2: subst o f; auto with *.
  destruct lsbfo as [o (lfl & sfo & fval)|].
  subst o; injection endo; intros f1; subst f.
  injection f1; intros n0; subst n.
  compute in nval; assumption.
  apply sb_lt in lsbfo1.
  apply sb_lt in lsbfo2.
  auto with *.
  1-3: destruct lsbno as [o (lnl & sno & nval)|].
  1,3,5: subst o n; compute in nval; assumption.
  1-3: apply sb_lt in lsbno2.
  1-2: apply sb_lt in lsbno1.
  1-2: auto with *.
  subst z.
  destruct lsbno1 as [o (lnl & sno & nval)|].
  subst o n; compute in nval; assumption.
  apply sb_lt in lsbno1_1.
  apply sb_lt in lsbno1_2.
  auto with *.

  1-2: intros [(f & (lnl & snf & ndob) & g & lsbfo & [-> endo])|(f & [<- startn] & g & lsbno & [-> endo])].
  unfold lend in *.
  destruct n; simpl in ndob.
  assumption.
  destruct o; apply sb_lt in lsbfo as snlto.
  auto with *.
  subst f.
  apply IHrey_cond with n o.
  left.
  repeat esplit; eauto.
  simpl in lnl |- *; auto with *.
  eapply is_sb_ext in lsbfo; simpl in lsbfo; fold (tc_to_l Op ithb_r e y IHrey) in lsbfo.
  rewrite PeanoNat.Nat.sub_0_r in lsbfo.
  assumption.
  assumption.
  simpl in endo |- *.
  auto with *.

  unfold lstart, lend in startn, endo; subst n; simpl in endo.
  apply t_step_rt in lsbno as (f & sbnf & [->|sbfo]%clos_refl_transE).
  1,2: destruct sbnf as (nlen & <- & nsb).
  pose (len_1 Op ithb_r e y IHrey).
  auto with *.
  destruct o; [apply sb_lt in sbfo; auto with *|].
  apply is_sb_ext in sbfo; simpl in sbfo; auto with *.
  rewrite PeanoNat.Nat.sub_0_r in sbfo.
  apply IHrey_cond with 0 o.
  right.
  repeat esplit.
  assumption.
  auto with *.
  apply sb_lt in sbfo; auto with *.
  simpl; auto with *.
  pose (len_1 Op ithb_r e y IHrey).
  auto with *.

  1-2: simpl in l.
  1-2: set (lp := tc_to_l Op ithb_r x e IHrxe) in *.
  1-2: set (ln := tc_to_l Op ithb_r e y IHrey) in *.
  1-2: unfold lend in endo; simpl in endo; subst o.
  subst f.
  destruct (Compare_dec.lt_dec n (length lp)).
  apply IHrey_cond with 0 (length ln).
  right.
  repeat esplit.
  apply is_sb_ext in lsbfo.
  assert (H1: S n - length lp = 0) by auto with *; rewrite H1 in *.
  assert (H2: length l - length lp = length ln).
    unfold l; rewrite app_length.
    auto with *.
  rewrite H2 in *.
  assumption.
  apply sb_lt in lsbfo; assumption.
  pose (H := len_1 _ _ _ _ IHrey); fold ln in H.
  unfold l; rewrite app_length; auto with *.
  apply IHrey_cond with (n - length lp) (length ln).
  left.
  repeat esplit; auto with *.
  unfold l in lnl; rewrite app_length in lnl.
  auto with *.
  assert (nth_error l n = nth_error ln (n - length lp)).
    unfold l.
    clear IHrxe_cond ndob lsbfo lnl.
    revert n n0.
    induction lp; intros n n0.
    simpl; auto with *.
    destruct n.
    contradict n0; simpl; auto with *.
    simpl.
    apply IHlp.
    simpl in n0.
    auto with *.
  rewrite <- H.
  assumption.
  apply is_sb_ext in lsbfo.
  assert (H1: S n - length lp = S (n - length lp)) by auto with *; rewrite <- H1.
  assert (H2: length ln = length l - length lp).
    unfold l; rewrite app_length; auto with *.
  rewrite H2.
  assumption.
  apply sb_lt in lsbfo; assumption.
  auto with *.

  unfold lstart in startn; subst n.
  apply (IHrey_cond 0 (length ln)).
  right.
  repeat esplit.
  apply is_sb_ext in lsbno.
  rewrite PeanoNat.Nat.sub_0_l in lsbno.
  assert (H2: length ln = length l - length lp).
    unfold l; rewrite app_length; auto with *.
  rewrite <- H2 in lsbno.
  auto.
  apply sb_lt in lsbno; assumption.
  unfold l; rewrite app_length.
  pose (H := len_1 _ _ _ _ IHrey); fold ln in H.
  auto with *.

  pose (clos_trans_t_size A R (x y: A) (rxy: clos_trans_t R x y) :=
    (fix f x y (rxy: clos_trans_t R x y) :=
      match rxy with
        t_step_t _ _ y rxy => 0
      | t_trans_t _ _ y z rxy ryz => (f _ _ rxy) + (f _ _ ryz) + 1
      end) _ _ rxy).
  pose (clos_trans_t_rtl_error A R (x y: A) (rxy: clos_trans_t R x y) :=
    (fix f x y (rxy: clos_trans_t R x y) :=
      match rxy with
        t_step_t _ _ y rxy => None
      | t_trans_t _ _ y z rxy ryz =>
          match (f _ _ ryz) with
            None => Some (existT _ _ rxy)
          | Some (existT _ e rtye) => Some (existT _ _ (t_trans_t _ _ _ _ rxy rtye))
          end
      end) _ _ rxy).
  pose (clos_trans_t_rhd A R (x y: A) (rxy: clos_trans_t R x y) :=
    (fix f x y (rxy: clos_trans_t R x y) :=
      match rxy with
        t_step_t _ _ y rxy => existT _ x rxy
      | t_trans_t _ _ y z rxy ryz => f y z ryz
      end) _ _ rxy).
  assert (clos_trans_t_rhd_hd_tl_join: 
    forall A R (x y: A) (rxy: clos_trans_t R x y),
      let '(existT _ e' rxyhd) := clos_trans_t_rhd _ _ _ _ rxy in
      match (clos_trans_t_rtl_error _ _ _ _ rxy) with
        None => x = e'
      | Some (existT _ e rxytl) => e = e'
      end).
    intros A R x y rxy.
    induction rxy; simpl; auto.
    destruct (clos_trans_t_rhd _ _ _ _ rxy2) as [f' rfz] eqn:rxy2hdeq.
    destruct (clos_trans_t_rtl_error _ _ _ _ rxy2) as [[f rxy2tl]|] eqn:rxy2tleq.
    rewrite <- IHrxy2.
    reflexivity.
    assumption.
  assert (size_rtl_dec:
    forall A R (x y: A) (rxy: clos_trans_t R x y),
      match (clos_trans_t_rtl_error _ _ _ _ rxy) with
        None => True
      | Some (existT _ e rxytl) =>
          S (clos_trans_t_size _ _ _ _ rxytl) = clos_trans_t_size _ _ _ _ rxy
      end).
    intros A R x y rxy.
    induction rxy; simpl; auto.
    destruct (clos_trans_t_rtl_error _ _ _ _ rxy2) as [[f rxy2tl]|] eqn:rxy2tleq.
    rewrite <- IHrxy2.
    cbn.
    fold (clos_trans_t_size _ _ _ _ rxy1).
    fold (clos_trans_t_size _ _ _ _ rxy2tl).
    auto with *.
    destruct rxy2; simpl in rxy2tleq |- *.
    auto with *.
    destruct (clos_trans_t_rtl_error _ _ _ _ rxy2_2) as [[foo bar]|]; discriminate rxy2tleq.
  assert (tc_to_l_rtl_eq:
    forall A R (x y: A) (rxy: clos_trans_t R x y),
      let 'existT _ e rey := clos_trans_t_rhd _ _ _ _ rxy in
      match (clos_trans_t_rtl_error _ _ _ _ rxy) with
        None => []
      | Some (existT _ _ rxytl) =>
          tc_to_l _ _ _ _ rxytl
      end ++ [existT _ (e, y) rey] = tc_to_l _ _ _ _ rxy).
    intros A R x y rxy.
    induction rxy; simpl; auto.
    destruct (clos_trans_t_rhd _ _ _ _ rxy2) as [f' rfz] eqn:rxy2hdeq.
    destruct (clos_trans_t_rtl_error _ _ _ _ rxy2) as [[f rxy2tl]|] eqn:rxy2tleq.
    rewrite <- IHrxy2.
    cbn.
    auto with *.
    destruct rxy2; simpl in rxy2hdeq, rxy2tleq |- *.
    apply (f_equal (
      fun '(existT _ p1 p2) =>
        existT (fun '(x, y) => R x y) (p1, y0) p2)) in rxy2hdeq.
    rewrite rxy2hdeq; reflexivity.
    destruct (clos_trans_t_rtl_error _ _ _ _ rxy2_2) as [[foo bar]|]; discriminate rxy2tleq.
  
  pose (clos_trans_t_rtl_rel A R x :=
    fun
      (p c: { y: A & clos_trans_t R x y }) =>
      let 'existT _ cy cr := c in
      match clos_trans_t_rtl_error _ _ _ _ cr with
        None => False
      | Some c_tl => p = c_tl
      end).

  assert (step_wf: forall A R x, well_founded (clos_trans_t_rtl_rel A R x)).
    intros A R x (y & rxy).
    (*
      step relation for x is on {y & crt Y x y}
      induction on size reqires {'(x,y) & crt Y x y}
      can we express x' y' rxy' in terms of the larger type?
       - rxy's type must be dependent on x' and y' in the step relation, rather than on projT1 rxy
       - 
      can we redefine our step relation in terms of the larger type?
       - 
    *)
    assert (size_ind :=
      well_founded_induction
        (Wf_nat.well_founded_ltof _ (
          fun '(existT _ (x, y) rxy: {'(x, y): A*A & clos_trans_t R x y}) =>
            clos_trans_t_size A R x y rxy))).
    unshelve evar (spec_flip:
      forall r'xy: {'(x,y): A*A & clos_trans_t R x y},
        (let '(x, y) := projT1 r'xy in clos_trans_t R x y) =
        clos_trans_t R (let '(x, y) := projT1 r'xy in x)
                        (let '(x, y) := projT1 r'xy in y)).
      destruct r'xy as [[]]; simpl; reflexivity.
    pose (r'xy := existT (fun '(x, y) => clos_trans_t R x y) (x, y) rxy).
    pose (x' := let (x'', y'') := projT1 r'xy in x'').
    unshelve evar (Heqx: x' = x).
      unfold x'; reflexivity.
    pose (y' := let (x'', y'') := projT1 r'xy in y'').
    unshelve evar (Heqy: y' = y).
      unfold y'; reflexivity.
    unshelve evar (rxy': clos_trans_t R x' y').
      unfold x', y'.
      rewrite <- (spec_flip r'xy).
      apply (projT2 r'xy).
    unshelve evar (rxy'_raw: clos_trans_t R x y).
      rewrite <- Heqx.
      rewrite <- Heqy.
      apply rxy'.
    unshelve evar (Heqrxy: rxy'_raw = rxy).
      (* requires invariance of reflexive rewrites, which is why the previous equalities are transparent *)
      unfold rxy'_raw, rxy'.
      unfold x', y', r'xy; simpl.
      reflexivity.
    clearbody Heqx Heqy Heqrxy r'xy.
    assert
     (Hacc:
        Acc (clos_trans_t_rtl_rel A R x)
          (existT (fun y0 : A => clos_trans_t R x y0) y rxy) =
        Acc (clos_trans_t_rtl_rel A R x')
          (existT (fun y0 : A => clos_trans_t R x' y0) y' rxy')).
      destruct Heqx, Heqy; simpl.
      f_equal.
      f_equal.
      simpl in rxy'_raw.
      subst rxy'_raw.
      symmetry; assumption.
    rewrite Hacc; clear Hacc.
    clear x y rxy Heqx Heqy Heqrxy rxy'_raw.
    revert x' y' rxy'.
    induction r'xy using size_ind; intros x' y' rxy'.
    assert (size_dec := size_rtl_dec _ _ _ _ rxy').
    constructor 1.
    intros [e rxe] e_tl_y.
    simpl in e_tl_y.
    destruct (clos_trans_t_rtl_error _ _ _ _ rxy').
    subst s.
    specialize (H (existT _ (x', e) rxe)); simpl in H.
    apply H.
    unfold Wf_nat.ltof.
    destruct r'xy as [[x y] rxy]; simpl in *.
    subst x' y' rxy'.
    auto with *.
    contradiction.

  intros x y (rxe & rxe_cond).
  remember y as e in rxe, rxe_cond.
  pose (r'xe := existT _ e rxe).
  set (e' := projT1 r'xe).
  unshelve evar (Heqe': e' = e).
    reflexivity.
  set (rxe' := projT2 r'xe).
  fold e' in rxe'.
  unshelve evar (rxe'_raw: clos_trans_t ithb_r x e).
    rewrite <- Heqe'.
    apply rxe'.
  unshelve evar (Heqrxe': rxe'_raw = rxe).
    unfold rxe'_raw, rxe'.
    unfold e', r'xe; simpl.
    reflexivity.
  clearbody Heqe' Heqrxe' r'xe.
  assert (Heqtcl: tc_to_l Op ithb_r x e rxe =
                  tc_to_l Op ithb_r x e' rxe').
    destruct Heqe', Heqrxe'; simpl.
    f_equal.
  rewrite Heqtcl in rxe_cond.
  subst e rxe.
  assert (ncond:
    ithb e' y \/
      let l := tc_to_l Op ithb_r x e' rxe' in
      let lsb := is_sb l in
      let ldob := is_dob l in
      let lstart := fun n : nat => n = 0 in
      let lend := fun n : nat => n = length l in
      ldob ⨾ lsb⁺ ⨾ ⦗lend⦘ ∪ ⦗lstart⦘ ⨾ lsb⁺ ⨾ ⦗lend⦘ ⊆ ∅₂ /\
      (sb e' y /\ ldob ⨾ ⦗lend⦘ ⊆ ∅₂ \/ e' = y)).
    right; split; auto.
  clear rxe'_raw Heqe' Heqtcl rxe_cond.
  induction r'xe as [r'xe IHp] using (well_founded_induction (step_wf _ _ x)).
  assert (rxytltol := tc_to_l_rtl_eq _ _ _ _ rxe').
  assert (rxyhdtl := clos_trans_t_rhd_hd_tl_join _ _ _ _ rxe').
  destruct (clos_trans_t_rhd _ _ _ _ rxe') as [f' rfe] eqn:rxehd.
  destruct (clos_trans_t_rtl_error _ _ _ _ rxe') as [[f rxf']|] eqn:rxetl.
  subst f'.
  apply (IHp (existT _ f rxf')).
  destruct r'xe; simpl in *; fold e' rxe'.
  rewrite rxetl; reflexivity.
  destruct ncond as [ithbey|[rxe_cond sbeqey]].
  left.
  destruct rfe as [[sbfe|swfe]|dobfe].
  econstructor 4; repeat esplit; eauto.
  econstructor 5; repeat esplit; vauto.
  econstructor 5; repeat esplit; vauto.
  destruct rfe as [[sbfe|swfe]|dobfe].
  right.
  intros l lsb ldob lstart lend.
  split.
  rewrite <- rxytltol in rxe_cond; clear rxytltol.
  intros i j
    [(e'' & (ilen & <- & ival) & f' & sbef & [-> jend])|
      (e'' & [<- istart] & f' & sbij & [-> jend])].
  unfold lend in jend; subst j.
  apply (rxe_cond i (S (length l))).
  left.
  repeat esplit.
  rewrite app_length; auto with *.
  rewrite nth_error_app1; assumption.
  apply t_rt_step; exists (length l); repeat esplit.
  apply clos_refl_transE; right.
  clear ilen.
  induction sbef as [e'' j (elen & <- & eval)|].
  constructor 1; repeat esplit.
  rewrite app_length; auto with *.
  rewrite nth_error_app1; assumption.
  econstructor 2; eauto.
  rewrite app_length; rewrite length_cons; unfold l; simpl; auto with *.
  rewrite nth_error_app2; unfold l.
  rewrite PeanoNat.Nat.sub_diag; simpl; constructor.
  constructor 1.
  rewrite app_length; rewrite length_cons; unfold l; simpl; auto with *.
  unfold lstart, lend in istart, jend; subst i j.
  apply (rxe_cond 0 (S (length l))).
  right.
  repeat esplit.
  apply t_rt_step; exists (length l); repeat esplit.
  apply clos_refl_transE; right.
  clear ldob lstart lend rxe_cond size_rtl_dec clos_trans_t_size len_1 IHp.
  induction sbij as [e'' j (elen & <- & eval)|].
  constructor 1; repeat esplit.
  rewrite app_length; auto with *.
  rewrite nth_error_app1; assumption.
  econstructor 2; eauto.
  rewrite app_length; rewrite length_cons; unfold l; simpl; auto with *.
  rewrite nth_error_app2; unfold l.
  rewrite PeanoNat.Nat.sub_diag; simpl; constructor.
  constructor 1.
  rewrite app_length; rewrite length_cons; unfold l; simpl; auto with *.
  assert (rxftltol := tc_to_l_rtl_eq _ _ _ _ rxf').
  assert (rxfhdtl := clos_trans_t_rhd_hd_tl_join _ _ _ _ rxf').
  destruct (clos_trans_t_rhd _ _ _ _ rxf') as [g' rgf] eqn:rxfhd.
  left; split.
  destruct sbeqey as [[sbey fecond]|<-].
  eapply sb_order; eassumption.
  assumption.
  pose (rxflen := rxftltol).
  apply (f_equal (@length _)) in rxflen.
  rewrite app_length in rxflen.
  rewrite length_cons in rxflen.
  simpl in rxflen.
  pose (rxelen := rxytltol).
  apply (f_equal (@length _)) in rxelen.
  rewrite app_length in rxelen.
  rewrite length_cons in rxelen.
  simpl in rxelen.
  intros i j (f' & (ilen & sif & ival) & [-> fend]).
  unfold lend in fend; subst j.
  unfold l in ival.
  simpl in ival, l.
  rewrite <- rxftltol in ival.
  rewrite nth_error_app2 in ival.
  unfold l in fend; rewrite <- rxflen in fend; simpl in fend.
  rewrite PeanoNat.Nat.add_comm in fend; apply (f_equal pred) in fend; simpl in fend.
  subst i.
  rewrite PeanoNat.Nat.sub_diag in ival.
  simpl in ival.
  destruct rgf as [[sbgf|swgf]|dobgf]; try contradiction.
  apply (rxe_cond (pred (length l)) (S (length l))).
  left; repeat esplit; unfold l; auto with *.
  rewrite <- rxytltol.
  rewrite <- rxftltol.
  rewrite nth_error_app1.
  rewrite nth_error_app2.
  rewrite app_length.
  rewrite length_cons; simpl.
  rewrite PeanoNat.Nat.add_comm; simpl.
  rewrite PeanoNat.Nat.sub_diag.
  simpl; constructor.
  rewrite app_length.
  rewrite length_cons; simpl.
  rewrite PeanoNat.Nat.add_comm; simpl.
  constructor.
  rewrite app_length; rewrite length_cons; auto with *.
  constructor 1; repeat esplit; auto with *.
  rewrite <- rxytltol.
  rewrite nth_error_app2.
  rewrite <- rxflen.
  rewrite PeanoNat.Nat.add_comm; simpl.
  rewrite PeanoNat.Nat.sub_diag.
  simpl; constructor.
  auto with *.
  unfold l in fend.
  rewrite <- rxflen in fend.
  rewrite PeanoNat.Nat.add_comm in fend; simpl in fend.
  auto with *.
  left.
  destruct sbeqey as [[sbey fecond]|<-].
  constructor 3; do 2 esplit; eassumption.
  constructor 1; assumption.
  destruct sbeqey as [[sbey fecond]|<-].
  exfalso; apply (fecond
    (pred (length (tc_to_l Op ithb_r x e' rxe')))
    (length (tc_to_l Op ithb_r x e' rxe'))).
  repeat esplit.
  1-4: rewrite <- rxytltol.
  1-4: rewrite app_length.
  1-4: rewrite length_cons.
  1-4: auto with *.
  rewrite nth_error_app2.
  rewrite PeanoNat.Nat.add_comm.
  rewrite PeanoNat.Nat.sub_diag.
  simpl; constructor.
  auto with *.
  left.
  constructor 2; eassumption.
  subst f'.
  destruct ncond as [ithbey|[rxe_cond sbeqey]].
  destruct rfe as [[sbfe|swfe]|dobfe].
  econstructor 4; repeat esplit; eauto.
  econstructor 5; repeat esplit; vauto.
  econstructor 5; repeat esplit; vauto.
  destruct rfe as [[sbfe|swfe]|dobfe].
  exfalso; apply (rxe_cond 0 1).
  simpl in rxytltol.
  right; repeat esplit; auto with *.
  constructor 1.
  repeat esplit; auto with *.
  1-3: rewrite <- rxytltol; simpl.
  1-3: auto.
  destruct sbeqey as [[sbey ndobey]|<-].
  constructor 3; do 2 esplit; eauto.
  constructor 1; auto.
  destruct sbeqey as [[sbey ndobey]|<-].
  exfalso; apply (ndobey 0 1).
  simpl in rxytltol.
  repeat esplit; auto with *.
  1-3: rewrite <- rxytltol; simpl.
  1-3: auto.
  constructor 2; auto.
Qed.

(*
Definition ithb_alt2: relation Op :=
  (sb^? ⨾ (`↑ dob ∪ (sw ⨾ sb^?)))⁺.
*)

(*
HB:
An evaluation A happens before an evaluation B (or, equivalently, B happens after A) if:
 — A is sequenced before B, or
 — A inter-thread happens before B.
*)

Definition hb := sb ∪ ithb.

(*
SHB:
An evaluation A strongly happens before an evaluation B if either
 — A is sequenced before B, or
 — A synchronizes with B, or
 — A strongly happens before X and X strongly happens before B.
*)

Definition shb := (sb ∪ sw)⁺.

(*
COHERENCE:
The value of an atomic object M, as determined by evaluation B, shall be the value stored by some side effect
A that modifies M, where B does not happen before A. [ Note: The set of such side effects is also restricted
by the rest of the rules described here, and in particular, by the coherence requirements below. — end note ]
*)

Conjecture coherence_rf: hb ⊆ hb \ `↑ rf⁻¹.

(*
COHERENCE:
If an operation A that modifies an atomic object M happens before an operation B that modifies M, then
A shall be earlier than B in the modification order of M. [ Note: This requirement is known as write-write
coherence. — end note ]
*)

Conjecture coherence_ww: hb ⊆ hb \ `↑ mo⁻¹.

(*
COHERENCE:
If a value computation A of an atomic object M happens before a value computation B of M, and A takes
its value from a side effect X on M, then the value computed by B shall either be the value stored by X or
the value stored by a side effect Y on M, where Y follows X in the modification order of M. [ Note: This
requirement is known as read-read coherence. — end note ]
*)

Conjecture coherence_rr: `↓ hb ⊆ `↓ hb \ from ↓ mo⁻¹.

(*
COHERENCE:
If a value computation A of an atomic object M happens before an operation B that modifies M, then A
shall take its value from a side effect X on M, where X precedes B in the modification order of M. [ Note:
This requirement is known as read-write coherence. — end note ]
*)

Conjecture coherence_rw: hb ⊆ hb \ (`↑ mo ⨾ `↑ rf)⁻¹.

(*
COHERENCE:
If a side effect X on an atomic object M happens before a value computation B of M, then the evaluation B
shall take its value from X or from a side effect Y that follows X in the modification order of M. [ Note: This
requirement is known as write-read coherence. — end note ]
*)

Conjecture coherence_wr: hb ⊆ hb \ `↑ mo⁻¹ ⨾ `↑ rf.

(*
SC-PER-LOC:
[ Note: The four preceding coherence requirements effectively disallow compiler reordering of atomic operations
to a single object, even if both operations are relaxed loads. This effectively makes the cache coherence
guarantee provided by most hardware available to C++ atomic operations. — end note ]

A total order per location, extended from sb per location, where each read reads from the write to the same
location immediately previous.

  sb ww: in mo
  sb wr: if not rf then in mo; rf
  sb rw: in rb
  sb rr (diff writes): in rb;mo?;rf
  sb rr (same writes): have same rf & rb just need to sequence them
*)

Lemma rw_finite: set_finite (A:=ReadWrite) set_full.
  destruct events'_finite as [findom inl].
  pose (fd := findom).
  assert (exists fdrw: list ReadWrite, forall x, In (``x) fd -> In x fdrw).
    induction fd.
    exists [].
    simpl; auto.
    destruct IHfd as [fdrwp inp].
    destruct (classic (exists a': ReadWrite, (``a') = a)) as [[a' aeq]|].
    exists (a' :: fdrwp).
    intros x [xa|xna].
    left.
    subst a; do 2 apply sig_ext.
    auto.
    right.
    eapply inp; auto.
    exists fdrwp.
    intros x [xa|xna].
    contradict H.
    exists x.
    auto.
    apply inp.
    auto.
  destruct H as [fdrw infd].
  exists fdrw.
  intros x _.
  apply infd.
  apply inl.
  destruct x as [[[] (ev & rfw & fwf)]]; apply ev.
Qed.

Lemma sc_per_loc:
  exists scl: relation ReadWrite,
    (forall l, strict_total_order (loc ↓₁ (eq l)) scl) /\
    restr_eq_rel loc (`↓ sb) ⊆ scl /\
    rf ⊆ immediate (restr_eq_rel loc (⦗`↓₁ IsWrite⦘ ⨾ scl)).
Proof.
  destruct (mo_total_order_per_loc 0) as [[irr' tra'] _].
  assert (strict_partial_order (AW2RW ↑ mo)) as [irr tra].
    split.
    intros x (e & f & moef & ee & <-).
    apply AW2RW_inj in ee.
    subst f.
    eapply irr'; eauto.
    intros x y z (e & f & moef & <- & <-) (f' & g & mofg & ff & <-).
    apply AW2RW_inj in ff.
    subst f'.
    repeat esplit.
    eapply tra'; eauto.
  pose (rb := (⦗`↓₁ set_compl IsWrite⦘ ⨾ rf⁻¹ ⨾ AW2RW ↑ mo)).
  pose (sb_sibling_reads := AR2RW ↑ restr_eq_rel from (`↓ restr_rel (set_compl IsWrite) sb)).
  pose (scl := (sb_sibling_reads ∪ AW2RW ↑ mo ∪ rf ∪ rb)⁺).

  pose (eqb_loc l := fun rw => Nat.eqb (loc rw) l).
  destruct (rw_finite) as [rwdom inrwdom].
  pose (rwdom_by_l l :=
    fold_right
      (fun (x: ReadWrite)
           (t: list {o: ReadWrite | loc o = l }) =>
         match PeanoNat.Nat.eq_dec (loc x) l
         with
           left e => (exist _ x e) :: t
         | right ne => t
         end) [] rwdom).
  pose (sclt := ⋃ l, `↑ tot_ext (rwdom_by_l l) (`↓ scl)).

  exists sclt.

  assert (rf_mo: forall x y, IsWrite (`y) -> (AW2RW ↑ mo ∪ (AW2RW ↑ mo)^? ⨾ rf) x y -> (AW2RW ↑ mo) x y).
    intros x y wy [moxy|(e & [->|moex] & [yr rfex])].
    auto.
    1,2: assert (yrmw: IsRMW (`y)).
      1,3: destruct y as [[[]]]; auto.
    1,2: lapply (rmw_atomic (`e) (`y)).
    1,3: intros (e' & f & [moxy imm] & xx & yy).
    2: apply tra with e; auto.
    1,2: repeat esplit; eauto.
    1-4: apply sig_ext.
    1,3: rewrite <- xx; destruct e' as [[[]]]; auto.
    1,2: rewrite <- yy; destruct f as [[[]]]; auto.
    1,2: repeat esplit; eauto.
    1,2: apply f_equal; eauto.

  pose (sclb :=
    sb_sibling_reads ∪
    (AW2RW ↑ mo ∪
     (AW2RW ↑ mo)^? ⨾ rf) ∪
    rb ⨾ rf^?).
  assert (to_b: scl ⊆ sclb).
    assert (rweq: forall x, ` (AR2RW x) = `x).
      intros []; simpl; reflexivity.
    assert (req: forall (x: Read) xwf xr, exist _ (exist _ (`` (AR2RW x)) xwf) xr = x).
      intros e ewf er.
      do 2 apply sig_ext; simpl.
      rewrite (rweq e).
      reflexivity.
    intros x y rxy.
    induction rxy as [x y [[[sbxy|moxy]|rfxy]|rbxy]|].
    left; left; auto.
    left; right; left; auto.
    left; right; right; esplit; eauto.
    right; esplit; eauto.
    assert (H: IsWrite (`y) \/ ~IsWrite (`y) /\ IsRead (`y)).
      clear rxy1 rxy2 IHrxy1 IHrxy2.
      destruct y as [[[] wf] nf]; auto.
      contradict nf; auto.
    destruct H as [iw|[nw ir]].
    destruct IHrxy1 as
      [[(x' & y' & [(sbxy & xnw & ynw) fxy] & <- & <-)|
        morfxy]|
       (f & (x' & [<- nw] & e & rfex & moef) & rffy)].
    destruct y'; contradiction.
    apply rf_mo in morfxy.
    destruct IHrxy2 as
      [[(y' & z' & [(sbyz & ynw & znw) fyz] & <- & <-)|
        [moyz|
         (e & [<-|moye] & rfez)]]|
       (e & (y' & [<- nwe] & rbye) & rfez)].
    destruct y'; contradiction.
    left; right; left; eapply tra; eauto.
    left; right; right; esplit; eauto.
    left; right; right; esplit; esplit.
    2: eauto.
    right; eapply tra; eauto.
    right; eauto.
    contradiction.
    auto.
    assert (moey: (AW2RW ↑ mo) e y).
      destruct rffy as [<-|[ir rffy]].
      auto.
      lapply (rmw_atomic (`f) (`y)).
      intros (f' & y' & [mofy imm] & ff & yy).
      eapply tra; eauto.
      repeat esplit; eauto.
      1,2: apply sig_ext.
      rewrite <- ff; destruct f' as [[[]]]; auto.
      rewrite <- yy; destruct y' as [[[]]]; auto.
      repeat esplit; eauto.
      apply f_equal; eauto.
      destruct y as [[[]]]; auto.
    right.
    destruct IHrxy2 as
      [[(y' & z' & [(sbyz & ynw & znw) fyz] & <- & <-)|
        [moyz|
         (g & [<-|moyg] & rfgz)]]|
       (g & (y' & [<- nwg] & rbyg) & rfgz)].
    destruct y'; contradiction.
    1-3: esplit; esplit; [esplit; esplit; esplit; auto; esplit; [eauto|]|].
    2: left; auto.
    eapply tra; eauto.
    2: eauto.
    auto.
    2: eauto.
    eapply tra; eauto.
    contradiction.
    destruct IHrxy2 as
      [[(y' & z' & [(sbyz & ynw & znw) fyz] & <- & <-)|
        [([e eiw] & f & moef & <- & <-)|
         (g & [<-|(y' & g' & moyg & <- & <-)] & zir & rfgz)]]|
       (g & (y' & [<- nwg] & h & [yir2 rfhy] & mohg) & rfgz)].
    destruct IHrxy1 as
      [[(x' & y'' & [(sbxy & xnw & ynw') fxy] & <- & yy)|
        [(x' & y'' & moxy & <- & yy)|
         (f & moxf & yir & rffy)]]|
      (f & (x' & [<- nwx] & e & rfex & moef) & [->|[yir rffy]])].
    apply AR2RW_inj in yy; subst y''.
    left; left; esplit; esplit; esplit; esplit.
    esplit.
    eapply sb_order.
    apply sbxy.
    eauto.
    eauto.
    etransitivity; eauto.
    1,2: auto.
    apply (f_equal (@proj1_sig _ _)) in yy.
    destruct y' as [y'], y'' as [y'']; simpl in yy; subst y''; contradiction.
    left; right; right; esplit; esplit.
    eauto.
    unshelve esplit.
      destruct z'; auto.
    rewrite (req z').
    rewrite <- fyz.
    rewrite (req y') in rffy.
    auto.
    destruct moef as (e' & y'' & moef & <- & yy).
    apply (f_equal (@proj1_sig _ _)) in yy.
    destruct y' as [y'], y'' as [y'']; simpl in yy; subst y''; contradiction.
    right; esplit; esplit.
    esplit; esplit; esplit; auto.
    eauto.
    right.
    unshelve esplit.
      destruct z'; auto.
    rewrite (req z').
    rewrite <- fyz.
    rewrite (req y') in rffy.
    auto.
    simpl in ir; contradiction.
    destruct z as [[[] (ev & rfw & fwf)] znf]; try discriminate zir.
    1-2: apply (f_equal (@proj1_sig _ _)) in rfgz; rewrite rfgz in *.
    1-2: destruct from0; compute in ir, nw, zir, rfw.
    1-8:
      try discriminate ir;
      try contradiction nw;
      try discriminate (rfw eq_refl).
    destruct y'; contradiction.
    destruct IHrxy1 as
      [[(x' & y' & [(sbxy & xnw & ynw) fxy] & <- & <-)|
        [(x' & y' & moxy & <- & <-)|
         (f & moxf & yir & rffy)]]|
       (f & (x' & [<- nwx] & e & rfex & moef) & [->|[yir rffy]])].
    right; esplit; esplit.
    2: apply rfgz.
    esplit; esplit; esplit; auto.
    destruct x'; auto.
    esplit.
    2: eauto.
    unshelve esplit.
      destruct x'; auto.
    rewrite (req x').
    rewrite fxy.
    rewrite (req y') in rfhy.
    auto.
    3: destruct moef as (e' & y' & moey & <- & <-).
    1,3: destruct y'; contradiction.
    1,2: assert (H: yir = yir2); [apply proof_irrelevance|].
    1,2: subst yir2; rewrite <- rffy in *; subst h.
    left; right.
    2: right; esplit; esplit.
    1,3: destruct rfgz; [
      subst g; left |
      right
    ].
    2: esplit; esplit; [right|].
    3-5: eauto.
    1,2: destruct moxf; [subst f; auto|eapply tra; eauto].
    esplit; esplit; esplit; eauto.

  all: assert (irr_scl: irreflexive scl).
    intros x rxy.
    apply to_b in rxy.
    destruct rxy as
      [[(x' & y' & [(sbxx & xnw & ynw) fxy] & <- & yy)|
        [moxx|
        (e & [<-|(x' & e' & moxe & <- & <-)] & ir & rfex)]]|
      (f & (x' & [<- nwx] & e & [xir rfex] & moef) & [->|[yir rffy]])].
    apply AR2RW_inj in yy; subst y'.
    eapply sb_order; eauto.
    eapply irr; eauto.
    apply (f_equal (@proj1_sig _ _)) in rfex.
    assert (xrmw: IsRMW (`x)).
      apply (f_equal (@proj1_sig _ _)) in rfex.
      destruct x as [[[] (ev & rfw & fwf)] nf]; compute in ir, nf, rfw, rfex |- *.
      1-4: try discriminate ir.
      1-2: rewrite <- rfex in rfw; try discriminate (rfw eq_refl).
      auto.
    lapply (rmw_atomic (`x) (`x)).
    intros (x' & x'' & [moxx imm] & <- & xx).
    apply sig_ext in xx; subst x''.
    eapply irr'; eauto.
    repeat esplit; eauto.
    apply (f_equal (@proj1_sig _ _)) in rfex.
    assert (xrmw: IsRMW (` (AW2RW x'))).
      destruct x' as [[[] (ev & rfw & fwf)] iw]; compute in ir, iw, rfw |- *.
      1-4: try discriminate ir; try discriminate iw.
      auto.
    lapply (rmw_atomic (` (AW2RW e')) (` (AW2RW x'))).
    intros (x'' & x''' & [moxx imm] & yy & xx).
    assert (x'' = e').
      destruct e'; apply sig_ext; auto.
    assert (x''' = x').
      destruct x'; apply sig_ext; auto.
    subst x''' x''.
    eapply irr'; eapply tra'; eauto.
    repeat esplit; eauto.
    destruct moef as (e' & x' & moef & <- & <-).
    destruct x'; contradiction.
    assert (xir = yir).
      apply proof_irrelevance.
    subst yir.
    rewrite <- rffy in *.
    subst f.
    eapply irr; eauto.

  assert (irr_sclt: irreflexive sclt).
    intros x [l' [_ (x' & x'' & rxx & xx & <-)]].
    apply sig_ext in xx; subst x''.
    revert rxx.
    apply tot_ext_irr.
    intros x rxx.
    apply -> clos_trans_of_transitive in rxx.
    eapply irr_scl; eauto.
    intros e f g; apply transitive_ct.

  assert (tra_sclt: transitive sclt).
    intros x y z rxy ryz.
    unfold sclt in *.
    clear sclt inrwdom.
    destruct
      rxy as [lx [_ (x' & y' & rxy & <- & <-)]],
      ryz as [ly [_ (y'' & z' & ryz & yy & <-)]].
    assert (lx = ly).
      destruct y', y''.
      simpl in yy.
      subst x0.
      clear rxy.
      rewrite e0 in e.
      auto.
    subst ly.
    apply sig_ext in yy.
    subst y''.
    exists lx; split; auto.
    repeat esplit.
    eapply tot_ext_trans; eauto.

  do 2 esplit.
  esplit.

  auto.

  auto.

  intros x xloc y yloc nxy.
  pose (x' := exist (fun x => loc x = l) x (eq_sym xloc)).
  pose (y' := exist (fun x => loc x = l) y (eq_sym yloc)).
  assert (x' <> y').
    intros nxy'.
    contradict nxy.
    apply (f_equal (@proj1_sig _ _)) in nxy'.
    simpl in nxy'.
    assumption.
  specialize (inrwdom x I) as inx.
  specialize (inrwdom y I) as iny.
  clear inrwdom irr_sclt tra_sclt.
  edestruct (tot_ext_total (rwdom_by_l l) (`↓ scl)); eauto.
  1,2: unfold rwdom_by_l.
  clear iny; induction rwdom; [contradiction|].
  2:clear inx; induction rwdom; [contradiction|].
  1,2: simpl in IHrwdom |- *.
  destruct (PeanoNat.Nat.eq_dec (loc a) l), inx as [->|inx].
  left; apply sig_ext; auto.
  right; apply IHrwdom; auto.
  destruct x'; contradict n; auto.
  apply IHrwdom; auto.
  destruct (PeanoNat.Nat.eq_dec (loc a) l), iny as [->|iny].
  left; apply sig_ext; auto.
  right; apply IHrwdom; auto.
  destruct x'; contradict n; auto.
  apply IHrwdom; auto.
  left; repeat esplit; eauto.
  right; repeat esplit; eauto.

  intros x y [sbxy locxy].
  pose (x' := exist (fun o => loc o = loc x) x eq_refl).
  pose (y' := exist (fun o => loc o = loc x) y (eq_sym locxy)).
  exists (loc x); split; auto.
  exists x', y'.
  repeat split; auto.
  apply tot_ext_extends.
  unfold map_rel; simpl.
  clear x' y'.
  destruct (mo_total_order_per_loc (loc x)) as [_ tot].
  assert (xrw: IsWrite (`x) \/ ~IsWrite (`x) /\ IsRead (`x)).
    destruct x as [[[]]]; auto.
    compute in n; contradiction.
  assert (yrw: IsWrite (`y) \/ ~IsWrite (`y) /\ IsRead (`y)).
    destruct y as [[[]]]; auto.
    compute in n; contradiction.
  destruct xrw as [xw|[xnw xr]], yrw as [yw|[ynw yr]].
  left; left; left; right.
  repeat esplit.
  set (x' := exist (fun x => IsWrite x) (`x) xw).
  set (y' := exist (fun x => IsWrite x) (`y) yw).
  lapply (coherence_ww (`x) (`y)).
  intros [hb_ex nmo_rev].
  assert (mo x' y' \/ mo y' x').
  apply tot.
  1,2: unfold set_map, compose.
  assert (xx: AW2RW x' = x).
    apply sig_ext; auto.
  rewrite xx; reflexivity.
  assert (yy: AW2RW y' = y).
    apply sig_ext; auto.
  rewrite yy; assumption.
  intros xy%(f_equal (@proj1_sig _ _)).
  simpl in xy; apply sig_ext in xy.
  subst y.
  eapply sb_order.
  eassumption.
  destruct H.
  eauto.
  destruct nmo_rev.
  repeat esplit.
  apply H.
  1,2: auto.
  left; apply sbxy.
  1,2: apply sig_ext; auto.
  set (x' := exist (fun x => IsWrite x) (`x) xw).
  set (y' := exist (fun x => IsRead x) (`y) yr).
  destruct (classic (x = AW2RW (from y'))) as [xy|xy].
  left; left; right.
  exists yr.
  apply sig_ext; apply sig_ext.
  apply (f_equal (@proj1_sig _ _)) in xy.
  apply (f_equal (@proj1_sig _ _)) in xy.
  unfold y' in xy; destruct y as [[[]]]; try discriminate yr.
  1,2: destruct x as [[[]]]; try discriminate xw.
  1-4: compute in xy |- *; auto.
  assert (mo x' (from y') \/ mo (from y') x').
  apply tot; unfold set_map, compose.
  assert (xx: AW2RW x' = x).
    apply sig_ext; auto.
  rewrite xx; auto.
  assert (yy: AR2RW y' = y).
    apply sig_ext; auto.
  pose (yfeq := from_eq_loc y').
  rewrite yy in yfeq.
  rewrite <- yfeq; auto.
  intros xyf; contradict xy.
  apply sig_ext.
  apply (f_equal (@proj1_sig _ _)) in xyf.
  assumption.
  destruct H.
  econstructor 2; econstructor 1.
  left; left; right; repeat esplit; eauto.
  apply sig_ext; auto.
  left; right; exists yr.
  apply sig_ext; apply sig_ext.
  unfold y'; destruct y as [[]]; simpl.
  apply from_eq.
  destruct (coherence_wr (`x) (`y)).
  left; auto.
  contradict H1; repeat esplit.
  apply H.
  auto.
  instantiate (1 := yr).
  apply sig_ext; simpl; apply from_eq.
  set (x' := exist (fun x => IsRead x) (`x) xr).
  set (y' := exist (fun x => IsWrite x) (`y) yw).
  assert (mo (from x') y' \/ mo y' (from x')).
  apply tot; unfold set_map, compose.
  assert (xx: AR2RW x' = x).
    apply sig_ext; auto.
  rewrite <- xx; apply from_eq_loc.
  assert (yy: AW2RW y' = y).
    apply sig_ext; auto.
  rewrite yy; auto.
  destruct (coherence_rf (`x) (`y)).
  left; auto.
  intros fxy; apply H0.
  repeat esplit; instantiate (1 := xr).
  apply sig_ext.
  apply (f_equal (@proj1_sig _ _)) in fxy.
  apply (f_equal (@proj1_sig _ _)) in fxy.
  simpl in fxy |- *.
  rewrite <- fxy; apply from_eq.
  destruct H.
  left; right; repeat esplit.
  auto.
  instantiate (2 := xr).
  match goal with |- ?G => assert (hg: mo (from x') y' = G) end.
  f_equal.
  do 2 apply sig_ext; apply from_eq.
  rewrite <- hg; auto.
  apply sig_ext; auto.
  destruct (coherence_rw (`x) (`y)).
  left; auto.
  contradict H1; repeat esplit.
  apply H.
  auto.
  instantiate (1 := xr).
  apply sig_ext; simpl; apply from_eq.
  set (x' := exist (fun x => IsRead x) (`x) xr).
  set (y' := exist (fun x => IsRead x) (`y) yr).
  destruct (classic (from x' = from y')).
  left; left; left; left; esplit; esplit; esplit; esplit.
  repeat esplit.
  4: apply H.
  1-5: auto.
  1-2: apply sig_ext; auto.
  assert (mo (from x') (from y') \/ mo (from y') (from x')).
  apply tot; unfold set_map, compose.
  assert (xx: AR2RW x' = x).
    apply sig_ext; auto.
  rewrite <- xx; apply from_eq_loc.
  assert (yy: AR2RW y' = y).
    apply sig_ext; auto.
  rewrite locxy; rewrite <- yy; apply from_eq_loc.
  auto.
  destruct H0.
  econstructor 2; econstructor 1.
  right; repeat esplit; auto.
  match goal with |- ?G => assert (xy: mo (from x') (from y') = G) end.
  f_equal.
  do 2 apply sig_ext; apply from_eq.
  instantiate (1 := xr).
  rewrite <- xy; auto.
  left; right; repeat esplit.
  instantiate (1 := yr).
  do 2 apply sig_ext; apply from_eq.
  destruct (coherence_rr x' y').
  left; auto.
  contradict H2; unfold map_rel; auto.

  intros x y [yr rfxy].
  assert (xw: IsWrite (`x)).
    subst x.
    destruct y as [[[] (ev & rfw & fwf)]]; try discriminate yr.
    1,2: destruct from0; try discriminate (rfw eq_refl).
    1-4: reflexivity.
  assert (locxy: loc x = loc y).
    pose (y'r := exist (fun o => IsRead o) (`y) yr).
    assert (y = AR2RW y'r).
      apply sig_ext; auto.
    assert (
      exist (fun o : Op => IsRead o)
        (exist (fun o : Op' => OP_WF o)
          (` (` y))
          (rf_obligation_1 y yr))
        (rf_obligation_2 y yr) = y'r).
      do 2 apply sig_ext; auto.
    rewrite H0 in *.
    subst x.
    replace y.
    symmetry.
    apply from_eq_loc.
  pose (x' := exist (fun o => loc o = loc x) x eq_refl).
  pose (y' := exist (fun o => loc o = loc x) y (eq_sym locxy)).
  esplit; try esplit.
  do 2 esplit.
  esplit; eauto.
  exists (loc x); split; auto.
  exists x', y'; repeat esplit; eauto.
  apply tot_ext_extends.
  left; left; right; esplit; eauto.
  auto.
  intros z [[x'' [[<- _] scxz]] xzloc] [[z'' [[<- zw] sczy]] zyloc].
  set (x'w := exist (fun x => IsWrite x) (`x) xw).
  set (z' := exist (fun o => loc o = loc x) z (eq_sym xzloc)).
  set (z'w := exist (fun x => IsWrite x) (`z) zw).
  destruct (mo_total_order_per_loc (loc x)) as [_ tot].
  assert (mo x'w z'w \/ mo z'w x'w).
  apply tot; unfold set_map, compose.
  assert (x = AW2RW x'w).
    apply sig_ext; auto.
  replace x; auto.
  rewrite xzloc.
  assert (z = AW2RW z'w).
    apply sig_ext; auto.
  replace z; auto.
  intros [=xz]; apply sig_ext in xz.
  subst z; eapply irr_sclt; eauto.
  destruct H.
  assert (IsRMW (`y) \/ ~IsWrite (`y)).
    destruct y as [[[]]]; auto.
  destruct H0.
  assert (IsWrite (`y)).
    destruct y as [[[]]]; try discriminate H0; auto.
  set (y'w := exist (fun x => IsWrite x) (`y) H1).
  assert (mo z'w y'w \/ mo y'w z'w).
  apply tot; unfold set_map, compose.
  rewrite xzloc.
  assert (z = AW2RW z'w).
    apply sig_ext; auto.
  replace z; auto.
  rewrite xzloc.
  rewrite zyloc.
  assert (y = AW2RW y'w).
    apply sig_ext; auto.
  replace y; auto.
  intros [=zy]; apply sig_ext in zy.
  subst y; eapply irr_sclt; eauto.
  destruct H2.
  destruct (rmw_atomic (`x) (`y)) as (x'' & y'' & [moxy imm] & xx & yy).
  esplit; esplit; esplit.
  esplit; esplit; esplit.
  apply rfxy.
  1-4: auto.
  assert (xx2: `x = `x'w) by auto.
  assert (yy2: `y = `y'w) by auto.
  rewrite xx2 in *.
  rewrite yy2 in *.
  apply sig_ext in xx.
  apply sig_ext in yy.
  subst x'' y''.
  exfalso; eapply imm.
  apply H.
  auto.
  exfalso; eapply irr_sclt.
  eapply tra_sclt.
  apply sczy.
  exists (loc x); split; auto.
  exists y', z'.
  repeat esplit.
  eapply tot_ext_extends.
  left; left; left; right; repeat esplit.
  apply H2.
  1,2: apply sig_ext; auto.
  exfalso; eapply irr_sclt.
  eapply tra_sclt.
  apply sczy.
  exists (loc x); split; auto.
  exists y', z'.
  repeat esplit.
  apply tot_ext_extends.
  left; right; esplit; esplit; esplit.
  auto.
  auto.
  esplit.
  esplit.
  apply rfxy.
  exists x'w, z'w.
  repeat esplit.
  apply H.
  1,2: apply sig_ext; auto.
  exfalso; eapply irr_sclt.
  eapply tra_sclt.
  apply scxz.
  exists (loc x); split; auto.
  exists z', x'.
  repeat eexists.
  eapply tot_ext_extends.
  left; left; left; right.
  repeat esplit.
  apply H.
  1,2: apply sig_ext; auto.
Qed.

(*
HB/SHB CYCLES:
The implementation shall ensure that no program execution demonstrates a cycle in the “happens before”
relation. [ Note: This cycle would otherwise be possible only through the use of consume operations. — end
note ]

We need existential quantification on sb/rf consistent with other constraints that exhibits a cycle.

 [ Note: In the absence of consume operations, the happens before and strongly happens before relations are
identical. Strongly happens before essentially excludes consume operations. — end note ]

We can assert an equivalence on hb with a superset of shb easily enough, but would need path construction
analysis to assert an equivalence on shb.
*)

Lemma shbb: shb ≡ (sb ∪ (sb^? ⨾ sw ⨾ sb^?)⁺).
Proof.
  split.
  {
    intros x y rxy.
    induction rxy as
      [x y [sbxy|swhb]|
        x y z
          rxy [sbxy|(e & [->|itfy]%clos_refl_transE & (e' & [<-|sbxe] & e'' & swee' & [->|sbee'']))%t_rt_step]
          ryz [sbyz|(f & (f' & [<-|sbyf] & f'' & swff' & [->|sbff'']) & [->|itfz]%clos_refl_transE)%t_step_rt]].
    left; assumption.
    right; constructor 1; do 2 esplit; [|do 2 esplit]; eauto.
    left; eapply sb_order; eauto.
    all: clear rxy ryz.
    all: right.
    all: repeat (
      try repeat match goal with
        H: sb ?x ?y, H2: sb ?y ?z |- _ =>
          assert (sb x z); [eapply sb_order; eauto|clear H H2]
      | H: sb ?x ?y, H2: sw ?y ?z, H3: sb ?z ?e |- _ ?x _ =>
          assert ((sb^? ⨾ sw ⨾ sb^?) x e); [do 2 esplit; [|do 2 esplit]; eauto|clear H H2 H3]
      | H: sb ?x ?y, H2: sw ?y ?z |- _ ?x _ =>
          assert ((sb^? ⨾ sw ⨾ sb^?) x z); [do 2 esplit; [|do 2 esplit]; eauto|clear H H2]
      | H: sw ?x ?y, H2: sb ?y ?z |- _ ?x _ =>
          assert ((sb^? ⨾ sw ⨾ sb^?) x z); [do 2 esplit; [|do 2 esplit]; eauto|clear H H2]
      | H: sw ?x ?y |- _ ?x _ =>
          assert ((sb^? ⨾ sw ⨾ sb^?) x y); [do 2 esplit; [|do 2 esplit]; eauto|clear H]
      end;
      try (idtac + constructor 1; eauto; solve [idtac]);
      try (econstructor 2; [idtac + econstructor 1; eauto; solve [idtac]|])).
  }
  intros x y [sbxy|swxy].
  constructor 1; left; auto.
  induction swxy as [x y (e & sbxe & f & swef & sbfy)|].
  {
    all: destruct sbxe as [<-|sbxe]; [|econstructor 2; [constructor 1; left; eauto|]].
    all: destruct sbfy as [<-|sbfy]; [|econstructor 2; [|constructor 1; left; eauto]].
    all: constructor 1; right; auto.
  }
  econstructor 2; eauto.
Qed.

Lemma shb_hb: shb ⊆ hb.
Proof.
  intros x y [sbxy|shbbxy]%shbb.
  left; auto.
  right.
  induction shbbxy as [x y (e & [<-|sbxe] & f & swef & [->|sbfz])|x z y rxz IHxz rzy IHzy].
  constructor 1; auto.
  constructor 3; esplit; esplit; eauto.
  constructor 4; esplit; esplit; [|constructor 1]; eauto.
  constructor 4; esplit; esplit; [|constructor 3; esplit; esplit]; eauto.
  constructor 5; esplit; esplit; eauto.
Qed.

Lemma hb_shb: hb ≡ (shb ∪ (hb^? ⨾ `↑ dob ⨾ ithb^?)).
Proof.
  split.
  intros x y [sbxy|ithbxy].
  left; constructor 1; left; assumption.
  induction ithbxy using ithb_my_ind.
  left; constructor 1; right; assumption.
  right; do 2 esplit; [|do 2 esplit]; eauto.
  destruct H as (e & swxe & sbey).
  left; econstructor 2; constructor 1; [right|left]; eauto.
  clear ithbxy; destruct IHithbxy as [shbey|(e' & [<-|[sbee|ithbee]] & ithbey)].
  left; econstructor 2; [constructor 1; left|]; eauto.
  right; do 2 esplit; [right; left|]; eauto.
  right; do 2 esplit; [right; left; eapply sb_order|]; eauto.
  right; do 2 esplit; [right; right; econstructor 4; do 2 esplit|]; eauto.
  destruct IHithbxy1 as [shbxe|(c & hbxc & d & dobcd & ithbde)].
  destruct IHithbxy2 as [shbey|(f & [<-|[sbef|ithbef]] & ithbcy)].
  left; econstructor 2; eauto.
  right; do 2 esplit; [right; right|]; eauto.
  apply shbb in shbxe as [sbxe|swxe].
  right; do 2 esplit; [right; left; eapply sb_order|]; eauto.
  apply t_rt_step in swxe as (b & swxb & c & sbbc & d & swcd & sbde).
  assert (ithbbe: ithb b f).
    destruct sbbc as [->|sbbc]; [|econstructor 4; do 2 esplit; eauto].
    1,2: econstructor 3; do 2 esplit; eauto.
    1,2: destruct sbde as [->|sbde]; [|eapply sb_order]; eauto.
  clear c d sbbc swcd sbde sbef.
  right; do 2 esplit; [right; right|eauto].
  apply clos_refl_transE in swxb as [<-|swxb]; [|econstructor 5; exists b; esplit]; eauto.
  clear ithbxy1 ithbxy2 ithbcy ithbbe e f y.
  induction swxb as [x y (c & sbxc & d & swcd & sbdy)|].
  destruct sbxc as [->|sbxc]; [|econstructor 4; do 2 esplit; eauto].
  1,2: destruct sbdy as [->|sbdy]; [econstructor 1|econstructor 3; do 2 esplit]; eauto.
  econstructor 5; do 2 esplit; eauto.
  right; do 2 esplit; [right; right|eauto].
  econstructor 5; do 2 esplit; eauto.
  right; do 2 esplit; [|do 2 esplit]; eauto.
  right; destruct ithbde as [<-|ithbde]; [|econstructor 5; do 2 esplit]; eauto.

  intros x y [shbxy|(e & hbxe & f & dobdf & ithbfy)].
  apply shbb in shbxy as [sbxy|swxy].
  left; assumption.
  right.
  induction swxy as [x y (d & sbxd & e & swde & sbey)|].
  destruct sbxd as [->|sbxd]; [|econstructor 4; do 2 esplit; eauto].
  1,2: destruct sbey as [->|sbey]; [econstructor 1|econstructor 3; do 2 esplit]; eauto.
  econstructor 5; do 2 esplit; eauto.
  right.
  destruct ithbfy as [<-|ithbfy]; [|econstructor 5; do 2 esplit; eauto].
  1,2: destruct hbxe as [<-|[sbxe|ithbxe]].
  1,4: constructor 2; auto.
  1,3: constructor 4; do 2 esplit; [|constructor 2]; eauto.
  1,2: constructor 5; do 2 esplit; [|constructor 2]; eauto.
Qed.

Lemma shb_acy: acyclic shb.
Proof.
  assert (sw_nshb: forall x y, (sb^? ⨾ sw ⨾ sb^?) x y -> ~ shb^? y x).
    intros w z (x & sbwx & y & swxy & sbyz) rzw.
    destruct swxy as (x' & [<- xrel] & e & sbxe & f & (e' & f' & rsef & <- & <-) & g & rffg & g' & [<- gatom] & y' & sbgy & [-> yacq]).
    assert (moef: mo^? e' f').
      destruct rsef as [(e'' & [<- eatom] & moef) _].
      auto.
    clear rsef.
    assert (ngshbe: ~shb^? g (`e')).
      intros shbge.
      destruct rffg as (f'' & g' & rfeg & ff & <-), moef as [<-|moef].
      replace (`e') in *; clear ff e'.
      destruct shbge as [<-%sig_ext|shbge].
      eapply rf_acy; constructor 1; eauto.
      destruct (coherence_rf (`g') (`f'')) as [_ nrffg].
      apply shb_hb; auto.
      apply nrffg; do 2 esplit; eauto.
      destruct shbge as [gg|shbge].
      assert (IsRMW (`g')).
        destruct rfeg as [ir rfeg], e' as [e iw], g' as [g irw].
        simpl in ir, gg |- *; subst g.
        destruct e as [[]]; try discriminate ir; try discriminate iw; reflexivity.
      destruct (rmw_atomic (`f'') (`g')) as (f''' & g'' & [mofg imm] & ff' & gg').
      do 3 esplit; eauto; replace (`e'); auto.
      rewrite gg in gg'.
      rewrite ff in ff'.
      apply sig_ext in ff'.
      apply sig_ext in gg'.
      subst f''' g''.
      do 2 eapply (mo_total_order_per_loc 0); eauto.
      destruct (coherence_rw (`g') (`e')) as [_ nmorfeg].
      apply shb_hb; auto.
      apply nmorfeg; do 4 esplit; eauto.
    apply ngshbe.
    assert (shbwe: shb^? w (`e')).
      destruct sbwx as [<-|sbwx], sbxe as [<-|(x' & [<- xfence] & sbxe)].
      left; auto.
      right; constructor 1; left; auto.
      right; constructor 1; left; auto.
      right; econstructor 2; econstructor 1; left; eauto.
    clear sbwx sbxe.
    assert (shbze: shb^? z (`e')).
      destruct shbwe as [<-|shbwe], rzw as [<-|rzw].
      left; auto.
      right; auto.
      right; auto.
      right; econstructor 2; eauto.
    clear shbwe rzw.
    assert (shbye: shb^? y (`e')).
      destruct shbze as [<-|shbze], sbyz as [<-|sbyz].
      left; auto.
      right; constructor 1; left; auto.
      right; auto.
      right; econstructor 2; [econstructor 1; left|]; eauto.
    clear shbze sbyz.
    destruct shbye as [<-|shbye], sbgy as [<-|(y' & sbgy & [<- yfence])].
    left; auto.
    right; constructor 1; left; auto.
    right; auto.
    right; econstructor 2; [econstructor 1; left|]; eauto.
  intros x rxy.
  apply -> clos_trans_of_transitive in rxy; [|apply transitive_ct].
  set (ryx := rxy).
  set (y := x) in rxy at 2, ryx at 1.
  clearbody y ryx.
  induction rxy as [x y [sbxy|swxy]|].
  apply shbb in ryx as [sbyx|swyx].
  do 2 eapply sb_order; eauto.
  assert (shbxy: shb x y).
    constructor 1; left; auto.
  clear sbxy.
  induction swyx as [x y swyx|x z y rxz IHrxz rzy IHrzy].
  eapply sw_nshb; eauto.
  apply IHrxz; econstructor 2; [eapply shbb; right|]; eauto.
  eapply sw_nshb.
  do 2 esplit; [|do 2 esplit].
  2: eauto.
  1,2: left; auto.
  right; auto.
  apply IHrxy1.
  econstructor 2; eauto.
Qed.

Conjecture hb_acyclic: acyclic hb.

(*
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
*)

Conjecture sc: relation {o: Op | IsSC o}.
Conjecture sc_total_order: strict_total_order set_full sc.
Conjecture sc_consistent: `↑ sc ⊆ `↑ sc \ (hb ∪ `↑ mo)⁻¹.
Conjecture sc_read_exclusions: rf ⊆ rf \ (
  (`↓ `↑ sc⁻¹) ∪
  (`↓ ((`↑ sc ∩ `↑ mo) ⨾ `↑ sc)) ∪
  (`↓ hb ⨾ immediate (restr_eq_rel loc (`↓ (⦗IsWrite⦘ ⨾ `↑ sc))))).

(*
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
*)

Conjecture sc_fence_1: rf ⊆ rf \ `↓ (`↑ mo ⨾ `↑ sc ⨾ ⦗IsFence⦘ ⨾ sb ⨾ ⦗IsAtomic⦘).
Conjecture sc_fence_2: rf ⊆ rf \ `↓ (`↑ mo ⨾ ⦗IsAtomic⦘ ⨾ sb ⨾ ⦗IsFence⦘ ⨾ `↑ sc).
Conjecture sc_fence_3: rf ⊆ rf \ `↓ (`↑ mo ⨾ ⦗IsAtomic⦘ ⨾ sb ⨾ ⦗IsFence⦘ ⨾ `↑ sc ⨾ ⦗IsFence⦘ ⨾ sb ⨾ ⦗IsAtomic⦘).

(*
SC-Fence:
For atomic modifications A and B of an atomic object M, B occurs later than A in the modification order of
M if:
 — there is a memory_order_seq_cst fence X such that A is sequenced before X, and X precedes B in S, or
 — there is a memory_order_seq_cst fence Y such that Y is sequenced before B, and A precedes Y in S, or
 — there are memory_order_seq_cst fences X and Y such that A is sequenced before X, Y is sequenced
before B, and X precedes Y in S.
*)

Conjecture sc_fence_4: `↑ mo ⊆ `↑ mo \ (⦗IsAtomic⦘ ⨾ sb ⨾ ⦗IsFence⦘ ⨾ `↑ sc)⁻¹.
Conjecture sc_fence_5: `↑ mo ⊆ `↑ mo \ (`↑ sc ⨾ ⦗IsFence⦘ ⨾ sb ⨾ ⦗IsAtomic⦘)⁻¹.
Conjecture sc_fence_6: `↑ mo ⊆ `↑ mo \ (⦗IsAtomic⦘ ⨾ sb ⨾ ⦗IsFence⦘ ⨾ `↑ sc ⨾ ⦗IsFence⦘ ⨾ sb ⨾ ⦗IsAtomic⦘)⁻¹.

(*
RACE:
Two actions are potentially concurrent if
 — they are performed by different threads, or
 — they are unsequenced, at least one is performed by a signal handler, and they are not both performed
by the same signal handler invocation.

Two expression evaluations conflict if one of them modifies a memory location (4.4) and the other one reads
or modifies the same memory location.

If a side effect on a memory location (4.4) is unsequenced relative to either another side effect on the same
memory location or a value computation using the value of any object in the same memory location, and they are
not potentially concurrent, the behavior is undefined

The execution of a program contains a data race if it contains two potentially concurrent conflicting actions ,
at least one of which is not atomic, and neither happens before the other, except for the special case for
signal handlers described below. Any such data race results in undefined behavior.
*)

Conjecture race_free:
  forall
    (x y: ReadWrite),
    loc x = loc y ->
    IsWrite (`x) \/ IsWrite (`y) ->
    thread (`x) = thread (`y) /\ sb^⋈? (`x) (`y) \/
    thread (`x) <> thread (`y) /\ (~IsAtomic (`x) \/ ~IsAtomic (`y) -> hb^⋈? (`x) (`y)).

(*
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

- all plain writes are ordered with all other operations on same loc by happens before
- all plain reads are ordered with all writes on same loc by happens before
- happens before is either
  - SB
  - SW induced by an SC read of an SC write
  - SB is consistent with SC, SC is total so (SB ∪ SC)⁺ is an irreflexive ordering
- Is RF immediate in (SB ∪ SC)⁺?
  - If write is plain
    - it's HB-ordered with the read and with all other writes
    - if another write is drf-after the write but drf-before the read
      - if it's plain, by HB-drf consistency it's HB-after the write and HB-before the read, violating coherence-wr
      - if it's SC, it's HB-after the write. No SC write hb-after the initial write can be drf-before the read,
        as this
        - if read is plain, requires that it's HB-before the read, violating coherence-wr
        - if read is SC, violates SC read exclusions.
  - If write is SC
    - if another write is drf-after the write but drf-before the read
      - if it's plain, it's also HB-after the write and HB-before the read, violating coherence-wr
      - if it's SC, it's SC-after the write, and
        - if read is plain, it's HB-after both writes, and the writes are MO-ordered violating coherence-wr
        - if read is SC, violates SC read exclusions
*)

Lemma drf_guarantee:
  (forall x, IsPln x \/ IsSC x) ->
  exists drf: relation Op,
    strict_total_order set_full drf /\
    sb ⊆ drf /\
    rf ⊆ immediate (restr_eq_rel loc (`↓ (⦗IsWrite⦘ ⨾ drf))).
Proof.
  intros allsc.

  destruct sc_total_order as [sc_spo sc_tot].

  pose (drf := (sb ∪ `↑ sc)⁺).
  pose (drfb := sb ∪ sb^? ⨾ `↑ sc ⨾ sb^?).

  assert (drf_drfb: drf ⊆ drfb).
    intros x y rxy.
    induction rxy as [x y [sbxy|(x' & y' & scxy & <- & <-)]|x e y rxe [sbxe|swxe] rey [sbey|swey]].
    left; auto.
    right; repeat esplit; eauto.
    left; eapply sb_order; eauto.
    destruct swey as (f & sbef & scfy).
    right; do 2 esplit; [|eauto].
    right; destruct sbef as [<-|sbef]; [|eapply sb_order]; eauto.
    destruct swxe as (c & sbxc & d & sccd & sbde).
    right; do 2 esplit; [|do 2 esplit].
    1-2: eauto.
    right; destruct sbde as [<-|sbde]; [|eapply sb_order]; eauto.
    destruct swxe as (c & sbxc & d & (c' & d' & swcd & <- & <-) & sbde),
             swey as (f & sbef & g & (f' & g' & swfg & <- & <-) & sbgy).
    right; do 2 esplit; [|do 2 esplit]; [eauto|..|eauto]; repeat esplit.
    assert (sbdf: sb^? (`d') (`f')).
      eapply transitive_cr.
      apply sb_order.
      1-2: eauto.
    destruct sbdf as [<-%sig_ext|sbdf].
    eapply sc_spo; eauto.
    eapply sc_spo; [|eapply sc_spo]; eauto.
    destruct (sc_tot d' I f' I) as [scdf|scfd].
    intros dnf; eapply sb_order; subst f'; eauto.
    assumption.
    destruct (sc_consistent (`f') (`d')) as [_ nhbdf].
    repeat esplit; eauto.
    contradict nhbdf.
    left; left; assumption.

  assert (drf_irr: irreflexive drf).
    intros x rxx.
    apply drf_drfb in rxx as [sbxx|(e & sbxe & f & (e' & f' & swef & <- & <-) & sbfx)].
    eapply sb_order; eauto.
    assert (sbfe: sb^? (`f') (`e')).
      eapply transitive_cr.
      apply sb_order.
      1-2: eauto.
    destruct sbfe as [<-%sig_ext|sbfe].
    eapply sc_spo; eauto.
    destruct (sc_consistent (`e') (`f')) as [_ nhbfe].
    repeat esplit; eauto.
    contradict nhbfe.
    left; left; assumption.
  
  assert (hb_drf: hb ⊆ drf).
    intros x y rxy.
    apply hb_shb in rxy as [shbxy|(e & hbxe & f & (e' & f' & dobef & <- & <-) & ithbfy)].
    induction shbxy as [x y [sbxy|(x' & [<- xrel] & e & sbxe & f & rsef & g & rffg & g' & [<- gatom] & y' & sbgy & -> & yacq)]|x e y shbxe IHxe shbey IHey].
    constructor 1; left; assumption.
    assert (esc: IsSC e).
      destruct rsef as (e' & f' & ((e'' & [<- eatom] & moef) & rsef) & <- & <-).
      assert (eplnsc := allsc (`e')).
      intuition.
    assert (gsc: IsSC g).
      assert (gplnsc := allsc g).
      intuition.
    set (e' := exist _ e esc).
    set (g' := exist _ g gsc).
    destruct (sc_tot e' I g' I).
    intros eg.
    destruct rsef as (e'' & f' & ((e''' & [<- eatom] & moef) & rsef) & <- & <-).
    destruct rffg as (f'' & g'' & rffg & ff & <-).
    assert (moeg: (`↑ mo) (`e'') (`g'') \/ ~IsWrite (`g'')).
      destruct rffg as [gir rffg].
      set (g := g'').
      destruct g'' as [[[]]]; try discriminate; fold g in rffg.
      right; auto.
      destruct (rmw_atomic (`f'') (`g)) as (f & g'' & [mofg imm] & ff' & gg).
      repeat esplit.
      rewrite <- rffg; reflexivity.
      rewrite ff in ff'; apply sig_ext in ff'; subst f'.
      left; repeat esplit; eauto.
      destruct moef as [<-|moef]; [|eapply (mo_total_order_per_loc 0)]; eauto.
    apply (f_equal (@proj1_sig _ _)) in eg; cbn in eg; rewrite <- eg in *.
    destruct moeg as [(e1 & e2 & moee & <-%sig_ext & <-%sig_ext)|enw].
    eapply (mo_total_order_per_loc 0); eauto.
    destruct e''; contradiction.
    destruct sbxe as [->|(x' & [<- xfence] & sbxe)]; [|econstructor 2; [constructor 1; left; eauto|]].
    1,2: destruct sbgy as [<-|(y' & sbgy & [<- yfence])]; [|econstructor 2; [|constructor 1; left; eauto]].
    1-4: constructor 1; right; repeat esplit; eauto.
    destruct (sc_consistent (`g') (`e')) as [_ nhbge].
    repeat esplit; eauto.
    contradict nhbge.
    left; right; constructor 1.
    do 3 esplit; [..|esplit; [|do 2 esplit; [|do 2 esplit; [|do 2 esplit; [esplit|do 2 esplit; [|esplit]]]]]].
    1,6,9: reflexivity.
    2,6: left; reflexivity.
    2,3: eauto.
    1-3: subst e'; subst g'; simpl; unfold IsSC, IsRel, IsAcq, IsAtomic in *.
    1-3: clear H; destruct (mode e), (mode g); simpl; auto.
    econstructor 2; eauto.
    destruct dobef as (g & rseg & h & rfgh & h' & [<- hcns] & cdhf).
    destruct (allsc (`h)) as [hmode|hmode]; unfold IsSC, IsPln, IsCns, set_map in hmode, hcns.
    1-2: rewrite hcns in hmode; discriminate.
  
  assert (scwloc_acy: acyclic (`↑ restr_eq_rel loc (`↓ (⦗IsWrite⦘ ⨾ `↑ sc)))⁻¹).
    intros x rxx.
    assert (xsc: IsSC x).
      induction rxx as [x y (x''' & y''' & [(y' & [<- yiw] & ([y'' ysc] & x'' & scyx & <- & xx)) xyloc] & <- & <-)|]; simpl; auto.
    set (x' := exist IsSC x xsc).
    apply sc_total_order with x'.
    unfold x'.
    set (ysc := xsc) in |- * at 1.
    set (y := x) in ysc, rxx at 2 |- * at 1.
    clearbody y ysc.
    clear x'.
    induction rxx as [x y (x''' & y''' & [(y' & [<- yiw] & (y'' & x'' & scyx & <- & <-)) xyloc] & <- & <-)|].
    match goal with |- ?m => assert (H: sc y'' x'' = m) end.
      f_equal; apply sig_ext; simpl; reflexivity.
    rewrite <- H.
    assumption.
    eapply sc_total_order; eauto.

  assert (scwloc_wf: well_founded (restr_eq_rel loc (`↓ (⦗IsWrite⦘ ⨾ `↑ sc)))⁻¹).
    assert (scwloc'_wf: well_founded (`↑ restr_eq_rel loc (`↓ (⦗IsWrite⦘ ⨾ `↑ sc)))⁻¹).
      apply acy_wf.
      assumption.
    intros x; specialize (scwloc'_wf (`x)).
    destruct x as [x' xrw]; simpl in scwloc'_wf.
    induction scwloc'_wf as [x' _ IH].
    constructor 1.
    intros y ryx.
    destruct y as [y' yrw].
    set (y := exist _ y' yrw).
    set (x := exist (fun x => ~IsFence x) x' xrw).
    unfold y.
    specialize (IH y') with yrw.
    apply IH.
    do 3 esplit.
    2: esplit; eauto.
    2: change x' with (`x); f_equal.
    2: change y' with (`y); f_equal.
    unfold x, y; assumption.

  exists drf.
  do 2 esplit; [esplit|..].

  apply drf_irr.

  apply transitive_ct.

  admit.

  intros x y sbxy.
  constructor 1; left; auto.

  intros x y rxy.
  repeat esplit.
  eapply rf_write; eauto.
  destruct (allsc (`x)) as [xpln|xsc], (allsc (`y)) as [ypln|ysc].
  1-3: destruct (race_free x y) as [[thrxy r'xy]|[nthrxy r'xy]];
    [apply rf_eq_loc; assumption|left; eapply rf_write; eassumption|..].
  2,4,6: lapply r'xy; clear r'xy; [intros r'xy|auto].
  1-6: destruct r'xy as [<-%sig_ext|[r'xy|r'yx]];
    [exfalso; eapply rf_acy; constructor 1; eauto|..].
  1,9,11: constructor 1; left; assumption.
  1,8,9: apply (or_introl (B := ithb (`y) (`x))) in r'yx.
  4,6,8: apply hb_drf; assumption.
  1-6: apply coherence_rf in r'yx as [_ nrfxy]; contradict nrfxy; do 3 esplit; [|esplit]; eauto.
  set (x' := exist _ (`x) xsc).
  set (y' := exist _ (`y) ysc).
  destruct (sc_tot x' I y' I).
  intros xy; apply (f_equal (@proj1_sig _ _)) in xy; cbn in xy; apply sig_ext in xy; subst y.
  eapply rf_acy; constructor 1; eauto.
  constructor 1; right; repeat esplit; eauto.
  destruct (sc_read_exclusions x y) as [_ excl].
  assumption.
  contradict excl.
  left; left; repeat esplit; eauto.
  apply rf_eq_loc; assumption.
  intros c [(x' & [<- xiw] & drfxc) locxc] [(c' & [<- ciw] & drfcy) loccy].
  destruct (allsc (`x)).
  destruct (race_free x c) as [[thrxc [<-%sig_ext|[sbxc|sbcx]]]|[nthrxc [<-%sig_ext|[hbxc|hbcx]]]]; auto.
  eapply drf_irr; eauto.
  2,4: lapply (hb_drf (`c) (`x)); [|auto; left; auto]; intros drfcx; eapply drf_irr; econstructor 2; eauto.
  apply (or_introl (B := ithb (`x) (`c))) in sbxc; change _ with (hb (`x) (`c)) in sbxc.
  1,2: destruct (race_free x y) as [[thrxy [<-%sig_ext|[sbxy|sbyx]]]|[nthrxy [<-%sig_ext|[hbxy|hbyx]]]];
    [rewrite locxc; rewrite loccy|..]; auto.
  1,6: eapply rf_acy; constructor 1; eauto.
  2,4,6,8: lapply (hb_drf (`y) (`x)); [|auto; left; auto]; intros drfyx; eapply drf_irr;
    econstructor 2; [|econstructor 2]; eauto.
  1,3: apply (or_introl (B := ithb (`x) (`y))) in sbxy; change _ with (hb (`x) (`y)) in sbxy.
  1-4: destruct (coherence_ww (`x) (`c)) as [_ nmocx]; auto.
  1-4: destruct (mo_total_order_per_loc (loc x)) as [_ mo_tot].
  1-4: set (x' := (exist IsWrite (`x) xiw)).
  1-4: set (c' := (exist IsWrite (`c) ciw)).
  1-4: edestruct mo_tot with x' c' as [moxc|mocx];
    [unfold compose, set_map; f_equal; apply sig_ext; reflexivity|
     rewrite locxc; unfold compose, set_map; f_equal; apply sig_ext; reflexivity|
     intros xc; apply (f_equal (@proj1_sig _ _)) in xc; cbn in xc; apply sig_ext in xc; subst c;
       eapply drf_irr; eauto|
     ..|
     contradict nmocx; repeat esplit; eauto].
  1-4: destruct (allsc (`c)).
  1,3,5,7: destruct (race_free c y) as [[thrcy [<-%sig_ext|[sbcy|sbyc]]]|[nthrcy [<-%sig_ext|[hbcy|hbyc]]]]; auto.
  1,14: eapply drf_irr; eauto.
  2,4,6,8,10,12,14,16: lapply (hb_drf (`y) (`c)); [|auto; left; auto]; intros drfyc; eapply drf_irr;
    econstructor 2; eauto.
  1,3,5,7: apply (or_introl (B := ithb (`c) (`y))) in sbcy; change _ with (hb (`c) (`y)) in sbcy.
  1-8: destruct (coherence_wr (`c) (`y)) as [_ nmorfcy]; eauto; contradict nmorfcy; do 4 esplit; eauto.
  1-4: destruct (allsc (`y)).
  1,3,5,7: destruct (race_free c y) as [[thrcy [<-%sig_ext|[sbcy|sbyc]]]|[nthrcy [<-%sig_ext|[hbcy|hbyc]]]]; auto.
  1,14: eapply drf_irr; eauto.
  2,4,6,8,10,12,14,16: lapply (hb_drf (`y) (`c)); [|auto; left; auto]; intros drfyc; eapply drf_irr;
    econstructor 2; eauto.
  1,3,5,7: apply (or_introl (B := ithb (`c) (`y))) in sbcy; change _ with (hb (`c) (`y)) in sbcy.
  1-8: destruct (coherence_wr (`c) (`y)) as [_ nmorfcy]; eauto; contradict nmorfcy; do 4 esplit; eauto.
  1-4: assert (sccy: (restr_eq_rel loc (`↓ (⦗IsWrite⦘ ⨾ `↑ sc)))⁻¹ y c).
    1,3,5,7: set (c'' := (exist _ (`c) H0)).
    1-4: set (y'' := (exist _ (`y) H1)).
    1-4: esplit; [do 2 esplit|]; [esplit|exists c'', y''; esplit; [|esplit]|]; eauto.
    1-4: destruct (sc_tot c'' I y'' I); auto; [
      intros cy; apply (f_equal (@proj1_sig _ _)) in cy; simpl in cy; rewrite cy in drfcy; eapply drf_irr; eauto
    | exfalso; eapply drf_irr; econstructor 2; [apply drfcy|]; constructor 1; right; repeat esplit; eauto].
  1-4: destruct (wf_imm_succ scwloc_wf _ _ sccy) as [eimm immsc].
  1-4: destruct (classic (eimm = c)).
  1,3,5,7: subst eimm.
  1-4: destruct (sc_read_exclusions x y) as [_ excl]; auto; contradict excl; right; do 2 esplit;
    [try apply sbxc; try apply hbxc|].
  1-4: destruct immsc; esplit; eauto.
  assert (IsSC (`eimm)).
    destruct immsc as [[(e'' & [<- eiw] & ([e''' esc] & y''' & scey & <- & yy)) loc] _]; simpl; assumption.
  assert (IsWrite (`eimm)).
  destruct immsc as [[(e'' & [<- eiw] & scey) loc] _]; simpl; assumption.
  assert (locce: loc y = loc eimm).
    destruct immsc as [[scey loc] _]; simpl; eauto.
  rewrite <- loccy in locce.
  pose (c'' := exist _ (`c) H0).
  pose (eimm'' := exist _ (`eimm) H3).
  pose (y'' := exist _ (`y) H1).
  destruct (sc_tot c'' I y'' I); [
    intros [=cy]; apply sig_ext in cy; subst c; eapply drf_irr; eauto|..|
    eapply drf_irr; econstructor 2; [apply drfcy|constructor 1; right; repeat esplit; eauto]].
  destruct (sc_tot c'' I eimm'' I); [
    intros [=ce]; contradict H2; apply sig_ext in ce; auto | .. |
    unshelve eapply immsc; [apply c|..]; esplit; eauto;
      [exists (`c)|exists (`eimm)]; esplit;
      [|exists c'', y''|..|exists eimm'', c'']; repeat esplit; eauto ].
  destruct (race_free x eimm) as [[thrxe [<-%sig_ext|[sbxe|sbex]]]|[nthrxe [<-%sig_ext|[hbxe|hbex]]]].
  assert (hb (`x) (`eimm)).
    eapply coherence_ww.
    destruct 
Qed.


(*
[ Note: memory_order_seq_cst ensures sequential consistency only for a program that is free of data races
and uses exclusively memory_order_seq_cst operations. Any use of weaker ordering will invalidate this
guarantee unless extreme care is used. In particular, memory_order_seq_cst fences ensure a total order only
for the fences themselves. Fences cannot, in general, be used to restore sequential consistency for atomic
operations with weaker ordering specifications. — end note ]
*)

(*
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

[ Note: The value observed by a load of an atomic depends on the “happens before” relation, which depends
on the values observed by loads of atomics. The intended reading is that there must exist an association of
atomic loads with modifications they observe that, together with suitably chosen modification orders and
the “happens before” relation derived as described above, satisfy the resulting constraints as imposed here.
— end note ]
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

Implementations should make atomic stores visible to atomic loads within a reasonable amount of time.

template <class T>
T kill_dependency( T y) noexcept ;
Effects: The argument does not carry a dependency to the return value (4. 7) .
Returns: y.
*)
