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
| rmw (uid: nat) (t: Thread) (m: Mode | In m [mAcq;mRel;mAcqRel;mSc]) (from: Op').

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

Definition IsRel (o: Op) := In (mode o) [mRel;mAcqRel;mSc].
Definition IsAcq (o: Op) := In (mode o) [mAcq;mAcqRel;mSc].
Definition IsSC (o: Op) := mode o = mSc.
Definition IsCns (o: Op) := mode o = mCns.

(*
Fixpoint rf_chain_length (o: Op') :=
  match o with
    write _ _
  | fence _ => 0
  | read _ f
  | rmw _ f => 1 + (rf_chain_length f)
  end.
*)

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

Don't think there is harm in including non-atomic objects in this. They are necessarily totally ordered anyway.
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

Assume the operator conditions are modelled as read-froms
*)

Definition cd := (rf ∩ (`↓ sb))⁺.

(*
RMW-ATOMIC:
Atomic read-modify-write operations shall always read the last value (in the modification order) written
before the write associated with the read-modify-write operation.
*)

Conjecture rmw_atomic: `↑ rf ⨾ ⦗IsRMW⦘ ⊆ `↑ (immediate mo).

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
  ⦗IsRel⦘ ⨾ (⦗IsFence⦘ ⨾ sb)^? ⨾ `↑ rs_fence ⨾ `↑ rf ⨾ (sb ⨾ ⦗IsFence⦘)^? ⨾ ⦗IsAcq⦘.

(*
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
*)

(*
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

(*
Program Fixpoint ithb' x y {measure x (sb⁻¹)} :=
  sw x y \/
  (*dob \/*)
  (sw ⨾ sb) x y \/
  exists c
    (p: sb x c), ithb' c y.
Next Obligation.
  unfold MR; simpl.
  lapply (acy_wf sb⁻¹).
  intros wf [x xp]; revert xp.
  induction x using (well_founded_induction (wf)).
  constructor 1.
  intros [y yp] rxy.
  apply H.
  auto.
  destruct (sb_order) as [irr tra].
  intros x rxx.
  apply -> clos_trans_of_transitive in rxx.
  apply irr with x; auto.
  intros e f g ref reg.
  apply tra with f; auto.
Qed.
*)

Definition ithb_alt: relation Op :=
  (sb^? ⨾ (`↑ dob ∪ (sw ⨾ sb^?)))⁺.

(*
HB:
An evaluation A happens before an evaluation B (or, equivalently, B happens after A) if:
 — A is sequenced before B, or
 — A inter-thread happens before B.
The implementation shall ensure that no program execution demonstrates a cycle in the “happens before”
relation. [ Note: This cycle would otherwise be possible only through the use of consume operations. — end
note ]
*)

Definition hb := sb ∪ ithb.

(*
SHB:
An evaluation A strongly happens before an evaluation B if either
 — A is sequenced before B, or
 — A synchronizes with B, or
 — A strongly happens before X and X strongly happens before B.
[ Note: In the absence of consume operations, the happens before and strongly happens before relations are
identical. Strongly happens before essentially excludes consume operations. — end note ]
*)

Definition shb := (sb ∪ sw)⁺.


(* can we assume the following for non-atomic too? surely non-atomics are SC-local too *)

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
  (*
  assert (tra_sclp: forall P, transitive (proj1_sig (P:=P) ↓ scl)).
    intros P x y z rxy ryz.
    esplit.
    apply sig_ext.
  *)

  (*
  assert (tra_sclloc: forall l, transitive (restr_rel (loc ↓₁ eq l) scl)).
    intros l x y z [rxy [xloc yloc]] [ryz [_ zloc]].
    esplit; auto.
    eapply transitive_ct; eauto.

  assert (scrt_loc: forall l x y dom,
    tot_ext (filter (eqb_loc l) dom) (restr_rel (loc ↓₁ eq l) scl) x y ->
    loc x = l).
    intros l x y dom rxy.
    revert x y rxy.
    induction dom.
    intros x y rxy.
    simpl in rxy.
    apply -> clos_trans_of_transitive in rxy; auto.
    destruct rxy as [rxy [xloc yloc]]; auto.
    intros x y rxy.
    simpl in rxy.
    destruct (eqb_loc l a) eqn:aeq.
    simpl in rxy.
    destruct rxy as [rxy|[rxa rnya]].
    apply (IHdom x y).
    apply clos_trans_of_transitive; auto.
    apply tot_ext_trans.
    apply clos_refl_transE in rxa as [<-|rxa].
    apply PeanoNat.Nat.eqb_eq in aeq; auto.
    eapply IHdom.
    eapply clos_trans_of_transitive; eauto.
    apply tot_ext_trans.
    eapply IHdom; eauto.
  *)

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
SHB acyclic
- sb is acyclic
- sw joins threads with certain mo* ⨾ rf release sequence
  - release sequence is a subset of sb* ⨾ rmw* ⨾ rf
  - the first rmw* happens after all previous things (sb ⊆ shb)
  - the subsequent rmw* must not happen before the first write (coherence_ww)
  - the read must not happen before the last rmw* (coherence_rf)
  - the read must not happen before the first rmw (coherence_rw)
  - the last element of sw must not happen before the first element (sb ⊆ shb)
  - any later writes to the same location in shb:
    - must not happen before the first rmw* (coherence_ww)
    - must not happen before any rmw* (rmw_atomic)
*)

Lemma shb_acy: acyclic shb.
Proof.
  assert (shbb: shb ≡ (sb ∪ (sb^? ⨾ sw ⨾ sb^?)⁺)); [split|].
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
  assert (shb_hb: shb ⊆ hb).
    intros x y [sbxy|shbbxy]%shbb.
    left; auto.
    right.
    induction shbbxy as [x y (e & [<-|sbxe] & f & swef & [->|sbfz])|x z y rxz IHxz rzy IHzy].
    constructor 1; auto.
    constructor 3; esplit; esplit; eauto.
    constructor 4; esplit; esplit; [|constructor 1]; eauto.
    constructor 4; esplit; esplit; [|constructor 3; esplit; esplit]; eauto.
    constructor 5; esplit; esplit; eauto.
  assert (sw_nshb: forall x y, (sb^? ⨾ sw ⨾ sb^?) x y -> ~ shb^? y x).
    intros w z (x & sbwx & y & swxy & sbyz) rzw.
    destruct swxy as (x' & [<- xrel] & e & sbxe & f & (e' & f' & rsef & <- & <-) & g & rffg & y' & sbgy & [-> yacq]).
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
  (*
  assert (shbs_nshbs: forall x y (rxy: shbs x y), ~shb^? y x).
    intros x y rxy ryx.
    destruct rxy as [sbxy|swxy], ryx as [<-|shbyx].
    eapply sb_order; eauto.
    do 2 eapply sb_order; eauto.
    apply sw_nshb in swyx; apply swyx; right; constructor 1; left; auto.
    apply sw_nshb in swxy; apply swxy; left; auto.
    1,2: apply sw_nshb in swxy; apply swxy; right; constructor 1.
    left; auto.
    right; auto.
  *)
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
Conjecture sc_consistent: (`sc ⊆ `sc \ (hb ∪ `mo)⁻¹)%rel.
Conjecture sc_read_exclusions: rf ⊆ rf \ (`sc⁻¹ ∪ (`sc ∩ `mo) ⨾ (`sc ∩ `mo) ∪ hb ⨾ immediate (`sc ∩ `mo))%rel.

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

Conjecture sc_fence_1: rf ⊆ rf \ (`mo ⨾ `sc ⨾ ⦗IsFence⦘ ⨾ sb ⨾ ⦗IsAtomic⦘)%rel.
Conjecture sc_fence_2: rf ⊆ rf \ (`mo ⨾ ⦗IsAtomic⦘ ⨾ sb ⨾ ⦗IsFence⦘ ⨾ `sc)%rel.
Conjecture sc_fence_3: rf ⊆ rf \ (`mo ⨾ ⦗IsAtomic⦘ ⨾ sb ⨾ ⦗IsFence⦘ ⨾ `sc ⨾ ⦗IsFence⦘ ⨾ sb ⨾ ⦗IsAtomic⦘)%rel.

(*
SC-Fence:
For atomic modifications A and B of an atomic object M, B occurs later than A in the modification order of
M if:
 — there is a memory_order_seq_cst fence X such that A is sequenced before X, and X precedes B in S, or
 — there is a memory_order_seq_cst fence Y such that Y is sequenced before B, and A precedes Y in S, or
 — there are memory_order_seq_cst fences X and Y such that A is sequenced before X, Y is sequenced
before B, and X precedes Y in S.
*)

Conjecture sc_fence_4: (`mo ⊆ `mo \ (⦗IsAtomic⦘ ⨾ sb ⨾ ⦗IsFence⦘ ⨾ `sc)⁻¹)%rel.
Conjecture sc_fence_5: (`mo ⊆ `mo \ (`sc ⨾ ⦗IsFence⦘ ⨾ sb ⨾ ⦗IsAtomic⦘)⁻¹)%rel.
Conjecture sc_fence_6: (`mo ⊆ `mo \ (⦗IsAtomic⦘ ⨾ sb ⨾ ⦗IsFence⦘ ⨾ `sc ⨾ ⦗IsFence⦘ ⨾ sb ⨾ ⦗IsAtomic⦘)⁻¹)%rel.

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
    IsWrite x \/ IsWrite y ->
    thread x = thread y /\ sb^⋈? x y \/
    thread x <> thread y /\ (~IsAtomic x \/ ~IsAtomic y) /\ hb^⋈? x y.
    (*same thread /\ ~sb_sym x y,
      diff thread /\ (~IsAtomic x \/ ~IsAtomic y) /\ ~hb_sym x y.*)

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

The value of an object visible to a thread T at a particular point is the initial value of the object, a value
assigned to the object by T, or a value assigned to the object by another thread, according to the rules
below.

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
