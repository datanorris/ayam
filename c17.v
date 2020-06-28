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

Notation " ` r " := ((@proj1_sig _ _) ↑ r) : function_scope.
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
*)

Inductive Loc :=
  loc_atomic (n: nat)
| loc_nonatomic (n: nat).

Definition Thread := nat.

Inductive Op' :=
| init (l: Loc) (* 1 initialise to 0 per oject *)
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
    init _
  | write _ _ _ _
  | fence _ _ _ => _
  | read _ _ _ f
  | rmw _ _ _ f => fun _ => f
  end (proj2_sig o).

Definition mode' (o: Op') :=
  match o with
    init => 
    read _ _ (exist _ m _) _
  | write _ _ (exist _ m _) _
  | fence _ _ (exist _ m _)
  | rmw _ _ (exist _ m _) _ => m
  end.

Definition IsAtomic' (o': Op') := mode' o' <> mPln.
Definition IsAtomicLoc (l: Loc) :=
  match l with
    loc_atomic _ => true
  | loc_nonatomic _ => false
  end.

Conjecture events': Op' -> Prop.
Conjecture events'_finite: set_finite events'.

Program Fixpoint OP_WF' (o: Op'): Prop :=
  ⟪op_event: events' o⟫ /\
  ⟪op_reads_from_write: forall s: IsRead' o, IsWrite' (from' o)⟫ /\
  ⟪op_from_wf': forall s: IsRead' o, OP_WF' (from' o)⟫.

Definition loc'
  (o: Op')
  (NF: ~IsFence' o)
  (wf: OP_WF' o): Loc.
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

Program Fixpoint OP_WF (o: Op'): Prop :=
  exists
    (wf': OP_WF' o),
    ⟪op_atomicity: forall s: IsRead' o \/ IsWrite' o,
      IsAtomic' o <-> IsAtomicLoc (loc' o _ _)⟫ /\
    ⟪op_from_wf: forall s: IsRead' o, OP_WF (from' o)⟫.
Next Obligation.
  destruct o; intuition.
Defined.

Definition Op := { o: Op' | OP_WF o }.

Definition mode (o: Op) :=
  mode' (`o).

Definition IsAtomic (o: Op) := IsAtomic' (`o).
Definition IsARead (o: Op) := IsAtomic o /\ IsRead' (`o).
Definition IsAWrite (o: Op) := IsAtomic o /\ IsWrite' (`o).
Definition IsFence (o: Op) := IsFence' (`o).
Definition IsRMW (o: Op) := IsRMW' (`o).

Definition ARead := { o: Op | IsARead o }.
Definition AWrite := { o: Op | IsAWrite o }.
Definition Fence := { o: Op | IsFence o }.
Definition AReadWrite := { o: Op | IsAtomic o /\ ~IsFence o }.

Definition AR2RW (o: ARead): AReadWrite.
Proof.
  destruct o as [owf [a r]].
  exists owf.
  destruct owf as [[]].
  all: repeat split; auto.
Defined.

Definition AW2RW (o: AWrite): AReadWrite.
Proof.
  destruct o as [owf [a w]].
  exists owf.
  destruct owf as [[]].
  all: repeat split; auto.
Defined.

Definition IsRel (o: Op) := In (mode o) [mRel;mAcqRel;mSc].
Definition IsAcq (o: Op) := In (mode o) [mAcq;mAcqRel;mSc].
Definition IsSC (o: Op) := mode o = mSc.

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

Program Definition loc (o: AReadWrite) :=
  loc' (``o) _ _.
Next Obligation.
  destruct o as [[o wf] [a nf]]; auto.
Defined.
Next Obligation.
  destruct o as [[o wf] [a nf]]; auto.
  destruct o; destruct wf; auto.
Defined.

Program Definition from (o: ARead): AWrite :=
  from' (``o).
Next Obligation. (* IsRead' (``o) *)
  case (o) as [[o' wf] [a r]]; auto.
Defined.
Next Obligation. (* OP_WF (from' (``o)) *)
  case (o) as [[[] (wf' & atom & fwf)]].
  all: apply fwf.
Defined.
Next Obligation. (* IsAWrite (from' (``o)) *)
  pose (o' := ``o).
  destruct o as [[[] wf] [ia ir]].
  all: destruct wf as ((ev & rfw & fwf') & atomloc & fwf).
  all: split; unfold IsAtomic in *.
  all: simpl in ia, ir, o' |- *.
  1,2,5,6: discriminate ir.
  all: specialize (rfw eq_refl) as rfw_.
  all: specialize (fwf eq_refl) as fwf_.
  2,4: assumption.
  all: destruct from, (fwf eq_refl) as (ffwf' & fatomloc & ffwf).
  2,3,6,7: discriminate rfw_.
  all: specialize (atomloc (or_introl eq_refl)).
  all: specialize (fatomloc (or_intror eq_refl)).
  all: assert (ffwf' = fwf' eq_refl).
  1,3,5,7: apply proof_irrelevance.
  all: subst ffwf'.
  all: eapply fatomloc.
  all: eapply atomloc.
  all: assumption.
Defined.

(*
SB:
Sequenced before is an asymmetric, transitive, pair-wise relation between evaluations executed by a single
thread, which induces a partial order among those evaluations.
*)

Conjecture sb: relation Op.
Conjecture sb_order: strict_partial_order sb.

(*
Do we need to model threads? 2 actions on the same thread are not "potentially concurrent" unless in a signal handler,
so if they are unsequenced and conflict it's undefined. So 2 reads to the same location, or 2 actions on different
locations, can be unsequenced.
    
Conjecture thread: Op -> nat.
Conjecture sb_same_thread: forall x y, sb x y -> thread x = thread y.
*)

(*
MO:
All modifications to a particular atomic object M occur in some particular total order, called the modification
order of M. [ Note: There is a separate order for each atomic object. There is no requirement that these can
be combined into a single total order for all objects. In general this will be impossible since different threads
may observe modifications to different objects in inconsistent orders. — end note ]

*)

Conjecture mo: relation AWrite.
Conjecture mo_same_loc_only: mo ≡ restr_eq_rel (loc ∘ AW2RW) mo.
Conjecture mo_total_order_per_loc: forall l: Loc, strict_total_order (fun x => (loc ∘ AW2RW) x = l) mo.

(*
RS:
A release sequence headed by a release operation A on an atomic object M is a maximal contiguous subsequence of
side effects in the modification order of M, where the first operation is A, and every subsequent operation
 — is performed by the same thread that performed A, or
 — is an atomic read-modify-write operation.
*)

Definition rs :=
  let mo' := (`mo)%rel in
  fun x y =>
    (⦗IsRel⦘ ⨾ mo'^?) x y /\
    forall z, mo' x z -> mo'^? z y ->
      sb^⋈ x z \/ IsRMW z.

(*
READ FROM
*)

Program Definition rf: relation Op :=
  fun w r => 
    exists (iw: IsAWrite w) (ir: IsARead r), w = from r.
Next Obligation.
  destruct r; auto.
Qed.

Lemma rf_acy: acyclic rf.
Proof.
  assert (d:
    forall x y, rf⁺ x y ->
      rf x y \/ exists (ir: IsARead y), rf⁺ x (proj1_sig (from (exist _ y ir)))).
    intros x y rxy.
    induction rxy.
    left; auto.
    right.
    destruct IHrxy2 as [(iw & ir & ryz)|[ir ryz]].
    assert (zeq: exist (fun o : Op' => OP_WF o) (` z) (rf_obligation_1 z ir) = z).
      apply sig_ext.
      auto.
    assert (zeq2:
      exist _
        (exist (fun o : Op' => OP_WF o) (` z) (rf_obligation_1 z ir))
        (rf_obligation_2 z ir) =
      exist _
        z
        (eq_rect _ (fun x => IsARead x) (rf_obligation_2 z ir) _ zeq)).
      apply sig_ext.
      apply sig_ext.
      auto.
    assert (ryz2 := eq_rect _ (fun x => y = proj1_sig (from x)) ryz _ zeq2).
    hnf in ryz2.
    rewrite ryz2 in rxy1.
    eexists; eauto.
    exists ir.
    constructor 2 with y; auto.
  intros x rxx.
  remember rxx as rxy.
  remember x as y in rxy at 2.
  clear Heqy Heqrxy.
  destruct y as [y wf].
  induction y.

  specialize (d _ _ rxy) as [(iw & [ia ir] & deq)|([ia ir] & rxf)].
  1,2: discriminate ir.

  specialize (d _ _ rxy) as [(iw & [ia ir] & deq)|([ia ir] & rxf)].
  unfold from, from' in deq; simpl in deq.
  eapply IHy.
  replace x in rxx at 2.
  eauto.
  unfold from, from' in rxf; simpl in rxf.
  eapply IHy.
  eauto.

  specialize (d _ _ rxy) as [(iw & [ia ir] & deq)|([ia ir] & rxf)].
  1,2: discriminate ir.

  specialize (d _ _ rxy) as [(iw & [ia ir] & deq)|([ia ir] & rxf)].
  unfold from, from' in deq; simpl in deq.
  eapply IHy.
  replace x in rxx at 2.
  eauto.
  unfold from, from' in rxf; simpl in rxf.
  eapply IHy.
  eauto.
Qed.

(*
RMW-ATOMIC:
Atomic read-modify-write operations shall always read the last value (in the modification order) written
before the write associated with the read-modify-write operation.
*)

Conjecture rmw_atomic: rf ⨾ ⦗IsRMW⦘ ⊆ (` (immediate mo))%rel.

(*
FENCE

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
*)

a sw b if a sb x rs_fence y sb b
a sw b if a sb x rs_fence x

(*
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

Definition sw: relation Op :=
  ⦗IsRel⦘ ⨾ rs^? ⨾ rf ⨾ ⦗IsAcq⦘.

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
(*| ithb_dob (r: dob x y)*)
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
  (sb^? ⨾ ((* dob ∪ *)(sw ⨾ sb^?)))⁺.

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

(*
INIT:

Variables with static storage duration are initialized as a consequence of program initiation. Variables with
thread storage duration are initialized as a consequence of thread execution. Within each of these phases of
initiation, initialization occurs as follows.

Together, zero-initialization and constant initialization are called static initialization;
all other initialization is dynamic initialization.

All static initialization strongly happens before (4.7.1) any dynamic initialization. [ Note: The dynamic
initialization of non-local variables is described in 6.6.3; that of local static variables is described in
9.7. — end note ]

Initializing atomic objects is non-atomic.
*)

Definition shb := (sb ∪ sw)⁺.

(*
COHERENCE:
The value of an atomic object M, as determined by evaluation B, shall be the value stored by some side effect
A that modifies M, where B does not happen before A. [ Note: The set of such side effects is also restricted
by the rest of the rules described here, and in particular, by the coherence requirements below. — end note ]
*)

Conjecture coherence_rf: hb ⊆ hb \ rf⁻¹.

(*
COHERENCE:
If an operation A that modifies an atomic object M happens before an operation B that modifies M, then
A shall be earlier than B in the modification order of M. [ Note: This requirement is known as write-write
coherence. — end note ]
*)

Conjecture coherence_ww: hb ⊆ hb \ (`mo⁻¹)%rel.

(*
COHERENCE:
If a value computation A of an atomic object M happens before a value computation B of M, and A takes
its value from a side effect X on M, then the value computed by B shall either be the value stored by X or
the value stored by a side effect Y on M, where Y follows X in the modification order of M. [ Note: This
requirement is known as read-read coherence. — end note ]
*)

Conjecture coherence_rr: @proj1_sig _ _ ↓ hb ⊆ @proj1_sig _ _ ↓ hb \ from ↓ mo⁻¹.

(*
COHERENCE:
If a value computation A of an atomic object M happens before an operation B that modifies M, then A
shall take its value from a side effect X on M, where X precedes B in the modification order of M. [ Note:
This requirement is known as read-write coherence. — end note ]
*)

Conjecture coherence_rw: hb ⊆ hb \ (rf⁻¹ ⨾ `mo)%rel.

(*
COHERENCE:
If a side effect X on an atomic object M happens before a value computation B of M, then the evaluation B
shall take its value from X or from a side effect Y that follows X in the modification order of M. [ Note: This
requirement is known as write-read coherence. — end note ]
*)

Conjecture coherence_wr: hb ⊆ hb \ (`mo⁻¹ ⨾ rf)%rel.

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

Conjecture sc_fence_1: rf ⊆ rf \ (`mo ⨾ `sc ⨾ ⦗IsFence⦘ ⨾ sb)%rel.
Conjecture sc_fence_2: rf ⊆ rf \ (`mo ⨾ sb ⨾ ⦗IsFence⦘ ⨾ `sc)%rel.
Conjecture sc_fence_3: rf ⊆ rf \ (`mo ⨾ sb ⨾ ⦗IsFence⦘ ⨾ `sc ⨾ ⦗IsFence⦘ ⨾ sb)%rel.

(*
SC-Fence:
For atomic modifications A and B of an atomic object M, B occurs later than A in the modification order of
M if:
 — there is a memory_order_seq_cst fence X such that A is sequenced before X, and X precedes B in S, or
 — there is a memory_order_seq_cst fence Y such that Y is sequenced before B, and A precedes Y in S, or
 — there are memory_order_seq_cst fences X and Y such that A is sequenced before X, Y is sequenced
before B, and X precedes Y in S.
*)



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

SC-PER-LOC:
[ Note: The four preceding coherence requirements effectively disallow compiler reordering of atomic operations
to a single object, even if both operations are relaxed loads. This effectively makes the cache coherence
guarantee provided by most hardware available to C++ atomic operations. — end note ]

[ Note: The value observed by a load of an atomic depends on the “happens before” relation, which depends
on the values observed by loads of atomics. The intended reading is that there must exist an association of
atomic loads with modifications they observe that, together with suitably chosen modification orders and
the “happens before” relation derived as described above, satisfy the resulting constraints as imposed here.
— end note ]

*)
(*
RACE:
If a side effect on a memory location (4. 4) is unsequenced relative to either another side effect on the same memory location or a
value computation using the value of any object in the same memory location, and they are not potentially
concurrent, the behavior is undefined

Two expression evaluations conflict if one of them modifies a memory location (4. 4) and the other one reads
or modifies the same memory location.

Two actions are potentially concurrent if
 — they are performed by different threads, or
 — they are unsequenced, at least one is performed by a signal handler, and they are not both performed
by the same signal handler invocation.

The execution of a program contains a data race if it contains two potentially concurrent conflicting actions ,
at least one of which is not atomic, and neither happens before the other, except for the special case for
signal handlers described below. Any such data race results in undefined behavior.
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

DOB:
An evaluation A is dependency-ordered before an evaluation B if
 — A performs a release operation on an atomic object M, and, in another thread, B performs a consume
operation on M and reads a value written by any side effect in the release sequence headed by A, or
 — for some evaluation X, A is dependency-ordered before X and X carries a dependency to B.
[ Note: The relation “ is dependency-ordered before” is analogous to “ synchronizes with”, but uses release/ -
consume in place of release/acquire. — end note ]




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
