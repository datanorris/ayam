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

Require Import List.
Require Import RelationClasses.
From hahn Require Import Hahn.

Inductive Mode := 
| pln
| rlx
| cns
| acq
| rel
| acqrel
| sc.

Definition Loc := nat.

Inductive Op :=
| write (m: {m: Mode | In m (pln::rlx::rel::acqrel::sc::nil)}) (l: Loc)
| read (m: {m: Mode | In m (pln::rlx::cns::acq::acqrel::sc::nil)}) (from: Op)
| fence (m: {m: Mode | In m (acq::rel::acqrel::sc::nil)})
| rmw (m: {m: Mode | In m (acq::rel::acqrel::sc::nil)}) (from: Op).

Definition IsRead (o: Op) :=
  match o with
    read _ _
  | rmw _ _ => true
  | _ => false
  end.
Definition IsWrite (o: Op) :=
  match o with
    write _ _
  | rmw _ _ => true
  | _ => false
  end.
Definition IsFence (o: Op) :=
  match o with
    fence _ => true
  | _ => false
  end.
Definition IsRMW (o: Op) :=
  match o with
    rmw _ _ => true
  | _ => false
  end.

Definition mode (o: Op) :=
  match o with
    read (exist _ m _) _
  | write (exist _ m _) _
  | fence (exist _ m _)
  | rmw (exist _ m _) _ => m
  end.

Definition from (o: Op) (WF: IsRead o) :=
  match o, WF
  with
    write _ _, WF'
  | fence _, WF' => match hahn__not_false_is_true WF' with end
  | read _ f, WF'
  | rmw _ f, WF' => f
  end.

Conjecture op_reads_from_write: forall (o: Op) (r: IsRead o), IsWrite (from o r).

Lemma write_not_fence (o: Op) (W: IsWrite o): ~IsFence o.
Proof
  match o
    return IsWrite o -> ~IsFence o
  with
    write _ _
  | rmw _ _ => fun _ => hahn__not_false_is_true
  | read _ _ => fun _ => hahn__not_false_is_true
  | fence _ => fun W' => match hahn__not_false_is_true W' with end
  end W.

Fixpoint loc (o: Op) (WF: ~IsFence o) :=
  match o, WF
  with
    write _ l as o', WF' => l
  | read _ f as o', WF'
  | rmw _ f as o', WF' => loc f (write_not_fence _ (op_reads_from_write o' eq_refl))
  | fence _ as o', WF' => match WF' eq_refl with end
  end.

(*
SB:
Sequenced before is an asymmetric, transitive, pair-wise relation between evaluations executed by a single
thread, which induces a partial order among those evaluations.
*)

Conjecture sb: relation Op.
Conjecture StrictOrder_sb: StrictOrder sb.

(* Do we need to model threads? *)
    
Conjecture thread: Op -> nat.
Conjecture sb_same_thread: forall x y, sb x y -> thread x = thread y.

(*
MO:
All modifications to a particular atomic object M occur in some particular total order, called the modification
order of M. [ Note: There is a separate order for each atomic object. There is no requirement that these can
be combined into a single total order for all objects. In general this will be impossible since different threads
may observe modifications to different objects in inconsistent orders. — end note ]
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

RS:
A release sequence headed by a release operation A on an atomic object M is a maximal contiguous subsequence of
side effects in the modification order of M, where the first operation is A, and every subsequent operation
 — is performed by the same thread that performed A, or
 — is an atomic read-modify-write operation.

SW:
Certain library calls synchronize with other library calls performed by another thread. For example, an
atomic store-release synchronizes with a load-acquire that takes its value from the store (32. 4). [ Note: Except
in the specified cases, reading a later value does not necessarily ensure visibility as described below. Such a
requirement would sometimes interfere with efficient implementation. —end note ] [ Note: The specifications
of the synchronization operations define when one reads the value written by another. For atomic objects ,
the definition is clear. All operations on a given mutex occur in a single total order. Each mutex acquisition
“ reads the value written” by the last mutex release. — end note ]

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

HB:
An evaluation A happens before an evaluation B (or, equivalently, B happens after A) if:
 — A is sequenced before B, or
 — A inter-thread happens before B.
The implementation shall ensure that no program execution demonstrates a cycle in the “happens before”
relation. [ Note: This cycle would otherwise be possible only through the use of consume operations. — end
note ]

SHB:
An evaluation A strongly happens before an evaluation B if either
 — A is sequenced before B, or
 — A synchronizes with B, or
 — A strongly happens before X and X strongly happens before B.
[ Note: In the absence of consume operations, the happens before and strongly happens before relations are
identical. S trongly happens before essentially excludes consume operations. — end note ]

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

COHERENCE:
The value of an atomic object M, as determined by evaluation B, shall be the value stored by some side effect
A that modifies M, where B does not happen before A. [ Note: The set of such side effects is also restricted
by the rest of the rules described here, and in particular, by the coherence requirements below. — end note ]

COHERENCE:
If an operation A that modifies an atomic object M happens before an operation B that modifies M, then
A shall be earlier than B in the modification order of M. [ Note: This requirement is known as write-write
coherence. — end note ]

COHERENCE:
If a value computation A of an atomic object M happens before a value computation B of M, and A takes
its value from a side effect X on M, then the value computed by B shall either be the value stored by X or
the value stored by a side effect Y on M, where Y follows X in the modification order of M. [ Note: This
requirement is known as read-read coherence. — end note ]

COHERENCE:
If a value computation A of an atomic object M happens before an operation B that modifies M, then A
shall take its value from a side effect X on M, where X precedes B in the modification order of M. [ Note:
This requirement is known as read-write coherence. — end note ]

COHERENCE:
If a side effect X on an atomic object M happens before a value computation B of M, then the evaluation B
shall take its value from X or from a side effect Y that follows X in the modification order of M. [ Note: This
requirement is known as write-read coherence. — end note ]

SC-PER-LOC:
[ Note: The four preceding coherence requirements effectively disallow compiler reordering of atomic operations
to a single object, even if both operations are relaxed loads. This effectively makes the cache coherence
guarantee provided by most hardware available to C++ atomic operations. — end note ]

[ Note: The value observed by a load of an atomic depends on the “happens before” relation, which depends
on the values observed by loads of atomics. The intended reading is that there must exist an association of
atomic loads with modifications they observe that, together with suitably chosen modification orders and
the “happens before” relation derived as described above, satisfy the resulting constraints as imposed here.
— end note ]



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

SW:
An atomic operation A that performs a release operation on an atomic object M synchronizes with an atomic
operation B that performs an acquire operation on M and takes its value from any side effect in the release
sequence headed by A.

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

Fence:
For atomic modifications A and B of an atomic object M, B occurs later than A in the modification order of
M if:
 — there is a memory_order_seq_cst fence X such that A is sequenced before X, and X precedes B in S, or
 — there is a memory_order_seq_cst fence Y such that Y is sequenced before B, and A precedes Y in S, or
 — there are memory_order_seq_cst fences X and Y such that A is sequenced before X, Y is sequenced
before B, and X precedes Y in S.

[ Note: memory_order_seq_cst ensures sequential consistency only for a program that is free of data races
and uses exclusively memory_order_seq_cst operations. Any use of weaker ordering will invalidate this
guarantee unless extreme care is used. In particular, memory_order_seq_cst fences ensure a total order only
for the fences themselves. Fences cannot, in general, be used to restore sequential consistency for atomic
operations with weaker ordering specifications. — end note ]

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

RMW-ATOMIC:
Atomic read-modify-write operations shall always read the last value (in the modification order) written
before the write associated with the read-modify-write operation.

Implementations should make atomic stores visible to atomic loads within a reasonable amount of time.

template <class T>
T kill_dependency( T y) noexcept ;
Effects: The argument does not carry a dependency to the return value (4. 7) .
Returns: y.
*)