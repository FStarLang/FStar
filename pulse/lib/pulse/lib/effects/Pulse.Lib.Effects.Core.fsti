module Pulse.Lib.Effects.Core

(* Graded computation trees with intrinsic abortive ownership.
   Trees describe code, not owned resumptions.
   Their grade bounds embedded computations, independently of the grade of
   operation implementations used when interpreting them. *)

open Pulse.Lib.Core

type grade = | Terminating | MayDiverge

let join (g h:grade) : grade =
  match g, h with Terminating, Terminating -> Terminating | _ -> MayDiverge

let below (g h:grade) : bool =
  match g, h with MayDiverge, Terminating -> false | _ -> true

let comp (g:grade) (a:Type0) (p:slprop) (q:a -> slprop) =
  match g with
  | Terminating -> stt a p (fun x -> q x)
  | MayDiverge -> stt_div a p (fun x -> q x)

type empty =

// Abortive operations cannot hide a continuation or its private ownership.
// Their empty reply type is exposed only to the generic interpreter interface.
noeq type operation =
  | Returning : input:Type0 -> output:Type0 ->
      request:(input -> slprop) -> reply:(input -> output -> slprop) -> operation
  | Aborting : input:Type0 -> request:(input -> slprop) -> operation

let input (op:operation) : Type0 =
  match op with Returning i _ _ _ -> i | Aborting i _ -> i

let output (op:operation) : Type0 =
  match op with Returning _ o _ _ -> o | Aborting _ _ -> empty

let request (op:operation) : input op -> slprop =
  match op with Returning _ _ p _ -> p | Aborting _ p -> p

let reply (op:operation) : input op -> output op -> slprop =
  match op with
  | Returning _ _ _ q -> q
  | Aborting _ _ -> fun _ impossible -> match impossible with

let signature (tag:Type0) = tag -> operation
let empty_ops : signature empty = fun impossible -> match impossible with

// The grade is an upper bound: even Return and Abort may inhabit MayDiverge.
// All continuation branches obey that bound; it is not a runtime tree scan.
noeq type tree (#tag:Type0) (ops:signature tag) (g:grade) (a:Type0)
  : slprop -> (a -> slprop) -> Type =
  | Return : #q:(a -> slprop) -> x:a -> tree ops g a (q x) q
  | Step : #p:slprop -> #q:(a -> slprop) -> #b:Type0 -> #s:(b -> slprop) ->
      action:(unit -> comp g b p s) ->
      next:(x:b -> tree ops g a (s x) q) ->
      tree ops g a p q
  | Perform : #q:(a -> slprop) -> #frame:slprop ->
      op:tag{Returning? (ops op)} -> arg:input (ops op) ->
      next:(y:output (ops op) ->
        tree ops g a (reply (ops op) arg y ** frame) q) ->
      tree ops g a (request (ops op) arg ** frame) q
  | Abort : #q:(a -> slprop) ->
      op:tag{Aborting? (ops op)} -> arg:input (ops op) ->
      tree ops g a (request (ops op) arg) q

// Computation-algebra operations select existing Pulse rules by grade.
// There is no coercion from a potentially divergent action to a terminating one.
inline_for_extraction
val frame_comp (#a:Type0) (g:grade) (#p:slprop) (#q:a -> slprop)
  (f:slprop) (action:comp g a p q)
  : comp g a (p ** f) (fun x -> q x ** f)

inline_for_extraction
val lift_comp (#a:Type0) (#g:grade) (h:grade{below g h})
  (#p:slprop) (#q:a -> slprop) (action:comp g a p q)
  : comp h a p q

val ghost_comp (g:grade) (#p #q:slprop)
  (proof:unit -> stt_ghost unit emp_inames p (fun _ -> q))
  : comp g unit p (fun _ -> q)

// Widening and sequencing preserve all operation protocols. A mixed-grade bind
// takes the join; a terminating subtree can always enter a divergent context.
inline_for_extraction
val weaken_grade (#tag:Type0) (#ops:signature tag) (#g:grade)
  (#a:Type0) (#p:slprop) (#q:a -> slprop) (h:grade{below g h})
  (c:tree ops g a p q)
  : Tot (tree ops h a p q) (decreases c)

inline_for_extraction
val lift (#tag:Type0) (#ops:signature tag) (#g:grade)
  (#a:Type0) (#p:slprop) (#q:a -> slprop)
  (action:unit -> comp g a p q)
  : tree ops g a p q

inline_for_extraction
val bind (#tag:Type0) (#ops:signature tag) (#g #h:grade)
  (#a #b:Type0) (#p:slprop) (#q:a -> slprop) (#s:b -> slprop)
  (c:tree ops g a p q)
  ([@@@FStar.Attributes.monomorphize] next:(x:a -> tree ops h b (q x) s))
  : tree ops (join g h) b p s

// Framing changes every abortive request protocol, not just the innermost one.
// Returning requests retain the frame privately and return it to continuation.
let frame_operation (f:slprop) (op:operation) : operation =
  match op with
  | Returning _ _ _ _ -> op
  | Aborting i p -> Aborting i (fun x -> p x ** f)

let frame_signature (#tag:Type0) (f:slprop) (ops:signature tag) : signature tag =
  fun op -> frame_operation f (ops op)

inline_for_extraction
val frame (#tag:Type0) (#ops:signature tag) (#g:grade)
  (#a:Type0) (#p:slprop) (#q:a -> slprop) (f:slprop) (c:tree ops g a p q)
  : Tot (tree (frame_signature f ops) g a (p ** f) (fun x -> q x ** f))
      (decreases c)

inline_for_extraction
val perform (#tag:Type0) (#ops:signature tag) (#g:grade)
  (op:tag{Returning? (ops op)}) (arg:input (ops op))
  : tree ops g (output (ops op)) (request (ops op) arg) (reply (ops op) arg)

// Relabeling preserves complete protocols, including returning/abortive kind.
inline_for_extraction
val relabel (#tag #other:Type0) (#ops:signature tag) (#target:signature other)
  (#g:grade) (#a:Type0) (#p:slprop) (#q:a -> slprop)
  (embed:(op:tag -> l:other{target l == ops op})) (c:tree ops g a p q)
  : Tot (tree target g a p q) (decreases c)

inline_for_extraction
val consequence (#tag:Type0) (#ops:signature tag) (#g:grade) (#a:Type0)
  (#p #p':slprop) (#q #q':a -> slprop)
  (before:unit -> stt_ghost unit emp_inames p' (fun _ -> p))
  (c:tree ops g a p q)
  (after:(x:a -> stt_ghost unit emp_inames (q x) (fun _ -> q' x)))
  : tree ops g a p' q'

// Abstract requests do not determine their implementations' termination.
// The interpreter combines the tree grade with the implementation-table grade.
let implementations (#tag:Type0) (ops:signature tag) (h:grade) =
  op:tag -> arg:input (ops op) ->
    comp h (output (ops op)) (request (ops op) arg) (reply (ops op) arg)

// Grade-specialized open interpreters expose literal computation types to Pulse.
val run_terminating (#tag:Type0) (#ops:signature tag)
  (#a:Type0) (#p:slprop) (#q:a -> slprop)
  (impl:implementations ops Terminating) (c:tree ops Terminating a p q)
  : Tot (stt a p (fun x -> q x)) (decreases c)

val run_divergent (#tag:Type0) (#ops:signature tag)
  (#a:Type0) (#p:slprop) (#q:a -> slprop)
  (impl:implementations ops MayDiverge) (c:tree ops MayDiverge a p q)
  : Tot (stt_div a p (fun x -> q x)) (decreases c)

inline_for_extraction
val run (#tag:Type0) (#ops:signature tag) (#g #h:grade)
  (#a:Type0) (#p:slprop) (#q:a -> slprop)
  (impl:implementations ops h) (c:tree ops g a p q)
  : Tot (comp (join g h) a p q) (decreases c)

// Literal computation types make these closing interfaces usable from Pulse.
// An empty signature may have been transformed by framing; it need not be the
// particular empty_ops function defined above.
val run_closed (#ops:signature empty) (#a:Type0) (#p:slprop) (#q:a -> slprop)
  (c:tree ops Terminating a p q) : stt a p (fun x -> q x)

val run_closed_div (#ops:signature empty) (#g:grade)
  (#a:Type0) (#p:slprop) (#q:a -> slprop)
  (c:tree ops g a p q) : stt_div a p (fun x -> q x)
