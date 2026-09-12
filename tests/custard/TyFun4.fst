module TyFun4
module U32 = FStar.UInt32
module I32 = FStar.Int32

(* Section 57.2.  Section 56 taught [ty_of_typ] to reduce a type-level
   function applied to values, and the comment there promised that a
   reduction too expensive to finish degrades gracefully: the request
   yields [any], --custard_warn_any reports it, and the backend refuses the
   [any] with error 368.

   That promise was not kept, because a *second* normalization wrapper ran
   over the same term first and had the opposite failure policy.
   [Mono.is_arity] asks of every binder of every definition extraction
   visits whether its sort is an arity, and it asked through
   [Mono.norm_bounded], which raises error 365 on exhaustion.  So the
   binder below was fatal before [ty_of_typ] was ever consulted.

   [loop] is the shape that makes the two policies distinguishable: it does
   not terminate, but unlike [TypeDiverge] it has a *head* -- one step gives
   [tuple2 U32.t (loop 0)] -- so the arity question is answerable cheaply
   and only the full reduction runs away.  The fix is that the arity
   question is a head question and is now asked in head normal form; this
   test is the claim that the graceful path is reachable.

   [f] is named as an entry point rather than called, for the reason
   [TypeDiverge] gives: constructing a [loop 0] would diverge in the front
   end instead. *)

#push-options "--admit_smt_queries true"
let rec loop (n : nat) : Type0 = U32.t & loop n
#pop-options

let f (c : loop 0) : I32.t = 0l

let main () : FStar.All.ML unit = FStar.IO.print_string "unreached\n"
