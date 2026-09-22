module TypeDiverge

(* PR #4494: cross-module inlining made `FStar.Pervasives.false_elim`
   delta-unfoldable in every client, and the legacy backends normalize *types*
   with delta, so a type computed by it -- [t] below -- unfolds

       false_elim () -> false_elim () -> ...

   without bound.  That is a divergence and not a slowdown: the process
   allocates until it is OOM-killed ("Fatal error: allocation failure during
   minor GC"), with no message naming anything.

   Section 3.6's budget is the "possible broader fix" that report asks for,
   and this test is the claim that Custard already has it.  The same shape
   reaches error 365 -- naming the term ([t sq]) and the chain that requested
   it -- in a fraction of a second.

   [my_false_elim] is spelled out rather than imported so that the test says
   what it means even if `FStar.Pervasives.false_elim` is later marked
   `irreducible`; the hazard is the *shape*, and any recursive definition
   whose unfolding makes no progress has it.

   [f] is reached by naming it as an entry point rather than by calling it,
   because a call would have to supply a [t sq] and typechecking *that* is a
   second divergence, in the front end rather than in extraction.  Naming it
   is also the honest reproduction: extraction is demand-driven from an entry
   point (section 3.2), which is a second and independent reason Custard is
   hard to hit here -- a definition nothing calls is never normalized at all
   -- so the test has to ask for [f] explicitly to test anything. *)

let rec my_false_elim (#a: Type) (_: squash False) : Tot a = my_false_elim ()

let t (sq: squash False) : Type0 = my_false_elim ()

let f (sq: squash False) (x: t sq) : nat = 0

let main () : FStar.All.ML unit = FStar.IO.print_string "unreached\n"
