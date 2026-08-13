module DivergentWhileGuard
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
#lang-pulse

(* Regression test for a bug found while investigating effectful/divergent
   loop guards in Pulse.

   `cont` below is a trivially-terminating function, but it is marked
   `divergent` -- exactly as PAL (FStar's C-to-Pulse translator) marks every
   function it emits by default, since it never proves termination unless
   asked to. Calling `cont` therefore has effect `stt_div` rather than `stt`.

   Using such a function as the guard of a `while` loop used to be rejected,
   even though the loop itself has no `decreases` clause and is otherwise
   treated as divergent throughout its body. This was because
   `Pulse.Checker.While.fst`'s `check_while` computes a `div` flag (true
   whenever the loop has no `decreases` measure) and threaded it through the
   loop *body* and *break*-label checks, but not through the initial
   *condition* check -- so the guard's real `stt_div` effect collided with
   an implicitly-fixed non-divergent (`stt`) expectation when composing the
   condition check, in `Pulse.Typing.Combinators.fst`'s `mk_bind`, failing
   with Error 228 ("Cannot compose computations in this divergent block:
   stt_div vs stt"). Fixed by making the condition check's post hint
   `div`-aware (and by making `comp_while_cond` take a `div` flag to match),
   mirroring how `comp_while_body`/`comp_while` already do. *)

divergent fn cont (i n : nat)
requires emp
returns b:bool
ensures pure (b == (i < n))
{
    (i < n)
}

divergent fn count_while_call_guard (n:nat)
returns z:nat
ensures pure (z <= n)
{
    let mut i : nat = 0;
    while (cont (!i) n)
    invariant exists* c. R.pts_to i c ** pure (c <= n)
    {
        let c = !i;
        i := c + 1;
    };
    !i
}
