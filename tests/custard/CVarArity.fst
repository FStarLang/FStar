module CVarArity

(* Section 26, item 1: a callee reached through an arrow-typed *global
   variable*.

   [e]'s body is a call that returns a function, so section 25.3's [cheap_expr]
   guard declines to eta-expand it and it is lowered to a variable of
   function-pointer type rather than to a function.  That lowering was
   load-bearing for correctness in a way nobody intended: both the arity table
   that drives eta-expansion and the C backend's call-arity check recorded
   *definitions*, and a variable of arrow type was neither.  So [call_e] --
   arity two in the source, shortened to [fun a -> e a] by [eta_reduce] --
   was owed nothing, stayed eta-short, and came out as [e(a)] against a
   two-parameter function pointer.

   Both tables now read a parameterless arrow-typed definition's arity off its
   type, which is what the emitted object actually accepts.

   [ap] deliberately *chooses* between its two function arguments rather than
   returning one of them outright: section 27.4's forwarder rule collapses the
   plain [fun phi -> phi] shape, and this test needs the function-pointer
   lowering to survive so that it still tests what it was written for.

   [call_e] is *also* a root, so this covers the shape that has no downstream
   over-application to catch it: with [main] deleted, nothing applied [call_e]
   to two arguments and the only symptom was the C compiler. *)

let ap (n: bool) (phi: (bool -> bool -> bool)) (psi: (bool -> bool -> bool))
  : (bool -> bool -> bool) = if n then phi else psi
let band (a: bool) (b: bool) : bool = a && b
let bor (a: bool) (b: bool) : bool = a || b

let e : bool -> bool -> bool = ap true band bor
let call_e (a: bool) (b: bool) : bool = e a b

let ck (b: bool) : FStar.UInt32.t = if b then 0ul else 1ul

let main () : FStar.UInt32.t =
  FStar.UInt32.logor (ck (call_e true true && not (call_e true false)))
                     (ck (e true true && not (e false true)))
