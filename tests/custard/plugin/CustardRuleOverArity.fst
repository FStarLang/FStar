module CustardRuleOverArity

(* Issue 4565.  A rule whose declared arity is too large.

   [store] retains two arguments -- its [squash] binder is erased, exactly as
   the binders a Pulse [requires] clause introduces are -- and
   CustardRulePlugin registers a rule for it at arity 3.  No use site can
   supply a third argument, so applying the rule would eta-expand every call
   into a lambda that nothing applies, and the simplifier would delete it as
   a dead pure binding: the store would vanish from the output with exit
   code 0.  Its codomain is [ML unit], which cannot be a function, so this is
   error 396 rather than a warning. *)

module U32 = FStar.UInt32

assume val store (dst:U32.t) (v:U32.t) (#_ : squash (U32.v v < 256))
  : FStar.All.ML unit

let main () : FStar.All.ML U32.t = store 0ul 7ul; 0ul
