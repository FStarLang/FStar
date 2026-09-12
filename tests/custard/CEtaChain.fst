module CEtaChain

(* Section 25: a definition that is parameterless *in the source* but whose
   type is an arrow, and the callers that apply it.

   [g] is [let g : bool -> bool -> bool = f] -- zero binders in the source,
   arity two in its type.  The backend eta-expands such a definition into a
   real two-argument C function, and that half always worked.  What did not is
   the *callers*: [eta_expand_decls] read every arity from the program as it
   found it, so it saw [g] with zero binders, concluded that [call_g] was owed
   nothing, and left it a partial application.  C then reported "too few
   arguments to function Wrap_g" -- against a prototype the same run had
   emitted.

   [call_g] is the sharp case, because it is not a partial application in the
   source at all: [eta_reduce] shortens [fun a b -> g a b] to [fun a -> g a],
   and nothing put the argument back.  So [call_g] and [call_g_partial] used
   to produce byte-identical C despite one being a full application and the
   other a partial one -- an argument went missing on the way, and the IR was
   wrong before the backend saw it.

   The expansion is now run to a fixpoint, which is what makes the chain
   [f] -> [g] -> [call_g] resolve: each round learns the arity the previous
   round established.  [call_f] is the control -- the same shape through a
   callee that has its binders in the source -- and it was always correct. *)

let f (x: bool) (y: bool) : bool = x && y   (* arity 2 in the source *)
let g : bool -> bool -> bool = f            (* arity 0 in the source *)

let call_f (a: bool) (b: bool) : bool = f a b
let call_g (a: bool) (b: bool) : bool = g a b
let call_g_partial (a: bool) : (bool -> bool) = g a

(* One more link, so that a single round of expansion cannot pass the test:
   [h] is owed its arity by [call_g], which is itself only expanded once [g]
   has been. *)
let h : bool -> bool -> bool = call_g

let ck (b: bool) : FStar.UInt32.t = if b then 0ul else 1ul

let main () : FStar.UInt32.t =
  FStar.UInt32.logor (ck (f true true && not (f true false)))
   (FStar.UInt32.logor (ck (call_f true true && not (call_f true false)))
    (FStar.UInt32.logor (ck (call_g true true && not (call_g true false)))
     (FStar.UInt32.logor (ck (call_g_partial true true))
                         (ck (h true true && not (h false true))))))
