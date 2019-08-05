module LowStar.RST.Array.Loops


module R = LowStar.Resource
module RST = LowStar.RST
module A = LowStar.Array
module AR = LowStar.RST.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module P = LowStar.Permissions
module U32 = FStar.UInt32
module L = LowStar.RST.Loops

open FStar.Mul

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

let iteri #a b context loop_inv f len =
  (**) let hinit = HST.get () in
  (**) R.reveal_star ();
  (**) RST.reveal_rst_inv ();
  (**) let init = RST.get (R.(AR.array_resource b <*> context)) in
  (**) let correct_inv (sel : RST.selector ((R.(AR.array_resource b <*> context)))) (i : nat) =
  (**)  loop_inv (RST.focus_selector sel context) i /\
  (**)  init (AR.array_resource b) == (sel (AR.array_resource b))
  (**) in
  let correct_f (i:U32.t{U32.(0 <= v i /\ v i < A.vlength b)})
    : RST.RST unit
      (R.(AR.array_resource b <*> context))
      (fun _ -> R.(AR.array_resource b <*> context))
      (requires (fun old ->
        correct_inv old (U32.v i)
      ))
      (ensures (fun old _ modern -> U32.(
        correct_inv old (v i) /\
        correct_inv modern (v i + 1)
      )))
  =
    let old = RST.get (R.(AR.array_resource b <*> context)) in
    assume(loop_inv (RST.focus_selector old context) (U32.v i));
    assume(init (AR.array_resource b) == (old (AR.array_resource b)));
    assert(correct_inv old (U32.v i));
    admit();
    let h0 = HST.get () in
    let x = RST.rst_frame
      (R.(AR.array_resource b <*> context))
      (fun _ -> R.(AR.array_resource b <*> context))
      (fun _ -> AR.index b i)
    in
    let f' () : RST.RST unit // TODO: figure out why we cannot remove this superfluous let-binding
      (context)
      (fun _ -> context)
      (fun old -> loop_inv old (U32.v i))
      (fun old _ modern -> loop_inv old (U32.v i) /\ loop_inv modern (U32.v i + 1))
      =
      f i x
    in
    RST.rst_frame
      R.(AR.array_resource b <*> context)
      (fun _ -> R.(AR.array_resource b <*> context))
      f'
  in
  (**) admit();
  L.for
    0ul
    len
    R.(AR.array_resource b <*> context)
    correct_inv
    correct_f
