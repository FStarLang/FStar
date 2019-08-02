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
  (**) assume(RST.rst_inv (AR.array_resource b) hinit);
  (**) let init = RST.get (R.(AR.array_resource b <*> context)) in
  (**) let correct_inv = fun (b_view, context_view) i -> loop_inv context_view i /\
  (**)  init (AR.array_resource b) == b_view
  (**) in
  (**) R.reveal_star ();
  let correct_f (i:U32.t{U32.(0 <= v i /\ v i < A.vlength b)})
    : RST.RST unit
      (R.(AR.array_resource b <*> context))
      (fun _ -> R.(AR.array_resource b <*> context))
      (requires (fun old ->
        correct_inv (old (R.(AR.array_resource b <*> context))) (U32.v i)
      ))
      (ensures (fun old _ modern -> U32.(
        correct_inv (old R.(AR.array_resource b <*> context)) (v i) /\
        correct_inv (modern R.(AR.array_resource b <*> context)) (v i + 1)
      )))
  =
    let x = RST.rst_frame
      (R.(AR.array_resource b <*> context))
      (fun _ -> R.(AR.array_resource b <*> context))
      (fun _ -> AR.index b i)
    in
    let f' () : RST.RST unit // TODO: figure out why we cannot remove this superfluous let-binding
      (context)
      (fun _ -> context)
      (fun old ->  loop_inv (old context) (U32.v i))
      (fun old _ modern -> loop_inv (old context) (U32.v i) /\ loop_inv (modern context) (U32.v i + 1))
      =
      f i x
    in
     RST.rst_frame
       R.(AR.array_resource b <*> context)
       (fun _ -> R.(AR.array_resource b <*> context))
       f'
  in
  (**) assume(R.inv (R.(AR.array_resource b <*> context)) hinit);
  (**) assume(RST.rst_inv (R.(AR.array_resource b <*> context)) hinit);
  (**) admit();
  L.for
    0ul
    len
    R.(AR.array_resource b <*> context)
    correct_inv
    correct_f
