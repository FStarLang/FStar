module WideChain

(* Section 32.1.  A chain entry is a specialization *key*, and a key is a
   term, so it is as big as the term is.  Round 37 saw one error block of
   6,426,280 bytes, of which 6,425,658 were a single "Reached through" line:
   section 30.17's fallback had keyed on an unreduced value and the chain
   printed it whole.

   [b6] here is the same shape as section 30.17's [LetShare] -- each link
   uses each field of its predecessor twice, so the normal form doubles per
   link -- and [use] both keys on it and is a caller of a definition that
   fails.  Its key is over sixteen thousand characters; the diagnostic must
   not be. *)

module U32 = FStar.UInt32

noeq type bnd = { p: U32.t -> U32.t; q: U32.t -> U32.t; r: U32.t -> U32.t }
let ext (b: bnd) : bnd =
  let { p = p; q = q; r = r } = b in
  { p = (fun x -> U32.add_mod (p x) (q x));
    q = (fun x -> U32.add_mod (q x) (r x));
    r = (fun x -> U32.add_mod (r x) (p x)) }
let b0 : bnd = { p = (fun x -> x); q = (fun x -> x); r = (fun x -> x) }
let b1 = ext b0
let b2 = ext b1
let b3 = ext b2
let b4 = ext b3
let b5 = ext b4
let b6 = ext b5

(* A [Mono] binder whose argument is a big value, and a body that then asks
   for something the C backend cannot represent: the chain has to carry the
   key of the outer specialization. *)
let inner ([@@@FStar.Attributes.monomorphize] m: U32.t) : U32.t = m

let use ([@@@FStar.Attributes.monomorphize] b: bnd) (n: U32.t) : U32.t = U32.add_mod (inner n) (b.p n)
let main () : U32.t = use b6 0ul
