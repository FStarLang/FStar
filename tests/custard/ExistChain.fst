module ExistChain

(* Section 33.4.  The same existential as [ExistAdvice], but reached from a
   field of runtime data rather than from a monomorphized binder.  Rule 4b
   rejects it either way; only the 364 path could say why, because only it
   still has the source type in hand.  By the time the backend meets the
   field, the [Type0] is erased and what is left is a [TAny] whose cause is
   invisible -- so the advice was "that is a Custard bug, please report it",
   about a type that is correctly rejected.

   The chain is what makes it findable: the type that lost its representation
   is [sized], and the existential is [desc], which the chain already names. *)

module SZ = FStar.SizeT

class sized (t:Type0) = { sz : SZ.t; dflt : t }
instance sized_u32 : sized UInt32.t = { sz = 4sz; dflt = 0ul }

noeq type desc =
  | D : (ty:Type0) -> {| sized ty |} -> len:UInt32.t -> desc

noeq type box = { d : desc; n : UInt32.t }

let go (b : box) : UInt32.t = b.n

let main () : UInt32.t = go ({ d = D UInt32.t 1ul; n = 2ul })
