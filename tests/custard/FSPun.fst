module FSPun

(* Section 122.6.2.  The value of type [sized UInt32.t] is stored in a field
   the layout analysis gave the type [sized any], so reading it back is a
   coercion between two instantiations of one parameterized type.  On the
   OCaml backend that is [Obj.magic] and costs nothing.  On .NET the two are
   different runtime types and the unbox raises [InvalidCastException] --- at
   run time, from a line nobody wrote --- so it is refused here instead. *)

module SZ = FStar.SizeT

class sized (t:Type0) = { sz : SZ.t; dflt : t }
instance sized_u32 : sized UInt32.t = { sz = 4sz; dflt = 0ul }

noeq type desc = | D : (ty:Type0) -> {| sized ty |} -> len:UInt32.t -> desc

noeq type box = { d : desc; n : UInt32.t }

let go (b:box) : UInt32.t = match b.d with | D _ len -> UInt32.add_mod len b.n

let main () : UInt32.t = go ({ d = D UInt32.t 1ul; n = 2ul })
