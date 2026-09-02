module StoredType

(* Section 32.6.  A constructor that stores a [Type0] nothing else mentions.
   Rule 4b used to make any binder of this type [Mono], so [dlen] could not
   take one at runtime; but the field is erased like any other type, and what
   remains is one [UInt32.t] with a perfectly uniform representation.  The
   dependence is what makes an existential, not the storing. *)

noeq type desc = | D : (ty:Type0) -> len:UInt32.t -> desc

let dlen (d:desc) : UInt32.t = match d with | D _ len -> len

let go (d:desc) : UInt32.t = dlen d

let main () : UInt32.t = if go (D UInt32.t 7ul) = 7ul then 0ul else 1ul
