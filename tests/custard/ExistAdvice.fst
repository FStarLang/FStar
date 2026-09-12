module ExistAdvice

(* Section 32.6.  Rule 4b classified binder 0 of [dlen] as [Mono] and error
   364 then advised writing an annotation -- or dropping one that was never
   written.  Neither is available: the type is an existential, and that is a
   property of the type rather than of any call site. *)

module SZ = FStar.SizeT

class sized (t:Type0) = { sz : SZ.t; dflt : t }
instance sized_u32 : sized UInt32.t = { sz = 4sz; dflt = 0ul }

noeq type desc =
  | D : (ty:Type0) -> {| sized ty |} -> len:UInt32.t -> desc

let dlen (d:desc) : UInt32.t = match d with | D _ len -> len

let go (d:desc) : UInt32.t = dlen d

let main () : UInt32.t = go (D UInt32.t 1ul)
