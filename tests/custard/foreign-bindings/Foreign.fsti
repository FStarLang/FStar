module Foreign
open FStar.Attributes
module U32 = FStar.UInt32

val hook (_proof:unit) (x:U32.t) : U32.t
val value : U32.t
val identity (#a:Type0) (x:a) : a
val other (x:U32.t) : U32.t
