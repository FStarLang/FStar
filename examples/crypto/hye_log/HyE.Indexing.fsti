module HyE.Indexing

abstract type id = UInt32.t
abstract type pke_id = UInt32.t

val honest: id -> Tot bool
val pke_honest: pke_id -> Tot bool

assume Index_hasEq: hasEq id
