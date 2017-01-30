module HyE.Indexing

abstract type id = UInt32.t

val honest: id -> Tot bool

assume Index_hasEq: hasEq id
