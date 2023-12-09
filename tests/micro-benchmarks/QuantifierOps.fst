module QuantifierOps

assume
val vprop:Type u#2

assume
val ( exists* ) (#a: Type) (f: (x: a -> vprop)) : vprop

assume
val ( forall* ) (#a: Type) (f: (x: a -> vprop)) : vprop

assume
val stt (#a: Type) (pre: vprop) (post: (a -> vprop)) : Type u#0

assume
val ref (a: Type u#0) : Type u#0

assume
val pts_to (#a: Type) (x: ref a) (v: a) : vprop

assume
val ( ** ) (x y: vprop) : vprop

assume
val emp:vprop

assume
val copy (x: ref int)
: stt 
  (requires exists* (v: int). pts_to x v)
  (ensures
    fun (y: ref int) ->
      exists* (v: int) (u: int).
        forall* (a: int) (b: int) (c: int). pts_to x (v + b + c) ** pts_to y (u + a))