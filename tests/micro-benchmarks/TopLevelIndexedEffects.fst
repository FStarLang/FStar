module TopLevelIndexedEffects

/// See the definition of top_level_effect in FStar.Pervasives.fsti

//
// Defining an identity effect
//

type repr (a:Type) = a
let return (a:Type) (x:a) : repr a = x
let bind (a b:Type) (f:repr a) (g:a -> repr b) : repr b = g f

effect { M with {repr; return; bind} }

let lift_PURE_M (a:Type) (f:unit -> a) : repr a = f ()

sub_effect Tot ~> M = lift_PURE_M

assume val f (_:unit) : M int


//
// If we try to use this effect at the top-level, F* complains
//

#push-options "--warn_error -272" //Warning_TopLevelEffect
[@@ expect_failure]
let n : int = f ()
#pop-options

//
// We define an identical effect N,
//   but with a top-level effect attribute
//

[@@ top_level_effect]
effect { N with {repr; return; bind} }

sub_effect Tot ~> N = lift_PURE_M

//
// And now F* lets the effect go through at the top-level
//

assume val g (_:unit) : N int

#push-options "--warn_error -272" //Warning_TopLevelEffect
let n : int = g ()
#pop-options