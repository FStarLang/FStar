module TopLevelIndexedEffects

/// See the definition of top_level_effect in FStar.Pervasives.fsti

//
// Defining an identity effect
//

type repr (a:Type) = a
let return (a:Type) (x:a) : repr a = x
let bind (a b:Type) (f:repr a) (g:a -> repr b) : repr b = g f

effect { M (a:Type) with {repr; return; bind}}

let lift_PURE_M (a:Type) (wp:pure_wp a) (f:unit -> PURE a wp)
  : Pure (repr a)
         (requires wp (fun _ -> True))
         (ensures fun _ -> True)
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    f ()

sub_effect PURE ~> M = lift_PURE_M

assume val f (_:unit) : M int


//
// If we try to use this effect at the top-level, F* complains
//

[@@ expect_failure]
let n : int = f ()

//
// We define an identical effect N,
//   but with a top-level effect attribute
//

[@@ top_level_effect]
effect { N (a:Type) with {repr; return; bind}}

sub_effect PURE ~> N = lift_PURE_M

//
// And now F* lets the effect go through at the top-level
//

assume val g (_:unit) : N int

let n : int = g ()
