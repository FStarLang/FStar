module EffectDeclChecks

(* An effect with no representation is an assumption, so it must be
   marked [assume]. *)
[@@expect_failure [162]]
effect FOO1

assume effect FOO2

(* Likewise, a sub-effect with no lift is an assumption. *)
[@@expect_failure [162]]
sub_effect Tot ~> FOO2

let id_repr (a:Type) : Type = a
let id_return (a:Type) (x:a) : id_repr a = x
let id_bind (a b:Type) (f:id_repr a) (g:a -> id_repr b) : id_repr b = g f

(* Conversely, the combinators of an effect definition are checked, so
   the definition cannot be marked [assume]. *)
[@@expect_failure [162]]
assume effect { FOO3 with { repr = id_repr; return = id_return; bind = id_bind } }

reifiable effect { FOO4 with { repr = id_repr; return = id_return; bind = id_bind } }

let lift_pure_foo4 (a:Type) (f:unit -> PURE a (requires True) (ensures fun _ -> True))
  : id_repr a
  = f ()

(* And the lift of a sub-effect is checked, so it cannot be marked [assume]. *)
[@@expect_failure [162]]
assume sub_effect Tot ~> FOO4 = lift_pure_foo4

(* FOO4 has a representation, so a lift from FOO2 into it cannot be
   synthesized out of FOO4's return combinator. *)
[@@expect_failure [187]]
assume sub_effect FOO2 ~> FOO4

let div_repr (a:Type) : Type = unit -> Dv a
let div_return (a:Type) (x:a) : div_repr a = fun () -> x
let div_bind (a b:Type) (f:div_repr a) (g:a -> div_repr b) : div_repr b = fun () -> g (f ()) ()

(* The representation is a divergent function, so the effect is not total. *)
[@@expect_failure [187]]
total
effect { FOO5 with { repr = div_repr; return = div_return; bind = div_bind } }
