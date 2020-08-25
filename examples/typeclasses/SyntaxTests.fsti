module SyntaxTests

open Add
open FStar.Tactics.Typeclasses

val foo (#a:Type) (#[tcresolve ()] _ : additive a) (x y : a) : Tot a

let test = {| additive int |} -> int

val foo2 : (#a:Type) -> {| additive a |} -> (x:a) -> (y:a) -> Tot a

val foo3 : (#a:Type) -> {| _ : additive a |} -> (x:a) -> (y:a) -> Tot a

val foo4 (#a:Type) {| _ : additive a |} (x: a) (y : a) : Tot a

val foo5 (#a:Type) {| additive a |} (x: a) (y : a) : Tot a
