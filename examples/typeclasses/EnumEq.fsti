module EnumEq

open Enum
open Eq
open FStar.Tactics.Typeclasses

[@tcinstance]
val enum_eq : (#a:Type) -> (d : enum a) -> deq a
