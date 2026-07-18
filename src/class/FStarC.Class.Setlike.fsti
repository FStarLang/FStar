module FStarC.Class.Setlike

open FStarC.Effect
open FStarC.Class.Ord

[@@Tactics.Typeclasses.fundeps [0]]
class setlike (e:Type) (s:Type) = {
  empty         : unit -> ML s;
  singleton     : e -> ML s;
  is_empty      : s -> ML bool;
  add           : e -> s -> ML s;
  remove        : e -> s -> ML s;
  mem           : e -> s -> ML bool;
  equal         : s -> s -> ML bool;
  subset        : s -> s -> ML bool;
  union         : s -> s -> ML s;
  inter         : s -> s -> ML s;
  diff          : s -> s -> ML s;
  for_all       : (e -> ML bool) -> s -> ML bool;
  for_any       : (e -> ML bool) -> s -> ML bool;
  elems         : s -> ML (list e);
  filter        : (e -> ML bool) -> s -> ML s;

  collect       : (e -> ML s) -> list e -> ML s;
  from_list     : list e -> ML s;
  addn          : list e -> s -> ML s;
}

val symdiff (#e #s : Type) {| setlike e s |} : s -> s -> ML s
