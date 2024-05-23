module FStar.Class.Setlike

open FStar.Compiler.Effect
open FStar.Class.Ord

[@@Tactics.Typeclasses.fundeps [0]]
class setlike (e:Type) (s:Type) = {
  empty         : unit -> s;
  singleton     : e -> s;
  is_empty      : s -> bool;
  add           : e -> s -> s;
  remove        : e -> s -> s;
  mem           : e -> s -> bool;
  equal         : s -> s -> bool;
  subset        : s -> s -> bool;
  union         : s -> s -> s;
  inter         : s -> s -> s;
  diff          : s -> s -> s;
  for_all       : (e -> bool) -> s -> bool;
  for_any       : (e -> bool) -> s -> bool;
  elems         : s -> list e;

  collect       : (e -> s) -> list e -> s;
  from_list     : list e -> s;
  addn          : list e -> s -> s;
}

val symdiff (#e #s : Type) {| setlike e s |} : s -> s -> s
