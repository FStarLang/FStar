open Prims
type top = (unit, Obj.t) Prims.dtuple2
type ('a, 'r, 't0, 't1) lift_binrel = (unit, 'r) Prims.dtuple2
let lower_binrel :
  'a 'r . top -> top -> ('a, 'r, unit, unit) lift_binrel -> 'r =
  fun x -> fun y -> fun p -> FStar_Pervasives.dsnd p

type ('a, 'r, 'wfur, 'uuuuu, 'uuuuu1) lift_binrel_as_well_founded_relation =
  ('a, 'r, unit, unit) lift_binrel
type ('a, 'r, 't0, 't1) lift_binrel_squashed = unit
type ('a, 'r, 'x, 'y) squash_binrel = unit

type ('a, 'r, 'wfur, 'uuuuu,
  'uuuuu1) lift_binrel_squashed_as_well_founded_relation = unit
