open Prims
type 'a binrel = unit
type ('a, 'r) well_founded = unit
let rec fix_F :
  'aa .
    unit ->
      unit ->
        ('aa -> ('aa -> unit -> Obj.t) -> Obj.t) -> 'aa -> unit -> Obj.t
  = fun r p f x a -> f x (fun y h -> fix_F () () f y ())
let fix (r : unit) (rwf : unit) (p : unit)
  (f : 'aa -> ('aa -> unit -> Obj.t) -> Obj.t) (x : 'aa) : Obj.t=
  fix_F () () f x ()
type 'a well_founded_relation = unit



