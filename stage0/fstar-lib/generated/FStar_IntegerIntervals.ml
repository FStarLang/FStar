open Prims
type 'k less_than = Prims.int
type 'k greater_than = Prims.int
type 'x not_less_than = unit greater_than
type 'x not_greater_than = unit less_than
let (coerce_to_less_than :
  Prims.int -> unit not_greater_than -> unit less_than) = fun n -> fun x -> x
let (coerce_to_not_less_than :
  Prims.int -> unit greater_than -> unit not_less_than) = fun n -> fun x -> x
let (interval_condition : Prims.int -> Prims.int -> Prims.int -> Prims.bool)
  = fun x -> fun y -> fun t -> (x <= t) && (t < y)
type ('x, 'y) interval_type = unit
type ('x, 'y) interval = Prims.int
type ('x, 'y) efrom_eto = (unit, unit) interval
type ('x, 'y) efrom_ito = (unit, unit) interval
type ('x, 'y) ifrom_eto = (unit, unit) interval
type ('x, 'y) ifrom_ito = (unit, unit) interval
type 'k under = (unit, unit) interval
let (interval_size : Prims.int -> Prims.int -> unit -> Prims.nat) =
  fun x -> fun y -> fun interval1 -> if y >= x then y - x else Prims.int_zero
type ('x, 'y, 'interval1) counter_for = unit under
let (closed_interval_size : Prims.int -> Prims.int -> Prims.nat) =
  fun x -> fun y -> interval_size x (y + Prims.int_one) ()
let (indices_seq : Prims.nat -> unit under FStar_Seq_Base.seq) =
  fun n -> FStar_Seq_Base.init n (fun x -> x)