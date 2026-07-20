open Prims
type 'k less_than = Prims.int
type 'k greater_than = Prims.int
type 'x not_less_than = Obj.t greater_than
type 'x not_greater_than = Obj.t less_than
let coerce_to_less_than (n : Prims.int) (x : Obj.t not_greater_than) :
  Obj.t less_than= x
let coerce_to_not_less_than (n : Prims.int) (x : Obj.t greater_than) :
  Obj.t not_less_than= x
let interval_condition (x : Prims.int) (y : Prims.int) (t : Prims.int) :
  Prims.bool= (x <= t) && (t < y)
type ('x, 'y) interval_type = unit
type ('x, 'y) interval = Prims.int
type ('x, 'y) efrom_eto = (Obj.t, 'y) interval
type ('x, 'y) efrom_ito = (Obj.t, Obj.t) interval
type ('x, 'y) ifrom_eto = ('x, 'y) interval
type ('x, 'y) ifrom_ito = ('x, Obj.t) interval
type 'k under = (Obj.t, 'k) interval
let interval_size (x : Prims.int) (y : Prims.int) (interval1 : unit) :
  Prims.nat= if y >= x then y - x else Prims.int_zero
type ('x, 'y, 'interval1) counter_for = Obj.t under
let closed_interval_size (x : Prims.int) (y : Prims.int) : Prims.nat=
  interval_size x (y + Prims.int_one) ()
let indices_seq (n : Prims.nat) : Obj.t under FStar_Seq_Base.seq=
  if n = Prims.int_zero
  then FStar_Seq_Base.MkSeq []
  else FStar_Seq_Base.init_aux n Prims.int_zero (fun x -> x)
