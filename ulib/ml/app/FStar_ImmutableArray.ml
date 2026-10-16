module IAB = FStar_ImmutableArray_Base
let to_list (x:'a IAB.t) = Array.to_list x
let upd (x:'a IAB.t) (i:Prims.int) (v:'a) : 'a IAB.t =
  let y = Array.copy x in
  y.(Z.to_int i) <- v;
  y
let push (x:'a IAB.t) (v:'a) : 'a IAB.t = Array.append x [| v |]
