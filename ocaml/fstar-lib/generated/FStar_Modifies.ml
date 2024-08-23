open Prims
type loc_aux =
  | LocBuffer of unit * Obj.t FStar_Buffer.buffer 
let (uu___is_LocBuffer : loc_aux -> Prims.bool) = fun projectee -> true
let (__proj__LocBuffer__item__b : loc_aux -> unit FStar_Buffer.buffer) =
  fun uu___ ->
    (fun projectee -> match projectee with | LocBuffer (t, b) -> Obj.magic b)
      uu___
type ('l, 'r, 'n) loc_aux_in_addr = Obj.t
type ('r, 'n) aloc = loc_aux
type ('a, 's, 'b) loc_aux_includes_buffer = Obj.t
type ('s1, 's2) loc_aux_includes = Obj.t
type ('l, 't, 'p) loc_aux_disjoint_buffer = Obj.t
type ('l1, 'l2) loc_aux_disjoint = Obj.t
type ('l, 'h1, 'h2) loc_aux_preserved = Obj.t
type loc = unit

type ('s1, 's2) loc_includes = unit
type ('s1, 's2) loc_disjoint = unit
type ('s, 'h1, 'h2) modifies = unit


type ('h, 'ra) does_not_contain_addr = unit
type ('uuuuu, 'uuuuu1) cloc_aloc = (unit, unit) aloc
