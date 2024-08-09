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
let (cls : (unit, unit) aloc FStar_ModifiesGen.cls) =
  FStar_ModifiesGen.Cls ((), (), (), (), (), (), (), (), (), ())
type loc = ((unit, unit) aloc, unit) FStar_ModifiesGen.loc
let (loc_none : loc) = FStar_ModifiesGen.loc_none cls
type ('s1, 's2) loc_includes =
  ((unit, unit) aloc, unit, unit, unit) FStar_ModifiesGen.loc_includes
type ('s1, 's2) loc_disjoint =
  ((unit, unit) aloc, unit, unit, unit) FStar_ModifiesGen.loc_disjoint
type ('s, 'h1, 'h2) modifies =
  ((unit, unit) aloc, unit, unit, unit, unit) FStar_ModifiesGen.modifies
let (address_liveness_insensitive_locs : loc) =
  FStar_ModifiesGen.address_liveness_insensitive_locs cls
let (region_liveness_insensitive_locs : loc) =
  FStar_ModifiesGen.region_liveness_insensitive_locs cls
type ('h, 'ra) does_not_contain_addr =
  (unit, unit) FStar_ModifiesGen.does_not_contain_addr
type ('uuuuu, 'uuuuu1) cloc_aloc = (unit, unit) aloc
let (cloc_cls : (unit, unit) cloc_aloc FStar_ModifiesGen.cls) = cls
let (cloc_of_loc :
  loc -> ((unit, unit) cloc_aloc, unit) FStar_ModifiesGen.loc) = fun l -> l
let (loc_of_cloc :
  ((unit, unit) cloc_aloc, unit) FStar_ModifiesGen.loc -> loc) = fun l -> l