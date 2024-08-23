open Prims
type aloc_t = unit
type ('al, 'c) aloc =
  | ALoc of unit * Prims.nat * 'al FStar_Pervasives_Native.option 
let uu___is_ALoc : 'al . unit -> ('al, unit) aloc -> Prims.bool =
  fun c -> fun projectee -> true

let __proj__ALoc__item__addr : 'al . unit -> ('al, unit) aloc -> Prims.nat =
  fun c ->
    fun projectee -> match projectee with | ALoc (region, addr, loc) -> addr
let __proj__ALoc__item__loc :
  'al . unit -> ('al, unit) aloc -> 'al FStar_Pervasives_Native.option =
  fun c ->
    fun projectee -> match projectee with | ALoc (region, addr, loc) -> loc
type ('a, 'b) i_restricted_g_t = unit
type 'regions addrs_dom = unit
type ('regions, 'regionulivenessutags, 'r) non_live_addrs_codom = unit
type ('regions, 'regionulivenessutags, 'nonuliveuaddrs,
  'r) live_addrs_codom = unit
type ('aloc1, 'c) loc = unit


type ('t, 'tu, 'p, 'f1, 'f2) fun_set_equal = unit
type ('al, 'c, 's1, 's2) loc_equal = Obj.t
type ('al, 'c, 'b0, 'b) aloc_includes = unit
type ('al, 'c, 's, 'b) loc_aux_includes_buffer = unit
type ('al, 'c, 's1, 's2) loc_aux_includes = unit
type ('al, 'c, 's1, 's2) loc_includes' = unit
type ('al, 'c, 's1, 's2) loc_includes = unit
type ('al, 'c, 'b1, 'b2) aloc_disjoint = Obj.t
type ('al, 'c, 'l1, 'l2) loc_aux_disjoint = unit
type ('al, 'c, 'l1, 'l2) loc_disjoint_region_liveness_tags = unit
type ('al, 'c, 'l1, 'l2) loc_disjoint_addrs = unit
type ('al, 'c, 'l1, 'l2) loc_disjoint_aux = unit
type ('al, 'c, 'l1, 'l2) loc_disjoint = unit
type ('al, 'c, 's, 'h1, 'h2) modifies_preserves_livenesses = unit
type ('al, 'c, 's, 'h1, 'h2) modifies_preserves_mreferences = unit
type ('al, 'c, 's, 'h1, 'h2) modifies_preserves_alocs = unit
type ('al, 'c, 's, 'h1, 'h2) modifies_preserves_regions = unit
type ('al, 'c, 's, 'h1, 'h2) modifies_preserves_not_unused_in = unit
type ('al, 'c, 's, 'h1, 'h2) modifies = unit
type ('h, 'ra) does_not_contain_addr = unit
type ('al, 'r, 'n) cls_union_aloc =
  | ALOC_FALSE of 'al 
  | ALOC_TRUE of 'al 
let uu___is_ALOC_FALSE :
  'al . unit -> Prims.nat -> ('al, unit, unit) cls_union_aloc -> Prims.bool =
  fun r ->
    fun n ->
      fun projectee ->
        match projectee with | ALOC_FALSE _0 -> true | uu___ -> false
let __proj__ALOC_FALSE__item___0 :
  'al . unit -> Prims.nat -> ('al, unit, unit) cls_union_aloc -> 'al =
  fun r ->
    fun n -> fun projectee -> match projectee with | ALOC_FALSE _0 -> _0
let uu___is_ALOC_TRUE :
  'al . unit -> Prims.nat -> ('al, unit, unit) cls_union_aloc -> Prims.bool =
  fun r ->
    fun n ->
      fun projectee ->
        match projectee with | ALOC_TRUE _0 -> true | uu___ -> false
let __proj__ALOC_TRUE__item___0 :
  'al . unit -> Prims.nat -> ('al, unit, unit) cls_union_aloc -> 'al =
  fun r ->
    fun n -> fun projectee -> match projectee with | ALOC_TRUE _0 -> _0
let bool_of_cls_union_aloc :
  'al . unit -> Prims.nat -> ('al, unit, unit) cls_union_aloc -> Prims.bool =
  fun r ->
    fun n ->
      fun l ->
        match l with | ALOC_FALSE uu___ -> false | ALOC_TRUE uu___ -> true
let aloc_of_cls_union_aloc :
  'al . unit -> Prims.nat -> ('al, unit, unit) cls_union_aloc -> 'al =
  fun r ->
    fun n -> fun l -> match l with | ALOC_FALSE x -> x | ALOC_TRUE x -> x
let make_cls_union_aloc :
  'al .
    Prims.bool ->
      unit -> Prims.nat -> 'al -> ('al, unit, unit) cls_union_aloc
  =
  fun b -> fun r -> fun n -> fun l -> if b then ALOC_TRUE l else ALOC_FALSE l
type ('al, 'c, 'r, 'a, 'larger, 'smaller) cls_union_aloc_includes = unit
type ('al, 'c, 'r, 'a, 'larger, 'smaller) cls_union_aloc_disjoint = unit
type ('al, 'c, 'r, 'a, 'x, 'h, 'hu) cls_union_aloc_preserved = Obj.t
type ('uuuuu, 'uuuuu1, 'uuuuu2) aloc_union =
  ('uuuuu, unit, unit) cls_union_aloc


type ('al, 'r, 'n) raise_aloc = 'al FStar_Universe.raise_t
let downgrade_aloc :
  'al . unit -> (('al, unit, unit) raise_aloc, unit) aloc -> ('al, unit) aloc
  =
  fun c ->
    fun a ->
      let uu___ = a in
      match uu___ with
      | ALoc (region, addr, x) ->
          ALoc
            ((), addr,
              (if FStar_Pervasives_Native.uu___is_None x
               then FStar_Pervasives_Native.None
               else
                 FStar_Pervasives_Native.Some
                   (FStar_Universe.downgrade_val
                      (FStar_Pervasives_Native.__proj__Some__item__v x))))
let upgrade_aloc :
  'al . unit -> ('al, unit) aloc -> (('al, unit, unit) raise_aloc, unit) aloc
  =
  fun c ->
    fun a ->
      let uu___ = a in
      match uu___ with
      | ALoc (region, addr, x) ->
          ALoc
            ((), addr,
              (if FStar_Pervasives_Native.uu___is_None x
               then FStar_Pervasives_Native.None
               else
                 FStar_Pervasives_Native.Some
                   (FStar_Universe.raise_val
                      (FStar_Pervasives_Native.__proj__Some__item__v x))))