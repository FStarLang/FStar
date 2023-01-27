open Prims
type ('a, 'uuuuu, 'uuuuu1) trivial_preorder = unit
type 'a buffer = ('a, unit, unit) LowStar_Monotonic_Buffer.mbuffer
let null : 'a . unit -> 'a buffer =
  fun uu___ -> LowStar_Monotonic_Buffer.mnull ()
type 'a pointer = 'a buffer
type 'a pointer_or_null = 'a buffer
let sub :
  'a .
    unit ->
      ('a, ('a, unit, unit) trivial_preorder,
        ('a, unit, unit) trivial_preorder) LowStar_Monotonic_Buffer.mbuffer
        ->
        FStar_UInt32.t ->
          unit ->
            ('a, ('a, unit, unit) trivial_preorder,
              ('a, unit, unit) trivial_preorder)
              LowStar_Monotonic_Buffer.mbuffer
  = fun uu___ -> LowStar_Monotonic_Buffer.msub
let offset :
  'a .
    unit ->
      ('a, ('a, unit, unit) trivial_preorder,
        ('a, unit, unit) trivial_preorder) LowStar_Monotonic_Buffer.mbuffer
        ->
        FStar_UInt32.t ->
          ('a, ('a, unit, unit) trivial_preorder,
            ('a, unit, unit) trivial_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  = fun uu___ -> LowStar_Monotonic_Buffer.moffset
type ('a, 'len) lbuffer = ('a, unit, unit) LowStar_Monotonic_Buffer.mbuffer
let gcmalloc :
  'a .
    unit ->
      unit ->
        'a ->
          FStar_UInt32.t ->
            ('a, ('a, unit, unit) trivial_preorder,
              ('a, unit, unit) trivial_preorder)
              LowStar_Monotonic_Buffer.mbuffer
  = fun uu___ -> LowStar_Monotonic_Buffer.mgcmalloc
let malloc :
  'a .
    unit ->
      unit ->
        'a ->
          FStar_UInt32.t ->
            ('a, ('a, unit, unit) trivial_preorder,
              ('a, unit, unit) trivial_preorder)
              LowStar_Monotonic_Buffer.mbuffer
  = fun uu___ -> LowStar_Monotonic_Buffer.mmalloc
let alloca :
  'a .
    unit ->
      'a ->
        FStar_UInt32.t ->
          ('a, ('a, unit, unit) trivial_preorder,
            ('a, unit, unit) trivial_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  = fun uu___ -> LowStar_Monotonic_Buffer.malloca
let alloca_of_list :
  'a .
    unit ->
      'a Prims.list ->
        ('a, ('a, unit, unit) trivial_preorder,
          ('a, unit, unit) trivial_preorder) LowStar_Monotonic_Buffer.mbuffer
  = fun uu___ -> LowStar_Monotonic_Buffer.malloca_of_list
let gcmalloc_of_list :
  'a .
    unit ->
      unit ->
        'a Prims.list ->
          ('a, ('a, unit, unit) trivial_preorder,
            ('a, unit, unit) trivial_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  = fun uu___ -> LowStar_Monotonic_Buffer.mgcmalloc_of_list
type ('a, 'l) assign_list_t = 'a buffer -> unit
let rec assign_list : 'a . 'a Prims.list -> 'a buffer -> unit =
  fun l ->
    fun b ->
      match l with
      | [] -> let h = FStar_HyperStack_ST.get () in ()
      | hd::tl ->
          let b_hd = LowStar_Monotonic_Buffer.msub b Stdint.Uint32.zero () in
          let b_tl = LowStar_Monotonic_Buffer.moffset b Stdint.Uint32.one in
          let h = FStar_HyperStack_ST.get () in
          ((let h1 = FStar_HyperStack_ST.get () in
            LowStar_Monotonic_Buffer.upd' b_hd Stdint.Uint32.zero hd);
           (let h0 = FStar_HyperStack_ST.get () in
            assign_list tl b_tl; (let h1 = FStar_HyperStack_ST.get () in ())))