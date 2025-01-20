open Prims
type ('a, 's1, 's2) immutable_preorder =
  ('a, unit, unit) FStar_Seq_Base.equal
type 'a ibuffer =
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer
let inull : 'a . unit -> 'a ibuffer =
  fun uu___ -> LowStar_Monotonic_Buffer.mnull ()
type 'a ipointer = 'a ibuffer
type 'a ipointer_or_null = 'a ibuffer
let isub :
  'a .
    unit ->
      ('a, ('a, unit, unit) immutable_preorder,
        ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer
        ->
        FStar_UInt32.t ->
          unit ->
            ('a, ('a, unit, unit) immutable_preorder,
              ('a, unit, unit) immutable_preorder)
              LowStar_Monotonic_Buffer.mbuffer
  = fun uu___ -> LowStar_Monotonic_Buffer.msub
let ioffset :
  'a .
    unit ->
      ('a, ('a, unit, unit) immutable_preorder,
        ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer
        ->
        FStar_UInt32.t ->
          ('a, ('a, unit, unit) immutable_preorder,
            ('a, unit, unit) immutable_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  = fun uu___ -> LowStar_Monotonic_Buffer.moffset
type ('a, 's, 's1) cpred = ('a, unit, unit) FStar_Seq_Base.equal
type ('a, 's, 'su) seq_eq = ('a, unit, unit) FStar_Seq_Base.equal
type ('a, 'b, 's) value_is =
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder, unit, ('a, unit, unit) seq_eq)
    LowStar_Monotonic_Buffer.witnessed
type ('a, 'len, 's) libuffer =
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer
type ('a, 'len, 'r, 's) libuffer_or_null =
  ('a, ('a, unit, unit) immutable_preorder,
    ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer
let igcmalloc :
  'a .
    unit ->
      'a ->
        FStar_UInt32.t ->
          ('a, ('a, unit, unit) immutable_preorder,
            ('a, unit, unit) immutable_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  =
  fun r ->
    fun init ->
      fun len ->
        let b = LowStar_Monotonic_Buffer.mgcmalloc () init len in
        LowStar_Monotonic_Buffer.witness_p b (); b
let igcmalloc_and_blit :
  'a .
    unit ->
      unit ->
        unit ->
          ('a, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer ->
            FStar_UInt32.t ->
              FStar_UInt32.t ->
                ('a, ('a, unit, unit) immutable_preorder,
                  ('a, unit, unit) immutable_preorder)
                  LowStar_Monotonic_Buffer.mbuffer
  =
  fun r ->
    fun rrel1 ->
      fun rel1 ->
        fun src ->
          fun id_src ->
            fun len ->
              let b =
                LowStar_Monotonic_Buffer.mgcmalloc_and_blit () () () src
                  id_src len in
              let h0 = FStar_HyperStack_ST.get () in
              LowStar_Monotonic_Buffer.witness_p b (); b
let igcmalloc_partial :
  'a .
    unit ->
      'a ->
        FStar_UInt32.t ->
          ('a, ('a, unit, unit) immutable_preorder,
            ('a, unit, unit) immutable_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  = fun r -> fun init -> fun len -> igcmalloc () init len
let imalloc :
  'a .
    unit ->
      'a ->
        FStar_UInt32.t ->
          ('a, ('a, unit, unit) immutable_preorder,
            ('a, unit, unit) immutable_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  =
  fun r ->
    fun init ->
      fun len ->
        let b = LowStar_Monotonic_Buffer.mmalloc () init len in
        LowStar_Monotonic_Buffer.witness_p b (); b
let imalloc_and_blit :
  'a .
    unit ->
      unit ->
        unit ->
          ('a, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer ->
            FStar_UInt32.t ->
              FStar_UInt32.t ->
                ('a, ('a, unit, unit) immutable_preorder,
                  ('a, unit, unit) immutable_preorder)
                  LowStar_Monotonic_Buffer.mbuffer
  =
  fun r ->
    fun rrel1 ->
      fun rel1 ->
        fun src ->
          fun id_src ->
            fun len ->
              let b =
                LowStar_Monotonic_Buffer.mmalloc_and_blit () () () src id_src
                  len in
              let h0 = FStar_HyperStack_ST.get () in
              LowStar_Monotonic_Buffer.witness_p b (); b
let imalloc_partial :
  'a .
    unit ->
      'a ->
        FStar_UInt32.t ->
          ('a, ('a, unit, unit) immutable_preorder,
            ('a, unit, unit) immutable_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  = fun r -> fun init -> fun len -> imalloc () init len
let ialloca :
  'a .
    'a ->
      FStar_UInt32.t ->
        ('a, ('a, unit, unit) immutable_preorder,
          ('a, unit, unit) immutable_preorder)
          LowStar_Monotonic_Buffer.mbuffer
  =
  fun init ->
    fun len ->
      let b = LowStar_Monotonic_Buffer.malloca init len in
      LowStar_Monotonic_Buffer.witness_p b (); b
let ialloca_and_blit :
  'a 'rrel1 'rel1 .
    ('a, 'rrel1, 'rel1) LowStar_Monotonic_Buffer.mbuffer ->
      FStar_UInt32.t ->
        FStar_UInt32.t ->
          ('a, ('a, unit, unit) immutable_preorder,
            ('a, unit, unit) immutable_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  =
  fun src ->
    fun id_src ->
      fun len ->
        let b = LowStar_Monotonic_Buffer.malloca_and_blit src id_src len in
        let h0 = FStar_HyperStack_ST.get () in
        LowStar_Monotonic_Buffer.witness_p b (); b
let ialloca_of_list :
  'a .
    'a Prims.list ->
      ('a, ('a, unit, unit) immutable_preorder,
        ('a, unit, unit) immutable_preorder) LowStar_Monotonic_Buffer.mbuffer
  =
  fun init ->
    let b = LowStar_Monotonic_Buffer.malloca_of_list init in
    LowStar_Monotonic_Buffer.witness_p b (); b
let igcmalloc_of_list :
  'a .
    unit ->
      'a Prims.list ->
        ('a, ('a, unit, unit) immutable_preorder,
          ('a, unit, unit) immutable_preorder)
          LowStar_Monotonic_Buffer.mbuffer
  =
  fun r ->
    fun init ->
      let b = LowStar_Monotonic_Buffer.mgcmalloc_of_list () init in
      LowStar_Monotonic_Buffer.witness_p b (); b
let igcmalloc_of_list_partial :
  'a .
    unit ->
      'a Prims.list ->
        ('a, ('a, unit, unit) immutable_preorder,
          ('a, unit, unit) immutable_preorder)
          LowStar_Monotonic_Buffer.mbuffer
  = fun r -> fun init -> igcmalloc_of_list () init
let witness_contents : 'a . 'a ibuffer -> 'a FStar_Seq_Base.seq -> unit =
  fun b -> fun s -> LowStar_Monotonic_Buffer.witness_p b ()
let recall_contents : 'a . 'a ibuffer -> 'a FStar_Seq_Base.seq -> unit =
  fun b -> fun s -> LowStar_Monotonic_Buffer.recall_p b ()
let witness_value : 'a . 'a ibuffer -> unit =
  fun b ->
    let h = FStar_HyperStack_ST.get () in
    LowStar_Monotonic_Buffer.witness_p b ()
let recall_value : 'a . 'a ibuffer -> unit -> unit =
  fun b -> fun s -> LowStar_Monotonic_Buffer.recall_p b ()