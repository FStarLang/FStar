open Prims
let buffer_dummy : 'uuuuu . unit -> 'uuuuu LowStar_Buffer.buffer =
  fun uu___ -> LowStar_Monotonic_Buffer.mnull ()
type nonzero = FStar_UInt32.t
type ('a, 'len, 'h, 'v) buffer_r_inv = unit
type ('a, 'len) buffer_repr = 'a FStar_Seq_Base.seq
type ('a, 'v) buffer_r_alloc_p = unit
let buffer_r_alloc :
  'a . unit -> ('a * nonzero) -> unit -> 'a LowStar_Buffer.buffer =
  fun uu___ ->
    fun uu___1 ->
      fun r ->
        match uu___1 with
        | (ia, len) -> LowStar_Monotonic_Buffer.mmalloc () ia len
let buffer_r_free :
  'a . unit -> ('a * nonzero) -> 'a LowStar_Buffer.buffer -> unit =
  fun uu___ -> fun len -> fun v -> LowStar_Monotonic_Buffer.free v
let buffer_copy :
  'a .
    unit ->
      ('a * nonzero) ->
        'a LowStar_Buffer.buffer -> 'a LowStar_Buffer.buffer -> unit
  =
  fun uu___ ->
    fun uu___1 ->
      fun src ->
        fun dst ->
          match uu___1 with
          | (ia, len) ->
              LowStar_Monotonic_Buffer.blit src Stdint.Uint32.zero dst
                Stdint.Uint32.zero len
let buffer_regional :
  'a .
    'a ->
      nonzero ->
        (('a * nonzero), 'a LowStar_Buffer.buffer) LowStar_Regional.regional
  =
  fun ia ->
    fun len ->
      LowStar_Regional.Rgl
        ((ia, len), (), (), (buffer_dummy ()), (), (), (), (), (), (), (),
          (buffer_r_alloc ()), (buffer_r_free ()))
let buffer_copyable :
  'a .
    'a ->
      nonzero ->
        (('a * nonzero), 'a LowStar_Buffer.buffer, unit)
          LowStar_RVector.copyable
  = fun ia -> fun len -> LowStar_RVector.Cpy (buffer_copy ())
let vector_dummy :
  'a 'uuuuu . unit -> ('a, 'uuuuu, unit) LowStar_RVector.rvector =
  fun uu___ ->
    LowStar_Vector.Vec
      (Stdint.Uint32.zero, Stdint.Uint32.zero,
        (LowStar_Monotonic_Buffer.mnull ()))
type ('a, 'rst, 'rg, 'h, 'v) vector_r_inv = unit
type ('a, 'rst, 'rg) vector_repr = unit FStar_Seq_Base.seq
type ('a, 'rst, 'rg, 'v) vector_r_alloc_p = unit
let vector_r_alloc :
  'a 'rst .
    ('rst, 'a) LowStar_Regional.regional ->
      unit -> ('a, 'rst, unit) LowStar_RVector.rvector
  =
  fun rg ->
    fun r ->
      FStar_HyperStack_ST.new_region ();
      LowStar_Vector.alloc_reserve Stdint.Uint32.one
        (LowStar_Regional.__proj__Rgl__item__dummy rg) ()
let vector_r_free :
  'uuuuu 'uuuuu1 .
    unit ->
      ('uuuuu1, 'uuuuu) LowStar_Regional.regional ->
        ('uuuuu, 'uuuuu1, unit) LowStar_RVector.rvector -> unit
  = fun uu___ -> fun uu___1 -> fun v -> LowStar_Vector.free v
let vector_regional :
  'a 'rst .
    ('rst, 'a) LowStar_Regional.regional ->
      (('rst, 'a) LowStar_Regional.regional,
        ('a, 'rst, unit) LowStar_RVector.rvector) LowStar_Regional.regional
  =
  fun rg ->
    LowStar_Regional.Rgl
      (rg, (), (), (vector_dummy ()), (), (), (), (), (), (), (),
        vector_r_alloc, (vector_r_free ()))