open Prims
let op_Array_Access :
  'a 'rrel 'rel .
    unit ->
      ('a, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer ->
        FStar_UInt32.t -> 'a
  = fun uu___ -> LowStar_Monotonic_Buffer.index
let op_Array_Assignment :
  'a 'rrel 'rel .
    ('a, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer ->
      FStar_UInt32.t -> 'a -> unit
  =
  fun b ->
    fun i ->
      fun v ->
        let h = FStar_HyperStack_ST.get () in
        LowStar_Monotonic_Buffer.upd' b i v
let op_Bang_Star :
  'a 'rrel 'rel . ('a, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer -> 'a =
  fun p -> LowStar_Monotonic_Buffer.index p Stdint.Uint32.zero
let op_Star_Equals :
  'a 'rrel 'rel .
    ('a, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer -> 'a -> unit
  =
  fun p ->
    fun v ->
      let h = FStar_HyperStack_ST.get () in
      LowStar_Monotonic_Buffer.upd' p Stdint.Uint32.zero v
let blit :
  'a 'rrel1 'rel1 'rrel2 'rel2 .
    unit ->
      ('a, 'rrel1, 'rrel2) LowStar_Monotonic_Buffer.mbuffer ->
        FStar_UInt32.t ->
          ('a, 'rel1, 'rel2) LowStar_Monotonic_Buffer.mbuffer ->
            FStar_UInt32.t -> FStar_UInt32.t -> unit
  = fun uu___ -> LowStar_Monotonic_Buffer.blit