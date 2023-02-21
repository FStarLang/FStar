open Prims
type ('q, 'a) qbuf_cases = Obj.t
type ('q, 'a) q_preorder = Obj.t
type 'a qbuf = (unit, Obj.t) Prims.dtuple2
type ('a, 'c, 'uuuuu, 'uuuuu1) qbuf_pre = Obj.t
let qbuf_mbuf :
  'a . 'a qbuf -> ('a, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer =
  fun uu___ -> (fun c -> Obj.magic (FStar_Pervasives.dsnd c)) uu___
type 'a const_buffer = 'a qbuf
let as_qbuf : 'a . 'a const_buffer -> 'a qbuf = fun c -> c
type ('a, 'h, 'c) live =
  ('a, Obj.t, Obj.t, unit, unit) LowStar_Monotonic_Buffer.live
let of_buffer : 'a . 'a LowStar_Buffer.buffer -> 'a const_buffer =
  fun b -> Prims.Mkdtuple2 ((), (Obj.magic b))
let of_ibuffer : 'a . 'a LowStar_ImmutableBuffer.ibuffer -> 'a const_buffer =
  fun b -> Prims.Mkdtuple2 ((), (Obj.magic b))
let of_qbuf :
  'uuuuu .
    unit ->
      ('uuuuu, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer ->
        'uuuuu const_buffer
  = fun q -> fun b -> Prims.Mkdtuple2 ((), (Obj.magic b))
let null : 'a . unit -> 'a const_buffer =
  fun uu___ -> of_buffer (LowStar_Monotonic_Buffer.mnull ())
let is_null : 'a . 'a const_buffer -> Prims.bool =
  fun c -> let x = qbuf_mbuf c in LowStar_Monotonic_Buffer.is_null x
let index : 'a . 'a const_buffer -> FStar_UInt32.t -> 'a =
  fun c -> fun i -> let x = qbuf_mbuf c in LowStar_Monotonic_Buffer.index x i
type ('a, 'i, 'len, 'csub, 'c) const_sub_buffer = unit
let sub : 'a . 'a const_buffer -> FStar_UInt32.t -> unit -> 'a const_buffer =
  fun c ->
    fun i ->
      fun len ->
        let uu___ = c in
        match uu___ with
        | Prims.Mkdtuple2 (q, x) ->
            let x1 = Obj.magic x in
            let y = LowStar_Monotonic_Buffer.msub x1 i () in
            Prims.Mkdtuple2 ((), (Obj.magic y))
let cast :
  'a . 'a const_buffer -> ('a, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
  = fun c -> qbuf_mbuf c
let to_buffer : 'a . 'a const_buffer -> 'a LowStar_Buffer.buffer =
  fun uu___ -> (fun c -> Obj.magic (qbuf_mbuf c)) uu___
let to_ibuffer : 'a . 'a const_buffer -> 'a LowStar_ImmutableBuffer.ibuffer =
  fun uu___ -> (fun c -> Obj.magic (qbuf_mbuf c)) uu___
let (test :
  FStar_UInt32.t LowStar_Buffer.buffer ->
    FStar_UInt32.t LowStar_ImmutableBuffer.ibuffer -> FStar_UInt32.t)
  =
  fun x ->
    fun y ->
      let c1 = of_buffer x in
      let c2 = of_ibuffer y in
      (let h = FStar_HyperStack_ST.get () in
       LowStar_Monotonic_Buffer.upd' x Stdint.Uint32.zero Stdint.Uint32.one);
      (let a = index c1 Stdint.Uint32.zero in
       let a' = index c2 Stdint.Uint32.zero in
       let c3 = sub c2 Stdint.Uint32.one () in
       let a'' = index c3 Stdint.Uint32.zero in
       FStar_UInt32.add (FStar_UInt32.add a a') a'')