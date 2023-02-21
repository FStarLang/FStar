open Prims
type uint32_t = FStar_UInt32.t
let (max_uint32 : uint32_t) = (Stdint.Uint32.of_string "4294967295")
type 'a vector_str =
  | Vec of uint32_t * uint32_t * 'a LowStar_Buffer.buffer 
let uu___is_Vec : 'a . 'a vector_str -> Prims.bool = fun projectee -> true
let __proj__Vec__item__sz : 'a . 'a vector_str -> uint32_t =
  fun projectee -> match projectee with | Vec (sz, cap, vs) -> sz
let __proj__Vec__item__cap : 'a . 'a vector_str -> uint32_t =
  fun projectee -> match projectee with | Vec (sz, cap, vs) -> cap
let __proj__Vec__item__vs : 'a . 'a vector_str -> 'a LowStar_Buffer.buffer =
  fun projectee -> match projectee with | Vec (sz, cap, vs) -> vs
type 'a vector = 'a vector_str
let size_of : 'a . 'a vector -> uint32_t =
  fun vec -> match vec with | Vec (sz, cap, vs) -> sz
let capacity_of : 'a . 'a vector -> uint32_t =
  fun vec -> match vec with | Vec (sz, cap, vs) -> cap
let is_empty : 'a . 'a vector -> Prims.bool =
  fun vec -> (match vec with | Vec (sz, cap, vs) -> sz) = Stdint.Uint32.zero
type ('a, 'h, 'vec) live =
  ('a, unit, unit, unit, unit) LowStar_Monotonic_Buffer.live
type ('a, 'vec) freeable =
  ('a, unit, unit, unit) LowStar_Monotonic_Buffer.freeable

type ('h0, 'h1) hmap_dom_eq = (unit, unit, unit) FStar_Set.equal
let alloc_empty : 'a . unit -> 'a vector =
  fun uu___ ->
    Vec
      (Stdint.Uint32.zero, Stdint.Uint32.zero,
        (LowStar_Monotonic_Buffer.mnull ()))
let alloc_rid : 'a . uint32_t -> 'a -> unit -> 'a vector =
  fun len ->
    fun v ->
      fun rid ->
        let uu___ = LowStar_Monotonic_Buffer.mmalloc () v len in
        Vec (len, len, uu___)
let alloc : 'a . uint32_t -> 'a -> 'a vector =
  fun len -> fun v -> alloc_rid len v ()
let alloc_reserve : 'a . uint32_t -> 'a -> unit -> 'a vector =
  fun len ->
    fun ia ->
      fun rid ->
        let uu___ = LowStar_Monotonic_Buffer.mmalloc () ia len in
        Vec (Stdint.Uint32.zero, len, uu___)
let alloc_by_buffer : 'a . uint32_t -> 'a LowStar_Buffer.buffer -> 'a vector
  = fun len -> fun buf -> Vec (len, len, buf)
let free : 'a . 'a vector -> unit =
  fun vec ->
    LowStar_Monotonic_Buffer.free (match vec with | Vec (sz, cap, vs) -> vs)
let index : 'a . 'a vector -> uint32_t -> 'a =
  fun vec ->
    fun i ->
      LowStar_Monotonic_Buffer.index
        (match vec with | Vec (sz, cap, vs) -> vs) i
let front : 'a . 'a vector -> 'a =
  fun vec ->
    LowStar_Monotonic_Buffer.index (match vec with | Vec (sz, cap, vs) -> vs)
      Stdint.Uint32.zero
let back : 'a . 'a vector -> 'a =
  fun vec ->
    LowStar_Monotonic_Buffer.index (match vec with | Vec (sz, cap, vs) -> vs)
      (FStar_UInt32.sub (match vec with | Vec (sz, cap, vs) -> sz)
         Stdint.Uint32.one)
let clear : 'a . 'a vector -> 'a vector =
  fun vec ->
    Vec
      (Stdint.Uint32.zero, (match vec with | Vec (sz, cap, vs) -> cap),
        (match vec with | Vec (sz, cap, vs) -> vs))
let assign : 'a . 'a vector -> uint32_t -> 'a -> unit =
  fun vec ->
    fun i ->
      fun v ->
        let hh0 = FStar_HyperStack_ST.get () in
        (let uu___1 =
           LowStar_Monotonic_Buffer.msub
             (match vec with | Vec (sz, cap, vs) -> vs) i () in
         let h = FStar_HyperStack_ST.get () in
         LowStar_Monotonic_Buffer.upd' uu___1 Stdint.Uint32.zero v);
        (let hh1 = FStar_HyperStack_ST.get () in ())
let (resize_ratio : uint32_t) = (Stdint.Uint32.of_int (2))
let (new_capacity : uint32_t -> uint32_t) =
  fun cap ->
    if FStar_UInt32.gte cap (FStar_UInt32.div max_uint32 resize_ratio)
    then max_uint32
    else
      if cap = Stdint.Uint32.zero
      then Stdint.Uint32.one
      else FStar_UInt32.mul cap resize_ratio
let insert : 'a . 'a vector -> 'a -> 'a vector =
  fun vec ->
    fun v ->
      let sz = match vec with | Vec (sz1, cap, vs) -> sz1 in
      let cap = match vec with | Vec (sz1, cap1, vs) -> cap1 in
      let vs = match vec with | Vec (sz1, cap1, vs1) -> vs1 in
      if sz = cap
      then
        let ncap = new_capacity cap in
        let nvs = LowStar_Monotonic_Buffer.mmalloc () v ncap in
        (LowStar_Monotonic_Buffer.blit vs Stdint.Uint32.zero nvs
           Stdint.Uint32.zero sz;
         (let h = FStar_HyperStack_ST.get () in
          LowStar_Monotonic_Buffer.upd' nvs sz v);
         LowStar_Monotonic_Buffer.free vs;
         Vec ((FStar_UInt32.add sz Stdint.Uint32.one), ncap, nvs))
      else
        ((let h = FStar_HyperStack_ST.get () in
          LowStar_Monotonic_Buffer.upd' vs sz v);
         Vec ((FStar_UInt32.add sz Stdint.Uint32.one), cap, vs))
let flush : 'a . 'a vector -> 'a -> uint32_t -> 'a vector =
  fun vec ->
    fun ia ->
      fun i ->
        let fsz =
          FStar_UInt32.sub (match vec with | Vec (sz, cap, vs) -> sz) i in
        let asz =
          if (match vec with | Vec (sz, cap, vs) -> sz) = i
          then Stdint.Uint32.one
          else fsz in
        let vs = match vec with | Vec (sz, cap, vs1) -> vs1 in
        let fvs = LowStar_Monotonic_Buffer.mmalloc () ia asz in
        LowStar_Monotonic_Buffer.blit vs i fvs Stdint.Uint32.zero fsz;
        LowStar_Monotonic_Buffer.free vs;
        Vec (fsz, asz, fvs)
let shrink : 'a . 'a vector -> uint32_t -> 'a vector =
  fun vec ->
    fun new_size ->
      Vec
        (new_size, (match vec with | Vec (sz, cap, vs) -> cap),
          (match vec with | Vec (sz, cap, vs) -> vs))
let rec fold_left_buffer :
  'a 'b .
    uint32_t -> 'a LowStar_Buffer.buffer -> ('b -> 'a -> 'b) -> 'b -> 'b
  =
  fun len ->
    fun buf ->
      fun f ->
        fun ib ->
          if len = Stdint.Uint32.zero
          then ib
          else
            (let uu___1 =
               LowStar_Monotonic_Buffer.msub buf Stdint.Uint32.one () in
             let uu___2 =
               let uu___3 =
                 LowStar_Monotonic_Buffer.index buf Stdint.Uint32.zero in
               f ib uu___3 in
             fold_left_buffer (FStar_UInt32.sub len Stdint.Uint32.one) uu___1
               f uu___2)
let fold_left : 'a 'b . 'a vector -> ('b -> 'a -> 'b) -> 'b -> 'b =
  fun vec ->
    fun f ->
      fun ib ->
        let uu___ =
          LowStar_Monotonic_Buffer.msub
            (match vec with | Vec (sz, cap, vs) -> vs) Stdint.Uint32.zero () in
        fold_left_buffer (match vec with | Vec (sz, cap, vs) -> sz) uu___ f
          ib
type ('a, 'seq, 'i, 'j, 'p) forall_seq = unit
type ('a, 'h, 'buf, 'i, 'j, 'p) forall_buffer = unit
type ('a, 'h, 'vec, 'i, 'j, 'p) forall_ = unit
type ('a, 'h, 'vec, 'p) forall_all = unit
type ('a, 'seq, 'i, 'j, 'p) forall2_seq = unit
type ('a, 'h, 'buf, 'i, 'j, 'p) forall2_buffer = unit
type ('a, 'h, 'vec, 'i, 'j, 'p) forall2 = unit
type ('a, 'h, 'vec, 'p) forall2_all = unit