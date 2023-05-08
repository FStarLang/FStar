open Prims
type ('a, 'b) fact1 = unit
type ('a, 'b) fact0 = unit
let (constant_time_carry :
  FStar_UInt64.t -> FStar_UInt64.t -> FStar_UInt64.t) =
  fun a ->
    fun b ->
      FStar_UInt64.shift_right
        (FStar_UInt64.logxor a
           (FStar_UInt64.logor (FStar_UInt64.logxor a b)
              (FStar_UInt64.logxor (FStar_UInt64.sub_mod a b) b)))
        (Stdint.Uint32.of_int (63))
type uint128 = {
  low: FStar_UInt64.t ;
  high: FStar_UInt64.t }
let (__proj__Mkuint128__item__low : uint128 -> FStar_UInt64.t) =
  fun projectee -> match projectee with | { low; high;_} -> low
let (__proj__Mkuint128__item__high : uint128 -> FStar_UInt64.t) =
  fun projectee -> match projectee with | { low; high;_} -> high
type t = uint128
let (v : t -> unit FStar_UInt.uint_t) =
  fun x ->
    (FStar_UInt64.v x.low) +
      ((FStar_UInt64.v x.high) * (Prims.pow2 (Prims.of_int (64))))
let (uint_to_t : unit FStar_UInt.uint_t -> t) =
  fun x ->
    {
      low = (FStar_UInt64.uint_to_t (x mod (Prims.pow2 (Prims.of_int (64)))));
      high = (FStar_UInt64.uint_to_t (x / (Prims.pow2 (Prims.of_int (64)))))
    }
let (carry : FStar_UInt64.t -> FStar_UInt64.t -> FStar_UInt64.t) =
  fun a -> fun b -> constant_time_carry a b
let (add : t -> t -> t) =
  fun a ->
    fun b ->
      let l = FStar_UInt64.add_mod a.low b.low in
      {
        low = l;
        high =
          (FStar_UInt64.add (FStar_UInt64.add a.high b.high) (carry l b.low))
      }
let (add_underspec : t -> t -> t) =
  fun a ->
    fun b ->
      let l = FStar_UInt64.add_mod a.low b.low in
      {
        low = l;
        high =
          (FStar_UInt64.add_underspec
             (FStar_UInt64.add_underspec a.high b.high) (carry l b.low))
      }
let (add_mod : t -> t -> t) =
  fun a ->
    fun b ->
      let l = FStar_UInt64.add_mod a.low b.low in
      let r =
        {
          low = l;
          high =
            (FStar_UInt64.add_mod (FStar_UInt64.add_mod a.high b.high)
               (carry l b.low))
        } in
      let a_l = FStar_UInt64.v a.low in
      let a_h = FStar_UInt64.v a.high in
      let b_l = FStar_UInt64.v b.low in let b_h = FStar_UInt64.v b.high in r
let (sub : t -> t -> t) =
  fun a ->
    fun b ->
      let l = FStar_UInt64.sub_mod a.low b.low in
      {
        low = l;
        high =
          (FStar_UInt64.sub (FStar_UInt64.sub a.high b.high) (carry a.low l))
      }
let (sub_underspec : t -> t -> t) =
  fun a ->
    fun b ->
      let l = FStar_UInt64.sub_mod a.low b.low in
      {
        low = l;
        high =
          (FStar_UInt64.sub_underspec
             (FStar_UInt64.sub_underspec a.high b.high) (carry a.low l))
      }
let (sub_mod_impl : t -> t -> t) =
  fun a ->
    fun b ->
      let l = FStar_UInt64.sub_mod a.low b.low in
      {
        low = l;
        high =
          (FStar_UInt64.sub_mod (FStar_UInt64.sub_mod a.high b.high)
             (carry a.low l))
      }
let (sub_mod : t -> t -> t) = fun a -> fun b -> sub_mod_impl a b
let (append_uint :
  Prims.nat ->
    Prims.nat ->
      unit FStar_UInt.uint_t ->
        unit FStar_UInt.uint_t -> unit FStar_UInt.uint_t)
  =
  fun n1 -> fun n2 -> fun num1 -> fun num2 -> num1 + (num2 * (Prims.pow2 n1))
let (vec128 : t -> unit FStar_BitVector.bv_t) =
  fun a -> FStar_UInt.to_vec (Prims.of_int (128)) (v a)
let (vec64 : FStar_UInt64.t -> unit FStar_BitVector.bv_t) =
  fun a -> FStar_UInt.to_vec (Prims.of_int (64)) (FStar_UInt64.v a)
let (logand : t -> t -> t) =
  fun a ->
    fun b ->
      let r =
        {
          low = (FStar_UInt64.logand a.low b.low);
          high = (FStar_UInt64.logand a.high b.high)
        } in
      r
let (logxor : t -> t -> t) =
  fun a ->
    fun b ->
      let r =
        {
          low = (FStar_UInt64.logxor a.low b.low);
          high = (FStar_UInt64.logxor a.high b.high)
        } in
      r
let (logor : t -> t -> t) =
  fun a ->
    fun b ->
      let r =
        {
          low = (FStar_UInt64.logor a.low b.low);
          high = (FStar_UInt64.logor a.high b.high)
        } in
      r
let (lognot : t -> t) =
  fun a ->
    let r =
      {
        low = (FStar_UInt64.lognot a.low);
        high = (FStar_UInt64.lognot a.high)
      } in
    r
let (__uint_to_t : Prims.int -> t) = fun x -> uint_to_t x
let (u32_64 : FStar_UInt32.t) = FStar_UInt32.uint_to_t (Prims.of_int (64))
let (add_u64_shift_left :
  FStar_UInt64.t -> FStar_UInt64.t -> FStar_UInt32.t -> FStar_UInt64.t) =
  fun hi ->
    fun lo ->
      fun s ->
        let high = FStar_UInt64.shift_left hi s in
        let low = FStar_UInt64.shift_right lo (FStar_UInt32.sub u32_64 s) in
        let s1 = FStar_UInt32.v s in
        let high_n =
          ((FStar_UInt64.v hi) mod (Prims.pow2 ((Prims.of_int (64)) - s1))) *
            (Prims.pow2 s1) in
        let low_n =
          (FStar_UInt64.v lo) / (Prims.pow2 ((Prims.of_int (64)) - s1)) in
        FStar_UInt64.add high low
let (add_u64_shift_left_respec :
  FStar_UInt64.t -> FStar_UInt64.t -> FStar_UInt32.t -> FStar_UInt64.t) =
  fun hi ->
    fun lo ->
      fun s ->
        let r = add_u64_shift_left hi lo s in
        let hi1 = FStar_UInt64.v hi in
        let lo1 = FStar_UInt64.v lo in let s1 = FStar_UInt32.v s in r
let (shift_left_small : t -> FStar_UInt32.t -> t) =
  fun a ->
    fun s ->
      if FStar_UInt32.eq s Stdint.Uint32.zero
      then a
      else
        (let r =
           {
             low = (FStar_UInt64.shift_left a.low s);
             high = (add_u64_shift_left_respec a.high a.low s)
           } in
         let s1 = FStar_UInt32.v s in
         let a_l = FStar_UInt64.v a.low in
         let a_h = FStar_UInt64.v a.high in r)
let (shift_left_large : t -> FStar_UInt32.t -> t) =
  fun a ->
    fun s ->
      let h_shift = FStar_UInt32.sub s u32_64 in
      let r =
        {
          low = (FStar_UInt64.uint_to_t Prims.int_zero);
          high = (FStar_UInt64.shift_left a.low h_shift)
        } in
      r
let (shift_left : t -> FStar_UInt32.t -> t) =
  fun a ->
    fun s ->
      if FStar_UInt32.lt s u32_64
      then shift_left_small a s
      else shift_left_large a s
let (add_u64_shift_right :
  FStar_UInt64.t -> FStar_UInt64.t -> FStar_UInt32.t -> FStar_UInt64.t) =
  fun hi ->
    fun lo ->
      fun s ->
        let low = FStar_UInt64.shift_right lo s in
        let high = FStar_UInt64.shift_left hi (FStar_UInt32.sub u32_64 s) in
        let s1 = FStar_UInt32.v s in
        let low_n = (FStar_UInt64.v lo) / (Prims.pow2 s1) in
        let high_n =
          ((FStar_UInt64.v hi) mod (Prims.pow2 s1)) *
            (Prims.pow2 ((Prims.of_int (64)) - s1)) in
        FStar_UInt64.add low high
let (add_u64_shift_right_respec :
  FStar_UInt64.t -> FStar_UInt64.t -> FStar_UInt32.t -> FStar_UInt64.t) =
  fun hi ->
    fun lo ->
      fun s ->
        let r = add_u64_shift_right hi lo s in let s1 = FStar_UInt32.v s in r
let (shift_right_small : t -> FStar_UInt32.t -> t) =
  fun a ->
    fun s ->
      if FStar_UInt32.eq s Stdint.Uint32.zero
      then a
      else
        (let r =
           {
             low = (add_u64_shift_right_respec a.high a.low s);
             high = (FStar_UInt64.shift_right a.high s)
           } in
         let a_h = FStar_UInt64.v a.high in
         let a_l = FStar_UInt64.v a.low in let s1 = FStar_UInt32.v s in r)
let (shift_right_large : t -> FStar_UInt32.t -> t) =
  fun a ->
    fun s ->
      let r =
        {
          low = (FStar_UInt64.shift_right a.high (FStar_UInt32.sub s u32_64));
          high = (FStar_UInt64.uint_to_t Prims.int_zero)
        } in
      let s1 = FStar_UInt32.v s in r
let (shift_right : t -> FStar_UInt32.t -> t) =
  fun a ->
    fun s ->
      if FStar_UInt32.lt s u32_64
      then shift_right_small a s
      else shift_right_large a s
let (eq : t -> t -> Prims.bool) =
  fun a ->
    fun b -> (FStar_UInt64.eq a.low b.low) && (FStar_UInt64.eq a.high b.high)
let (gt : t -> t -> Prims.bool) =
  fun a ->
    fun b ->
      (FStar_UInt64.gt a.high b.high) ||
        ((FStar_UInt64.eq a.high b.high) && (FStar_UInt64.gt a.low b.low))
let (lt : t -> t -> Prims.bool) =
  fun a ->
    fun b ->
      (FStar_UInt64.lt a.high b.high) ||
        ((FStar_UInt64.eq a.high b.high) && (FStar_UInt64.lt a.low b.low))
let (gte : t -> t -> Prims.bool) =
  fun a ->
    fun b ->
      (FStar_UInt64.gt a.high b.high) ||
        ((FStar_UInt64.eq a.high b.high) && (FStar_UInt64.gte a.low b.low))
let (lte : t -> t -> Prims.bool) =
  fun a ->
    fun b ->
      (FStar_UInt64.lt a.high b.high) ||
        ((FStar_UInt64.eq a.high b.high) && (FStar_UInt64.lte a.low b.low))
let (eq_mask : t -> t -> t) =
  fun a ->
    fun b ->
      let mask =
        FStar_UInt64.logand (FStar_UInt64.eq_mask a.low b.low)
          (FStar_UInt64.eq_mask a.high b.high) in
      { low = mask; high = mask }
let (gte_mask : t -> t -> t) =
  fun a ->
    fun b ->
      let mask_hi_gte =
        FStar_UInt64.logand (FStar_UInt64.gte_mask a.high b.high)
          (FStar_UInt64.lognot (FStar_UInt64.eq_mask a.high b.high)) in
      let mask_lo_gte =
        FStar_UInt64.logand (FStar_UInt64.eq_mask a.high b.high)
          (FStar_UInt64.gte_mask a.low b.low) in
      let mask = FStar_UInt64.logor mask_hi_gte mask_lo_gte in
      { low = mask; high = mask }
let (uint64_to_uint128 : FStar_UInt64.t -> t) =
  fun a -> { low = a; high = (FStar_UInt64.uint_to_t Prims.int_zero) }
let (uint128_to_uint64 : t -> FStar_UInt64.t) = fun a -> a.low
let (u64_l32_mask : FStar_UInt64.t) =
  FStar_UInt64.uint_to_t (Prims.parse_int "0xffffffff")
let (u64_mod_32 : FStar_UInt64.t -> FStar_UInt64.t) =
  fun a ->
    FStar_UInt64.logand a
      (FStar_UInt64.uint_to_t (Prims.parse_int "0xffffffff"))
let (u32_32 : FStar_UInt32.t) = FStar_UInt32.uint_to_t (Prims.of_int (32))
let (u32_combine : FStar_UInt64.t -> FStar_UInt64.t -> FStar_UInt64.t) =
  fun hi -> fun lo -> FStar_UInt64.add lo (FStar_UInt64.shift_left hi u32_32)
let (mul32 : FStar_UInt64.t -> FStar_UInt32.t -> t) =
  fun x ->
    fun y ->
      let x0 = u64_mod_32 x in
      let x1 = FStar_UInt64.shift_right x u32_32 in
      let x0y = FStar_UInt64.mul x0 (FStar_Int_Cast.uint32_to_uint64 y) in
      let x0yl = u64_mod_32 x0y in
      let x0yh = FStar_UInt64.shift_right x0y u32_32 in
      let x1y' = FStar_UInt64.mul x1 (FStar_Int_Cast.uint32_to_uint64 y) in
      let x1y = FStar_UInt64.add x1y' x0yh in
      let r =
        {
          low = (u32_combine x1y x0yl);
          high = (FStar_UInt64.shift_right x1y u32_32)
        } in
      r
let (l32 : unit FStar_UInt.uint_t -> unit FStar_UInt.uint_t) =
  fun x -> x mod (Prims.pow2 (Prims.of_int (32)))
let (h32 : unit FStar_UInt.uint_t -> unit FStar_UInt.uint_t) =
  fun x -> x / (Prims.pow2 (Prims.of_int (32)))
let (mul32_bound :
  unit FStar_UInt.uint_t -> unit FStar_UInt.uint_t -> unit FStar_UInt.uint_t)
  = fun x -> fun y -> x * y
let (pll : FStar_UInt64.t -> FStar_UInt64.t -> unit FStar_UInt.uint_t) =
  fun x ->
    fun y -> mul32_bound (l32 (FStar_UInt64.v x)) (l32 (FStar_UInt64.v y))
let (plh : FStar_UInt64.t -> FStar_UInt64.t -> unit FStar_UInt.uint_t) =
  fun x ->
    fun y -> mul32_bound (l32 (FStar_UInt64.v x)) (h32 (FStar_UInt64.v y))
let (phl : FStar_UInt64.t -> FStar_UInt64.t -> unit FStar_UInt.uint_t) =
  fun x ->
    fun y -> mul32_bound (h32 (FStar_UInt64.v x)) (l32 (FStar_UInt64.v y))
let (phh : FStar_UInt64.t -> FStar_UInt64.t -> unit FStar_UInt.uint_t) =
  fun x ->
    fun y -> mul32_bound (h32 (FStar_UInt64.v x)) (h32 (FStar_UInt64.v y))
let (pll_l : FStar_UInt64.t -> FStar_UInt64.t -> unit FStar_UInt.uint_t) =
  fun x -> fun y -> l32 (pll x y)
let (pll_h : FStar_UInt64.t -> FStar_UInt64.t -> unit FStar_UInt.uint_t) =
  fun x -> fun y -> h32 (pll x y)
let (mul_wide_low : FStar_UInt64.t -> FStar_UInt64.t -> Prims.int) =
  fun x ->
    fun y ->
      ((((plh x y) +
           (((phl x y) + (pll_h x y)) mod (Prims.pow2 (Prims.of_int (32)))))
          * (Prims.pow2 (Prims.of_int (32))))
         mod (Prims.pow2 (Prims.of_int (64))))
        + (pll_l x y)
let (mul_wide_high : FStar_UInt64.t -> FStar_UInt64.t -> Prims.int) =
  fun x ->
    fun y ->
      ((phh x y) +
         (((phl x y) + (pll_h x y)) / (Prims.pow2 (Prims.of_int (32)))))
        +
        (((plh x y) +
            (((phl x y) + (pll_h x y)) mod (Prims.pow2 (Prims.of_int (32)))))
           / (Prims.pow2 (Prims.of_int (32))))
let (u32_combine' : FStar_UInt64.t -> FStar_UInt64.t -> FStar_UInt64.t) =
  fun hi -> fun lo -> FStar_UInt64.add lo (FStar_UInt64.shift_left hi u32_32)
let (mul_wide : FStar_UInt64.t -> FStar_UInt64.t -> t) =
  fun x ->
    fun y ->
      let uu___ =
        let u1 = u64_mod_32 x in
        let v1 = u64_mod_32 y in
        let t1 = FStar_UInt64.mul u1 v1 in
        let w3 = u64_mod_32 t1 in
        let k = FStar_UInt64.shift_right t1 u32_32 in
        let x' = FStar_UInt64.shift_right x u32_32 in
        let t' = FStar_UInt64.add (FStar_UInt64.mul x' v1) k in
        (u1, w3, x', t') in
      match uu___ with
      | (u1, w3, x', t') ->
          let k' = u64_mod_32 t' in
          let w1 = FStar_UInt64.shift_right t' u32_32 in
          let y' = FStar_UInt64.shift_right y u32_32 in
          let t'' = FStar_UInt64.add (FStar_UInt64.mul u1 y') k' in
          let k'' = FStar_UInt64.shift_right t'' u32_32 in
          let r0 = u32_combine' t'' w3 in
          let xy_w1 = FStar_UInt64.add (FStar_UInt64.mul x' y') w1 in
          let r1 = FStar_UInt64.add_mod xy_w1 k'' in
          let r = { low = r0; high = r1 } in r