open Prims
let constant_time_carry (a : FStar_UInt64.t) (b : FStar_UInt64.t) :
  FStar_UInt64.t=
  FStar_UInt64.shift_right
    (FStar_UInt64.logxor a
       (FStar_UInt64.logor (FStar_UInt64.logxor a b)
          (FStar_UInt64.logxor (FStar_UInt64.sub_mod a b) b)))
    (Stdint.Uint32.of_int 63)
type uint128 = {
  low: FStar_UInt64.t ;
  high: FStar_UInt64.t }
let __proj__Mkuint128__item__low (projectee : uint128) : FStar_UInt64.t=
  match projectee with | { low; high;_} -> low
let __proj__Mkuint128__item__high (projectee : uint128) : FStar_UInt64.t=
  match projectee with | { low; high;_} -> high
type t = uint128
let v (x : t) : Obj.t FStar_UInt.uint_t=
  (FStar_UInt64.v x.low) +
    ((FStar_UInt64.v x.high) * (Prims.pow2 (Prims.of_int 64)))
let uint_to_t (x : Obj.t FStar_UInt.uint_t) : t=
  {
    low = (FStar_UInt64.uint_to_t ((mod) x (Prims.pow2 (Prims.of_int 64))));
    high = (FStar_UInt64.uint_to_t (x / (Prims.pow2 (Prims.of_int 64))))
  }
let carry (a : FStar_UInt64.t) (b : FStar_UInt64.t) : FStar_UInt64.t=
  constant_time_carry a b
let add (a : t) (b : t) : t=
  {
    low = (FStar_UInt64.add_mod a.low b.low);
    high =
      (FStar_UInt64.add (FStar_UInt64.add a.high b.high)
         (carry (FStar_UInt64.add_mod a.low b.low) b.low))
  }
let add_underspec (a : t) (b : t) : t=
  {
    low = (FStar_UInt64.add_mod a.low b.low);
    high =
      (FStar_UInt64.add_underspec (FStar_UInt64.add_underspec a.high b.high)
         (carry (FStar_UInt64.add_mod a.low b.low) b.low))
  }
let add_mod (a : t) (b : t) : t=
  {
    low = (FStar_UInt64.add_mod a.low b.low);
    high =
      (FStar_UInt64.add_mod (FStar_UInt64.add_mod a.high b.high)
         (carry (FStar_UInt64.add_mod a.low b.low) b.low))
  }
let sub (a : t) (b : t) : t=
  {
    low = (FStar_UInt64.sub_mod a.low b.low);
    high =
      (FStar_UInt64.sub (FStar_UInt64.sub a.high b.high)
         (carry a.low (FStar_UInt64.sub_mod a.low b.low)))
  }
let sub_underspec (a : t) (b : t) : t=
  {
    low = (FStar_UInt64.sub_mod a.low b.low);
    high =
      (FStar_UInt64.sub_underspec (FStar_UInt64.sub_underspec a.high b.high)
         (carry a.low (FStar_UInt64.sub_mod a.low b.low)))
  }
let sub_mod_impl (a : t) (b : t) : t=
  {
    low = (FStar_UInt64.sub_mod a.low b.low);
    high =
      (FStar_UInt64.sub_mod (FStar_UInt64.sub_mod a.high b.high)
         (carry a.low (FStar_UInt64.sub_mod a.low b.low)))
  }
let sub_mod (a : t) (b : t) : t= sub_mod_impl a b
let append_uint (n1 : Prims.nat) (n2 : Prims.nat)
  (num1 : Obj.t FStar_UInt.uint_t) (num2 : Obj.t FStar_UInt.uint_t) :
  Obj.t FStar_UInt.uint_t= num1 + (num2 * (Prims.pow2 n1))
let vec128 (a : t) : Obj.t FStar_BitVector.bv_t=
  FStar_UInt.to_vec (Prims.of_int 128) (v a)
let vec64 (a : FStar_UInt64.t) : Obj.t FStar_BitVector.bv_t=
  FStar_UInt.to_vec (Prims.of_int 64) (FStar_UInt64.v a)
let logand (a : t) (b : t) : t=
  {
    low = (FStar_UInt64.logand a.low b.low);
    high = (FStar_UInt64.logand a.high b.high)
  }
let logxor (a : t) (b : t) : t=
  {
    low = (FStar_UInt64.logxor a.low b.low);
    high = (FStar_UInt64.logxor a.high b.high)
  }
let logor (a : t) (b : t) : t=
  {
    low = (FStar_UInt64.logor a.low b.low);
    high = (FStar_UInt64.logor a.high b.high)
  }
let lognot (a : t) : t=
  { low = (FStar_UInt64.lognot a.low); high = (FStar_UInt64.lognot a.high) }
let __uint_to_t (x : Prims.int) : t= uint_to_t x
let u32_64 : FStar_UInt32.t= FStar_UInt32.uint_to_t (Prims.of_int 64)
let add_u64_shift_left (hi : FStar_UInt64.t) (lo : FStar_UInt64.t)
  (s : FStar_UInt32.t) : FStar_UInt64.t=
  FStar_UInt64.add (FStar_UInt64.shift_left hi s)
    (FStar_UInt64.shift_right lo (FStar_UInt32.sub u32_64 s))
let add_u64_shift_left_respec (hi : FStar_UInt64.t) (lo : FStar_UInt64.t)
  (s : FStar_UInt32.t) : FStar_UInt64.t= add_u64_shift_left hi lo s
let shift_left_small (a : t) (s : FStar_UInt32.t) : t=
  if FStar_UInt32.eq s Stdint.Uint32.zero
  then a
  else
    {
      low = (FStar_UInt64.shift_left a.low s);
      high = (add_u64_shift_left_respec a.high a.low s)
    }
let shift_left_large (a : t) (s : FStar_UInt32.t) : t=
  {
    low = (FStar_UInt64.uint_to_t Prims.int_zero);
    high = (FStar_UInt64.shift_left a.low (FStar_UInt32.sub s u32_64))
  }
let shift_left (a : t) (s : FStar_UInt32.t) : t=
  if FStar_UInt32.lt s u32_64
  then shift_left_small a s
  else shift_left_large a s
let add_u64_shift_right (hi : FStar_UInt64.t) (lo : FStar_UInt64.t)
  (s : FStar_UInt32.t) : FStar_UInt64.t=
  FStar_UInt64.add (FStar_UInt64.shift_right lo s)
    (FStar_UInt64.shift_left hi (FStar_UInt32.sub u32_64 s))
let add_u64_shift_right_respec (hi : FStar_UInt64.t) (lo : FStar_UInt64.t)
  (s : FStar_UInt32.t) : FStar_UInt64.t= add_u64_shift_right hi lo s
let shift_right_small (a : t) (s : FStar_UInt32.t) : t=
  if FStar_UInt32.eq s Stdint.Uint32.zero
  then a
  else
    {
      low = (add_u64_shift_right_respec a.high a.low s);
      high = (FStar_UInt64.shift_right a.high s)
    }
let shift_right_large (a : t) (s : FStar_UInt32.t) : t=
  {
    low = (FStar_UInt64.shift_right a.high (FStar_UInt32.sub s u32_64));
    high = (FStar_UInt64.uint_to_t Prims.int_zero)
  }
let shift_right (a : t) (s : FStar_UInt32.t) : t=
  if FStar_UInt32.lt s u32_64
  then shift_right_small a s
  else shift_right_large a s
let eq (a : t) (b : t) : Prims.bool=
  (FStar_UInt64.eq a.low b.low) && (FStar_UInt64.eq a.high b.high)
let gt (a : t) (b : t) : Prims.bool=
  (FStar_UInt64.gt a.high b.high) ||
    ((FStar_UInt64.eq a.high b.high) && (FStar_UInt64.gt a.low b.low))
let lt (a : t) (b : t) : Prims.bool=
  (FStar_UInt64.lt a.high b.high) ||
    ((FStar_UInt64.eq a.high b.high) && (FStar_UInt64.lt a.low b.low))
let gte (a : t) (b : t) : Prims.bool=
  (FStar_UInt64.gt a.high b.high) ||
    ((FStar_UInt64.eq a.high b.high) && (FStar_UInt64.gte a.low b.low))
let lte (a : t) (b : t) : Prims.bool=
  (FStar_UInt64.lt a.high b.high) ||
    ((FStar_UInt64.eq a.high b.high) && (FStar_UInt64.lte a.low b.low))
let eq_mask (a : t) (b : t) : t=
  {
    low =
      (FStar_UInt64.logand (FStar_UInt64.eq_mask a.low b.low)
         (FStar_UInt64.eq_mask a.high b.high));
    high =
      (FStar_UInt64.logand (FStar_UInt64.eq_mask a.low b.low)
         (FStar_UInt64.eq_mask a.high b.high))
  }
let gte_mask (a : t) (b : t) : t=
  {
    low =
      (FStar_UInt64.logor
         (FStar_UInt64.logand (FStar_UInt64.gte_mask a.high b.high)
            (FStar_UInt64.lognot (FStar_UInt64.eq_mask a.high b.high)))
         (FStar_UInt64.logand (FStar_UInt64.eq_mask a.high b.high)
            (FStar_UInt64.gte_mask a.low b.low)));
    high =
      (FStar_UInt64.logor
         (FStar_UInt64.logand (FStar_UInt64.gte_mask a.high b.high)
            (FStar_UInt64.lognot (FStar_UInt64.eq_mask a.high b.high)))
         (FStar_UInt64.logand (FStar_UInt64.eq_mask a.high b.high)
            (FStar_UInt64.gte_mask a.low b.low)))
  }
let uint64_to_uint128 (a : FStar_UInt64.t) : t=
  { low = a; high = (FStar_UInt64.uint_to_t Prims.int_zero) }
let uint128_to_uint64 (a : t) : FStar_UInt64.t= a.low
let u64_l32_mask : FStar_UInt64.t=
  FStar_UInt64.uint_to_t (Prims.parse_int "0xffffffff")
let u64_mod_32 (a : FStar_UInt64.t) : FStar_UInt64.t=
  FStar_UInt64.logand a
    (FStar_UInt64.uint_to_t (Prims.parse_int "0xffffffff"))
let u32_32 : FStar_UInt32.t= FStar_UInt32.uint_to_t (Prims.of_int 32)
let u32_combine (hi : FStar_UInt64.t) (lo : FStar_UInt64.t) : FStar_UInt64.t=
  FStar_UInt64.add lo (FStar_UInt64.shift_left hi u32_32)
let mul32 (x : FStar_UInt64.t) (y : FStar_UInt32.t) : t=
  {
    low =
      (u32_combine
         (FStar_UInt64.add
            (FStar_UInt64.mul (FStar_UInt64.shift_right x u32_32)
               (FStar_Int_Cast.uint32_to_uint64 y))
            (FStar_UInt64.shift_right
               (FStar_UInt64.mul (u64_mod_32 x)
                  (FStar_Int_Cast.uint32_to_uint64 y)) u32_32))
         (u64_mod_32
            (FStar_UInt64.mul (u64_mod_32 x)
               (FStar_Int_Cast.uint32_to_uint64 y))));
    high =
      (FStar_UInt64.shift_right
         (FStar_UInt64.add
            (FStar_UInt64.mul (FStar_UInt64.shift_right x u32_32)
               (FStar_Int_Cast.uint32_to_uint64 y))
            (FStar_UInt64.shift_right
               (FStar_UInt64.mul (u64_mod_32 x)
                  (FStar_Int_Cast.uint32_to_uint64 y)) u32_32)) u32_32)
  }
let l32 (x : Obj.t FStar_UInt.uint_t) : Obj.t FStar_UInt.uint_t=
  (mod) x (Prims.pow2 (Prims.of_int 32))
let h32 (x : Obj.t FStar_UInt.uint_t) : Obj.t FStar_UInt.uint_t=
  x / (Prims.pow2 (Prims.of_int 32))
let mul32_bound (x : Obj.t FStar_UInt.uint_t) (y : Obj.t FStar_UInt.uint_t) :
  Obj.t FStar_UInt.uint_t= x * y
let pll (x : FStar_UInt64.t) (y : FStar_UInt64.t) : Obj.t FStar_UInt.uint_t=
  mul32_bound (l32 (FStar_UInt64.v x)) (l32 (FStar_UInt64.v y))
let plh (x : FStar_UInt64.t) (y : FStar_UInt64.t) : Obj.t FStar_UInt.uint_t=
  mul32_bound (l32 (FStar_UInt64.v x)) (h32 (FStar_UInt64.v y))
let phl (x : FStar_UInt64.t) (y : FStar_UInt64.t) : Obj.t FStar_UInt.uint_t=
  mul32_bound (h32 (FStar_UInt64.v x)) (l32 (FStar_UInt64.v y))
let phh (x : FStar_UInt64.t) (y : FStar_UInt64.t) : Obj.t FStar_UInt.uint_t=
  mul32_bound (h32 (FStar_UInt64.v x)) (h32 (FStar_UInt64.v y))
let pll_l (x : FStar_UInt64.t) (y : FStar_UInt64.t) :
  Obj.t FStar_UInt.uint_t= l32 (pll x y)
let pll_h (x : FStar_UInt64.t) (y : FStar_UInt64.t) :
  Obj.t FStar_UInt.uint_t= h32 (pll x y)
let mul_wide_low (x : FStar_UInt64.t) (y : FStar_UInt64.t) : Prims.int=
  ((mod)
     (((plh x y) +
         ((mod) ((phl x y) + (pll_h x y)) (Prims.pow2 (Prims.of_int 32))))
        * (Prims.pow2 (Prims.of_int 32))) (Prims.pow2 (Prims.of_int 64)))
    + (pll_l x y)
let mul_wide_high (x : FStar_UInt64.t) (y : FStar_UInt64.t) : Prims.int=
  ((phh x y) + (((phl x y) + (pll_h x y)) / (Prims.pow2 (Prims.of_int 32))))
    +
    (((plh x y) +
        ((mod) ((phl x y) + (pll_h x y)) (Prims.pow2 (Prims.of_int 32))))
       / (Prims.pow2 (Prims.of_int 32)))
let u32_combine' (hi : FStar_UInt64.t) (lo : FStar_UInt64.t) :
  FStar_UInt64.t= FStar_UInt64.add lo (FStar_UInt64.shift_left hi u32_32)
let mul_wide (x : FStar_UInt64.t) (y : FStar_UInt64.t) : t=
  {
    low =
      (u32_combine'
         (FStar_UInt64.add
            (FStar_UInt64.mul (u64_mod_32 x)
               (FStar_UInt64.shift_right y u32_32))
            (u64_mod_32
               (FStar_UInt64.add
                  (FStar_UInt64.mul (FStar_UInt64.shift_right x u32_32)
                     (u64_mod_32 y))
                  (FStar_UInt64.shift_right
                     (FStar_UInt64.mul (u64_mod_32 x) (u64_mod_32 y)) u32_32))))
         (u64_mod_32 (FStar_UInt64.mul (u64_mod_32 x) (u64_mod_32 y))));
    high =
      (FStar_UInt64.add_mod
         (FStar_UInt64.add
            (FStar_UInt64.mul (FStar_UInt64.shift_right x u32_32)
               (FStar_UInt64.shift_right y u32_32))
            (FStar_UInt64.shift_right
               (FStar_UInt64.add
                  (FStar_UInt64.mul (FStar_UInt64.shift_right x u32_32)
                     (u64_mod_32 y))
                  (FStar_UInt64.shift_right
                     (FStar_UInt64.mul (u64_mod_32 x) (u64_mod_32 y)) u32_32))
               u32_32))
         (FStar_UInt64.shift_right
            (FStar_UInt64.add
               (FStar_UInt64.mul (u64_mod_32 x)
                  (FStar_UInt64.shift_right y u32_32))
               (u64_mod_32
                  (FStar_UInt64.add
                     (FStar_UInt64.mul (FStar_UInt64.shift_right x u32_32)
                        (u64_mod_32 y))
                     (FStar_UInt64.shift_right
                        (FStar_UInt64.mul (u64_mod_32 x) (u64_mod_32 y))
                        u32_32)))) u32_32))
  }
