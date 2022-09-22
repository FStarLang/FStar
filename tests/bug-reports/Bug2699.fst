module Bug2699

open FStar.UInt32

inline_for_extraction noextract
let broken_get_length_f32 (i:UInt32.t) (n:UInt32.t{UInt32.v n <> 0}) : _ =
  FStar.UInt32.mul_mod (FStar.UInt32.div i n) n,
  FStar.UInt32.add_mod i n

let broken_length_f32 : _ = broken_get_length_f32 24ul 4ul

inline_for_extraction noextract
let works_get_length_f32 (i:UInt32.t{ UInt32.v i < 128 }) (n:UInt32.t{UInt32.v n <> 0 /\ UInt32.v n < 128}) : _ =
  assert_norm (128 + 128 < pow2 32 - 1);
  FStar.UInt32.mul (FStar.UInt32.div i n) n,
  FStar.UInt32.add i n

let works_length_f32 : _ = works_get_length_f32 24ul 4ul

open FStar.Tactics

let testu8_add_mod = assert FStar.UInt8.(250uy `add_mod` 6uy == 0uy)
            by (norm [primops]; trefl(); qed())

let testu8_sub_mod = assert FStar.UInt8.(6uy `sub_mod` 250uy == 12uy)
            by (norm [primops]; trefl(); qed())

let testu8_mul_mod = assert FStar.UInt8.(30uy `mul_mod` 12uy == 104uy)
            by (norm [primops]; trefl(); qed())

let testu8_gt = assert FStar.UInt8.(30uy `gt` 10uy)
            by (norm [primops]; trivial(); qed())

let testu8_gte = assert FStar.UInt8.(30uy `gte` 30uy)
            by (norm [primops]; trivial(); qed())

let testu8_lt = assert FStar.UInt8.(29uy `lt` 30uy)
            by (norm [primops]; trivial(); qed())

let testu8_lte = assert FStar.UInt8.(30uy `lte` 30uy)
            by (norm [primops]; trivial(); qed())


let testu16_add_mod = assert FStar.UInt16.(65530us `add_mod` 6us == 0us)
            by (norm [primops]; trefl(); qed())

let testu16_sub_mod = assert FStar.UInt16.(6us `sub_mod` 65530us == 12us)
            by (norm [primops]; trefl(); qed())

let testu16_mul_mod = assert FStar.UInt16.((256us `mul_mod` 256us) == 0us)
            by (norm [primops]; trefl(); qed())

let testu16_gt = assert FStar.UInt16.(30us `gt` 10us)
            by (norm [primops]; trivial(); qed())

let testu16_gte = assert FStar.UInt16.(30us `gte` 30us)
            by (norm [primops]; trivial(); qed())

let testu16_lt = assert FStar.UInt16.(29us `lt` 30us)
            by (norm [primops]; trivial(); qed())

let testu16_lte = assert FStar.UInt16.(30us `lte` 30us)
            by (norm [primops]; trivial(); qed())


let testu32_add_mod = assert FStar.UInt32.(0xfffffffaul `add_mod` 6ul == 0ul)
            by (norm [primops]; trefl(); qed())

let testu32_sub_mod = assert FStar.UInt32.(6ul `sub_mod` 0xfffffffaul == 12ul)
            by (norm [primops]; trefl(); qed())

let testu32_mul_mod = assert FStar.UInt32.((0x10000ul `mul_mod` 0x10000ul) == 0ul)
            by (norm [primops]; trefl(); qed())

let testu32_gt = assert FStar.UInt32.(30ul `gt` 10ul)
            by (norm [primops]; trivial(); qed())

let testu32_gte = assert FStar.UInt32.(30ul `gte` 30ul)
            by (norm [primops]; trivial(); qed())

let testu32_lt = assert FStar.UInt32.(29ul `lt` 30ul)
            by (norm [primops]; trivial(); qed())

let testu32_lte = assert FStar.UInt32.(30ul `lte` 30ul)
            by (norm [primops]; trivial(); qed())


let testu64_add_mod = assert FStar.UInt64.(0xfffffffffffffffauL `add_mod` 6uL == 0uL)
            by (norm [primops]; trefl(); qed())

let testu64_sub_mod = assert FStar.UInt64.(6uL `sub_mod` 0xfffffffffffffffauL == 12uL)
            by (norm [primops]; trefl(); qed())

let testu64_muL_mod = assert FStar.UInt64.((0x100000000uL `mul_mod` 0x100000000uL) == 0uL)
            by (norm [primops]; trefl(); qed())

let testu64_gt = assert FStar.UInt64.(30uL `gt` 10uL)
            by (norm [primops]; trivial(); qed())

let testu64_gte = assert FStar.UInt64.(30uL `gte` 30uL)
            by (norm [primops]; trivial(); qed())

let testu64_lt = assert FStar.UInt64.(29uL `lt` 30uL)
            by (norm [primops]; trivial(); qed())

let testu64_lte = assert FStar.UInt64.(30uL `lte` 30uL)
            by (norm [primops]; trivial(); qed())


let testu128_add_mod = assert FStar.UInt128.(uint_to_t 0xfffffffffffffffffffffffffffffffa `add_mod` uint_to_t 6 == uint_to_t 0)
            by (norm [primops]; trefl(); qed())

let testu128_sub_mod = assert FStar.UInt128.(uint_to_t 6 `sub_mod` uint_to_t 0xfffffffffffffffffffffffffffffffa == uint_to_t 12)
            by (norm [primops]; trefl(); qed())

// No mul_mod for 128
// let testu128_muL_mod = assert FStar.UInt128.((uint_to_t 0x1000000000000 `mul_mod` uint_to_t 0x1000000000000) == uint_to_t 0)
//             by (norm [primops]; trefl(); qed())

let testu128_gt = assert FStar.UInt128.(uint_to_t 30 `gt` uint_to_t 10)
            by (norm [primops]; trivial(); qed())

let testu128_gte = assert FStar.UInt128.(uint_to_t 30 `gte` uint_to_t 30)
            by (norm [primops]; trivial(); qed())

let testu128_lt = assert FStar.UInt128.(uint_to_t 29 `lt` uint_to_t 30)
            by (norm [primops]; trivial(); qed())

let testu128_lte = assert FStar.UInt128.(uint_to_t 30 `lte` uint_to_t 30)
            by (norm [primops]; trivial(); qed())



let nbe_testu8_add_mod = assert FStar.UInt8.(250uy `add_mod` 6uy == 0uy)
            by (norm [nbe;primops]; trefl(); qed())

let nbe_testu8_sub_mod = assert FStar.UInt8.(6uy `sub_mod` 250uy == 12uy)
            by (norm [nbe;primops]; trefl(); qed())

let nbe_testu8_mul_mod = assert FStar.UInt8.(30uy `mul_mod` 12uy == 104uy)
            by (norm [nbe;primops]; trefl(); qed())

let nbe_testu8_gt = assert FStar.UInt8.(30uy `gt` 10uy)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu8_gte = assert FStar.UInt8.(30uy `gte` 30uy)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu8_lt = assert FStar.UInt8.(29uy `lt` 30uy)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu8_lte = assert FStar.UInt8.(30uy `lte` 30uy)
            by (norm [nbe;primops]; trivial(); qed())


let nbe_testu16_add_mod = assert FStar.UInt16.(65530us `add_mod` 6us == 0us)
            by (norm [nbe;primops]; trefl(); qed())

let nbe_testu16_sub_mod = assert FStar.UInt16.(6us `sub_mod` 65530us == 12us)
            by (norm [nbe;primops]; trefl(); qed())

let nbe_testu16_mul_mod = assert FStar.UInt16.((256us `mul_mod` 256us) == 0us)
            by (norm [nbe;primops]; trefl(); qed())

let nbe_testu16_gt = assert FStar.UInt16.(30us `gt` 10us)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu16_gte = assert FStar.UInt16.(30us `gte` 30us)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu16_lt = assert FStar.UInt16.(29us `lt` 30us)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu16_lte = assert FStar.UInt16.(30us `lte` 30us)
            by (norm [nbe;primops]; trivial(); qed())


let nbe_testu32_add_mod = assert FStar.UInt32.(0xfffffffaul `add_mod` 6ul == 0ul)
            by (norm [nbe;primops]; trefl(); qed())

let nbe_testu32_sub_mod = assert FStar.UInt32.(6ul `sub_mod` 0xfffffffaul == 12ul)
            by (norm [nbe;primops]; trefl(); qed())

let nbe_testu32_mul_mod = assert FStar.UInt32.((0x10000ul `mul_mod` 0x10000ul) == 0ul)
            by (norm [nbe;primops]; trefl(); qed())

let nbe_testu32_gt = assert FStar.UInt32.(30ul `gt` 10ul)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu32_gte = assert FStar.UInt32.(30ul `gte` 30ul)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu32_lt = assert FStar.UInt32.(29ul `lt` 30ul)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu32_lte = assert FStar.UInt32.(30ul `lte` 30ul)
            by (norm [nbe;primops]; trivial(); qed())


let nbe_testu64_add_mod = assert FStar.UInt64.(0xfffffffffffffffauL `add_mod` 6uL == 0uL)
            by (norm [nbe;primops]; trefl(); qed())

let nbe_testu64_sub_mod = assert FStar.UInt64.(6uL `sub_mod` 0xfffffffffffffffauL == 12uL)
            by (norm [nbe;primops]; trefl(); qed())

let nbe_testu64_muL_mod = assert FStar.UInt64.((0x100000000uL `mul_mod` 0x100000000uL) == 0uL)
            by (norm [nbe;primops]; trefl(); qed())

let nbe_testu64_gt = assert FStar.UInt64.(30uL `gt` 10uL)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu64_gte = assert FStar.UInt64.(30uL `gte` 30uL)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu64_lt = assert FStar.UInt64.(29uL `lt` 30uL)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu64_lte = assert FStar.UInt64.(30uL `lte` 30uL)
            by (norm [nbe;primops]; trivial(); qed())


let nbe_testu128_add_mod = assert FStar.UInt128.(uint_to_t 0xfffffffffffffffffffffffffffffffa `add_mod` uint_to_t 6 == uint_to_t 0)
            by (norm [nbe;primops]; trefl(); qed())

let nbe_testu128_sub_mod = assert FStar.UInt128.(uint_to_t 6 `sub_mod` uint_to_t 0xfffffffffffffffffffffffffffffffa == uint_to_t 12)
            by (norm [nbe;primops]; trefl(); qed())

// No mul_mod for 128
// let nbe_testu128_muL_mod = assert FStar.UInt128.((uint_to_t 0x1000000000000 `mul_mod` uint_to_t 0x1000000000000) == uint_to_t 0)
//             by (norm [nbe;primops]; trefl(); qed())

let nbe_testu128_gt = assert FStar.UInt128.(uint_to_t 30 `gt` uint_to_t 10)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu128_gte = assert FStar.UInt128.(uint_to_t 30 `gte` uint_to_t 30)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu128_lt = assert FStar.UInt128.(uint_to_t 29 `lt` uint_to_t 30)
            by (norm [nbe;primops]; trivial(); qed())

let nbe_testu128_lte = assert FStar.UInt128.(uint_to_t 30 `lte` uint_to_t 30)
            by (norm [nbe;primops]; trivial(); qed())

