(* We want to use Big_int from the num library. However, this type
   does not support OCaml comparisons, failing with "abstract
   value". Thus, we need to represent them with compare-enabled OCaml
   values, and convert to and from them.

   We represent a nonnegative big integer as its length
   and its representation as a decimal number.

   We represent a negative big integer as 0 - its length, and its
   representation as a decimal number where each digit x is replaced
   with (10-x)%10 (i.e. 0 becomes 9, 1 becomes 8, etc.)

   This way, OCaml comparisons not only work, but also are correct:

   - OCaml compares strings lexicographically starting from index 0,
     and compares records lexicographically following the order in which
     record fields are declared

   - Replacing the digits of negative number representations is
     actually equivalent to taking the 10's complement
*)
type bigint = {
    length: int;
    value: string;
}

type t = bigint

(* BEGIN conversion functions *)

  let mirror_char = function
  | '0' -> '9'
  | '1' -> '8'
  | '2' -> '7'
  | '3' -> '6'
  | '4' -> '5'
  | '5' -> '4'
  | '6' -> '3'
  | '7' -> '2'
  | '8' -> '1'
  | '9' -> '0'
  | x -> x


let bigint_of_big_int'
  (x: Big_int.big_int)
: bigint
=
  let open Big_int in
  let nonneg = le_big_int zero_big_int x in
  let s = string_of_big_int x in
  let s0 = s in
  let len = String.length s in
  let s =
    if nonneg
    then s
    else String.map mirror_char s
  in
(*  prerr_string (Printf.sprintf "bigint_of_big_int' : from %s to %s\n" s0 s); *)
  {
    length = (if nonneg then len else 0-len);
    value = s;
  }

let big_int_of_bigint'
  (x: bigint)
: Big_int.big_int
=
  let open Big_int in
  let nonneg = x.length >= 0 in
  let s =
    if nonneg
    then x.value
    else String.map mirror_char x.value
  in
(*  prerr_string (Printf.sprintf "big_int_of_bigint' : from %s to %s\n" x.value s); *)
  big_int_of_string s

let bigint_of_big_int x =
  let y = bigint_of_big_int' x in
(*  assert (BIGINT.eq_big_int (big_int_of_bigint' y) x); *)
  y

let big_int_of_bigint x =
  let y = big_int_of_bigint' x in
(*  assert (bigint_of_big_int' y = x); *)
  y

let cto (f: 'a -> Big_int.big_int) (x: 'a) : bigint =
  bigint_of_big_int (f x)

let cfrom1 (f: Big_int.big_int -> 'a) (x: bigint) : 'a =
  f (big_int_of_bigint x)

let cfrom2 (f: Big_int.big_int -> Big_int.big_int -> 'a) : bigint -> bigint -> 'a =
  cfrom1 (fun x -> cfrom1 (f x))

let cunop f = cto (cfrom1 f)

let cbinop f = cfrom2 (fun x -> cto (f x))

let cbinop1 f = cfrom1 (fun x -> cto (f x))

(* END conversion functions *)

let zero = bigint_of_big_int Big_int.zero_big_int
let one = bigint_of_big_int Big_int.unit_big_int
let two = bigint_of_big_int (Big_int.big_int_of_int 2)

let succ_big_int = cunop Big_int.succ_big_int
let pred_big_int = cunop Big_int.pred_big_int
let minus_big_int = cunop Big_int.minus_big_int
let abs_big_int = cunop Big_int.abs_big_int

let add_big_int = cbinop Big_int.add_big_int
let mult_big_int = cbinop Big_int.mult_big_int
let sub_big_int = cbinop Big_int.sub_big_int
let div_big_int = cbinop Big_int.div_big_int
let mod_big_int = cbinop Big_int.mod_big_int

let ediv_big_int = cbinop Big_int.div_big_int
let erem_big_int = cbinop Big_int.mod_big_int

let eq_big_int = ( = )
let le_big_int = ( <= )
let lt_big_int = ( < )
let ge_big_int = ( >= )
let gt_big_int = ( > )

(* Bitwise not is not provided by Big_int, but the identity is well-known *)
let lognot_big_int' x =
  Big_int.sub_big_int (Big_int.minus_big_int x) Big_int.unit_big_int

(* Big_int bitwise operators operate on nonnegative values only.  So
   we need to extend their domains to negative values with De Morgan
   identities and left-truncatures.

   If a is nonnegative and b is negative, then `bitwise_truncate a b`
   computes b with its "lead ones" truncated to match the size of
   a. This is enough to compute "bitwise and".
*)
let bitwise_truncate a b =
  let not_b = lognot_big_int' b in
  let nbits = BatBig_int.num_bits_big_int a in
  let significant_bits = Big_int.sub_big_int (Big_int.power_int_positive_int 2 nbits) Big_int.unit_big_int in
  Big_int.xor_big_int not_b significant_bits
let bitwise_and_pos_neg a b =
  Big_int.and_big_int a (bitwise_truncate a b)
let big_int_is_nonnegative x =
  Big_int.sign_big_int x >= 0
let logand_big_int' a b =
  match big_int_is_nonnegative a, big_int_is_nonnegative b with
  | true, true -> Big_int.and_big_int a b
  | true, false -> bitwise_and_pos_neg a b
  | false, true -> bitwise_and_pos_neg b a
  | _ -> lognot_big_int' (Big_int.or_big_int (lognot_big_int' a) (lognot_big_int' b))
let logor_big_int' a b =
  if big_int_is_nonnegative a && big_int_is_nonnegative b
  then Big_int.or_big_int a b
  else lognot_big_int' (logand_big_int' (lognot_big_int' a) (lognot_big_int' b))
let logxor_big_int' a b =
  match big_int_is_nonnegative a, big_int_is_nonnegative b with
  | true, true -> Big_int.xor_big_int a b
  | false, false -> Big_int.xor_big_int (lognot_big_int' a) (lognot_big_int' b)
  | _ ->
     logor_big_int'
       (logand_big_int' (lognot_big_int' a) b)
       (logand_big_int' (lognot_big_int' b) a)
  
let logand_big_int = cbinop logand_big_int'
let logor_big_int = cbinop logor_big_int'
let logxor_big_int = cbinop logxor_big_int'
let lognot_big_int = cunop lognot_big_int'

let shift_left_big_int' x y =
  Big_int.shift_left_big_int x (Big_int.int_of_big_int y)
let shift_left_big_int = cbinop shift_left_big_int'
let shift_right_big_int' x y =
  Big_int.shift_right_big_int x (Big_int.int_of_big_int y)
let shift_right_big_int = cbinop shift_right_big_int'
let shift_arithmetic_left_big_int = cbinop1 Big_int.shift_left_big_int
let shift_arithmetic_right_big_int = cbinop1 Big_int.shift_right_big_int

let sqrt_big_int = cunop Big_int.sqrt_big_int

let of_int = cto Big_int.big_int_of_int
let to_int = cfrom1 Big_int.int_of_big_int

let of_int_fs x = x
let to_int_fs x = x

let big_int_of_string' x =
    try
      Big_int.big_int_of_string x
    with _ ->
      (* FStar_Compiler_Util.safe_int_of_string expects big_int_of_string
         to raise Invalid_argument in case of failure *)
      raise (Invalid_argument "big_int_of_string")
let big_int_of_string = cto big_int_of_string'
let string_of_big_int = cfrom1 Big_int.string_of_big_int

let of_hex' =
  let v0 = Big_int.zero_big_int in
  let v1 = Big_int.unit_big_int in
  let v2 = Big_int.big_int_of_int 2 in
  let v3 = Big_int.big_int_of_int 3 in
  let v4 = Big_int.big_int_of_int 4 in
  let v5 = Big_int.big_int_of_int 5 in
  let v6 = Big_int.big_int_of_int 6 in
  let v7 = Big_int.big_int_of_int 7 in
  let v8 = Big_int.big_int_of_int 8 in
  let v9 = Big_int.big_int_of_int 9 in
  let va = Big_int.big_int_of_int 10 in
  let vb = Big_int.big_int_of_int 11 in
  let vc = Big_int.big_int_of_int 12 in
  let vd = Big_int.big_int_of_int 13 in
  let ve = Big_int.big_int_of_int 14 in
  let vf = Big_int.big_int_of_int 15 in
  let vsixteen = Big_int.big_int_of_int 16 in
  let hex_of_char = function
    | '0' -> v0
    | '1' -> v1
    | '2' -> v2
    | '3' -> v3
    | '4' -> v4
    | '5' -> v5
    | '6' -> v6
    | '7' -> v7
    | '8' -> v8
    | '9' -> v9
    | 'a' | 'A' -> va
    | 'b' | 'B' -> vb
    | 'c' | 'C' -> vc
    | 'd' | 'D' -> vd
    | 'e' | 'E' -> ve
    | 'f' | 'F' -> vf
    | _ -> failwith "hex_of_char"
  in
  fun s ->
  let rec aux accu i =
    if i = 0
    then accu
    else
      let i = i - 1 in
      let accu = Big_int.mult_big_int accu vsixteen in
      let accu = Big_int.add_big_int accu (hex_of_char (String.get s i)) in
      aux accu i
  in
  aux Big_int.zero_big_int (String.length s)
let of_hex = cto of_hex'
let pp_print' fmt x = Format.pp_print_string fmt (Big_int.string_of_big_int x)
let pp_print fmt = cfrom1 (pp_print' fmt)

let of_float = cto BatBig_int.of_float
let to_float = cfrom1 Big_int.float_of_big_int

let of_int64 = cto Big_int.big_int_of_int64
let to_int64 = cfrom1 Big_int.int64_of_big_int

module HashedType : BatHashtbl.HashedType with type t = bigint = struct
  type t = bigint
  let hash = BatHashtbl.hash
  let equal = ( = )
end

module OrderedType : BatInterfaces.OrderedType with type t = bigint = struct
  type t = bigint
  let compare = cfrom2 Big_int.compare_big_int
end

type krmlint = int
let krmlint_of_int_fs = to_int
