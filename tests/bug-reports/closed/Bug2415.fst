module Bug2415

let sign = (z:int{z = 0 \/ z = (-1) \/ z = 1})

let example_1 (s:sign) : string =
 match s with
 | -1 -> "negative"
 | 1 -> "positive"
 | 0 -> "zero"
 | -2 -> assert False; ""

open FStar.Int32
open FStar.Int8
open FStar.UInt32
open FStar.UInt8

type i8 = FStar.Int8.t
type i32 = FStar.Int32.t
type u8 = FStar.UInt8.t
type u32 = FStar.UInt32.t

let test1 (n:i32) =
  match n with
  | -1l -> assert (Int32.v n == -1)
  | 1l -> assert (Int32.v n == 1)
  | _ -> ()

[@@ expect_failure [114]]  // type of pattern (Int32.t) does not match the type of scrutinee (Int8.t)
let test2 (n:i8) =
  match n with
  | -0l -> ()
  | _ -> ()
