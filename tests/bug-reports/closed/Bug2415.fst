module Bug2415

let sign = (z:int{z = 0 \/ z = (-1) \/ z = 1})

let example_1 (s:sign) : string =
 match s with
 | -1 -> "negative"
 | 1 -> "positive"
 | 0 -> "zero"
 | -2 -> assert False; ""

// The report also included a negative literal nested under Some.
let example_option (s:option sign) : string =
  match s with
  | Some (-1) -> "negative"
  | Some 1 -> "positive"
  | Some 0 -> "zero"
  | None -> "none"

let test_option () =
  assert (example_option (Some (-1)) == "negative");
  assert (example_option (Some 0) == "zero");
  assert (example_option (Some 1) == "positive");
  assert (example_option None == "none")

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
