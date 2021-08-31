module RecordFieldDisambiguation

type r = { a:nat }
type s = { a:bool }

let test_project_s (x:s) : bool = x.a
let test_project_s2 (x:s) = x.a
let test_project_s3 x = x.a

let test_project_r (x:r) : nat = x.a
let test_project_r2 (x:r) = x.a
[@@expect_failure]
let test_project_r3 x : nat = x.a

let test_construct_s (x:bool) = { a = x }
let test_construct_s2 x : s = { a = x }
let test_construct_r2 x : r = { a = x }

let test_construct_r (x:nat) : r = { a = x }

[@@expect_failure]
let test_construct_r3 (x:nat) = { a = x }


type t0 = { f1:bool; f2:int }
type t1 = { f1:int; f2:bool }

let test_construct_t0_with_1 (x:t0) = { x with f2=0 }
let test_construct_t0_with_2 x : t0 = { x with f2=0 }
let test_construct_t1_with x = { x with f2=true }

let test_pattern_t0 (x:t0) =
  match x with
  | { f1=b; f2=i} -> if b then i + 1 else i - 1

let test_pattern_t0_1 (x:t0) =
  match x with
  | { f1=b } -> if b then 0 else 1

let test_pattern_t1 x =
  match x with
  | { f1=i; f2=b} -> if b then i + 1 else i - 1

type da =
  | D0 : x:int -> da

type db =
  | C0 : x:bool -> db

let test_project_da (f:da) = f.x
let test_project_db (f:db) = f.x

noeq
type recfun = { doit : unit -> unit }

let call0 (r:recfun) = let f = r.doit in f()
let call (r:recfun) = r.doit()
