module RecordFieldDisambiguation

type tf0 = { f : bool }
type tf1 = { f : bool }
let test_tf0_1 (x:tf0) (y:tf1) = x.f && y.f
let test_tf0_2 (x:tf0) : tf1 = { f = x.f }

let tf0_abbrev0 = tf0
let proj_tf0_abbrev0 (x:tf0_abbrev0) = x.f
let mk_tf0_abbrev0 (x:bool) : tf0_abbrev0 = { f = x }

let tf0_abbrev1 (n:nat) = tf0_abbrev0
let proj_tf0_abbrev1 (x:nat) (y:tf0_abbrev1 x) = y.f
let mk_tf0_abbrev1 (y:bool) : tf0_abbrev1 0 = { f = y }

let tf0_abbrev2 (n:nat) : Type = tf0_abbrev1 n
let proj_tf0_abbrev2 (x:nat) (y:tf0_abbrev2 x) = y.f
let mk_tf0_abbrev2 (y:bool) : tf0_abbrev2 0 = { f = y }

type r = { a:nat }
type s = { a:bool }

let test_project_s (x:s) : bool = x.a
let test_project_s2 (x:s) = x.a
let test_project_s3 x = x.a

let test_project_r (x:r) : nat = x.a
let test_project_r2 (x:r) = x.a
[@@expect_failure]
let test_project_r3 x : nat = x.a

let test_construct_s x = { a = x }
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

////////////////////////////////////////////////////////////////////////////////
//Universe polymorphic records
////////////////////////////////////////////////////////////////////////////////
noeq
type upoly_t = {
  actions: Type u#a
}

type aaa = {
  actions:bool
}

let mk_upoly_t (a:Type) : upoly_t = { actions = a }
let proj_upoly_t (prog: upoly_t) : Type = prog.actions
let match_upoly_t (p:upoly_t) = let { actions = t } = p in t

let mk_aaa (a:bool) : aaa = { actions = a }
let proj_aaa (prog: aaa) : bool = prog.actions
let match_aaa (p:aaa) = let { actions = t } = p in t
