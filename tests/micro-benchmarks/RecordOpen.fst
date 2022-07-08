module RecordOpen

open FStar.VConfig
open FStar.Mul

type ty = {x:int; y:bool}

let f (r:ty) : int =
  let open r <: ty in
  if y then x else -x

let _ = assert (f ({x=3; y=true}) == 3)
let _ = assert (f ({x=3; y=false}) == -3)

type ty2 (t:Type) = {x:t; y:bool}

(* Arguments on the type are OK *)
let f2 (r:ty2 int) : int =
  let open r <: ty2 int in
  if y then x else -x

(* Shadowing as expected *)
let f3 (r:ty2 int) : unit =
  assume (r.x == 10);
  let x = 42 in
  let open r <: ty2 int in
  assert (x == 10)

[@@expect_failure [189]]
let f4 (r:ty2 int) : int =
  let open r <: ty in
  if y then x else -x

let t = 42

[@@expect_failure [346]]
let not_a_record (r:ty2 int) : int =
  let open r <: int in
  if y then x else -x

type indty =
  | Mkindty : x:int -> indty

let f6 (r:indty) : int =
  let open r <: indty in
  x

let bump_rlimit (v:vconfig) : vconfig =
  let open v <: vconfig in
  { v with z3rlimit = 2 * z3rlimit }

let bump_rlimit2 (v:vconfig) : vconfig =
  let open v <: FStar.VConfig.vconfig in
  { v with z3rlimit = 2 * z3rlimit }

let bump_rlimit3 (v:vconfig) : vconfig =
  let open v <: VConfig.vconfig in
  { v with z3rlimit = 2 * z3rlimit }
