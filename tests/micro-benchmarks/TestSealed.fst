module TestSealed

open FStar.Sealed
open FStar.Tactics.V2

let test1 (x y : int) =
  sealed_singl (seal x) (seal y);
  assert (seal x == seal y)

// Using an SMT pattern
let is_sealed #a (s:sealed a) : prop = True

let my_seal (#a:Type) (x:a) : s:sealed a { is_sealed s } = seal x

let my_seal_singleton (#a:Type) (x y : sealed a)
  : Lemma 
    (x == y)
    [SMTPat (is_sealed x);
     SMTPat (is_sealed y)]
  = sealed_singl x y

let test1_auto (x y : int) =
  assert (my_seal x == my_seal y)

[@@expect_failure [19]]
let test2 (x y : int) =
  assert (seal x == seal y ==> x == y)

[@@expect_failure [19]]
let test3 (x y : int) =
  assert_norm (seal x =!= seal y)

(* Sealed values do not have to be equal at
different types. *)
[@@expect_failure [19; 19]]
let test4 (x : int) (y : nat) =
  assert (seal #int x == seal #nat y)

let rec sfac (n:nat) : Tac (sealed nat) =
  match n with
  | 0 -> seal 1
  | _ -> seal (n * unseal (sfac (n-1)))

(* Testing it actually runs *)
let _ = assert True by begin
  let r = unseal (sfac 5) in
  if r <> 120 then
    fail "bad"
end

//With inhabited seals
module I = FStar.Sealed.Inhabited
let snat = I.sealed #nat 0
let sealnat x : snat = I.seal x
let sealnat_auto (x y : nat) =
  assert (sealnat x == sealnat y)
let rec snatfac (n:nat) : Tac snat =
  match n with
  | 0 -> sealnat 1
  | _ -> sealnat (n * unseal (snatfac (n-1)))

let _ = assert True by begin
  let r = unseal (snatfac 5) in
  if r <> 120 then
    fail "bad"
end

(* map_seal and bind_seal *)
let _ = assert True by begin
  let f (x:int) : int = x*2 in
  let s = seal 123 in
  let s = map_seal s f in
  let r = unseal s in
  if r <> 246 then
    fail "bad"
end

let _ = assert True by begin
  let t = `(map_seal #int #int (seal 1) (fun (x:int) -> x+1)) in
  print (term_to_string t);
  let t = norm_term [primops] t in
  print (term_to_string t);
  if not (term_eq t (`seal u#0 #int 2)) then
    fail "not equal";
  ()
end

let _ = assert True by begin
  let f (x:int) : sealed int = seal (x*2) in
  let s = seal 123 in
  let s = bind_seal s f in
  let r = unseal s in
  if r <> 246 then
    fail "bad"
end

let _ = assert True by begin
  let t = `(bind_seal #int #int (seal 1) (fun (x:int) -> seal (x+1))) in
  print (term_to_string t);
  let t = norm_term [primops] t in
  print (term_to_string t);
  if not (term_eq t (`seal u#0 #int 2)) then
    fail "not equal";
  ()
end

(* [unseal] lives in [Nd], which is a subeffect of [Tac] (used above),
   but is also usable on its own, in total code. *)
let unseal_nd (#a:Type) (s : sealed a) : Nd a = FStar.Sealed.unseal s

(* It reveals nothing: [Nd] is nondeterministic, so [sealed_singl]
   cannot be used to equate arbitrary values. *)
[@@expect_failure [19]]
let unseal_no_spec (x:int) : Nd unit =
  let v = FStar.Sealed.unseal (seal x) in
  assert (v == x)

[@@expect_failure [19]]
let unseal_not_a_function (x:int) : Nd unit =
  let a = FStar.Sealed.unseal (seal x) in
  let b = FStar.Sealed.unseal (seal x) in
  assert (a == b)

[@@expect_failure [19]]
let unseal_no_contradiction () : Nd unit =
  sealed_singl (seal 0) (seal 1);
  let a = FStar.Sealed.unseal (seal 0) in
  let b = FStar.Sealed.unseal (seal 1) in
  assert (a == b)

(* map_seal/bind_seal accept Nd functions, in particular ones that
   themselves unseal. *)
let map_seal_nd (s : sealed (sealed int)) : sealed int =
  map_seal s (fun s' -> FStar.Sealed.unseal s')

let bind_seal_nd (s : sealed (sealed int)) : sealed int =
  bind_seal s (fun s' -> seal (FStar.Sealed.unseal s'))

(* And it reduces at the meta level. *)
let _ = assert True by begin
  let t = `(FStar.Sealed.unseal #int (seal 1)) in
  let t = norm_term [primops] t in
  if not (term_eq t (`1)) then
    fail "unseal did not reduce";
  ()
end
