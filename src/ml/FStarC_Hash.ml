
type hash_code = int (* OCaml int *)

let cmp_hash (x:hash_code) (y:hash_code) : Z.t = Z.of_int (x-y)

let to_int (i:hash_code) : Z.t = Z.of_int i

(* NB: F* integers are unbounded, so we cannot use Z.to_int here: it
   raises Z.Overflow on large literals (e.g. 0xffffffffffffffff). Small
   integers are immediate in Zarith though, and are their own hash: this is on
   the path of every term construction, so avoid the C call for them. *)
let[@inline] of_int (i:Z.t) : hash_code =
  if Obj.is_int (Obj.repr i) then (Obj.magic i : int) else Z.hash i
let of_string (s:string) = BatHashtbl.hash s

(* The combining step of MurmurHash64A, on OCaml's 63-bit integers.

   This runs on every term construction (term hash codes are computed
   eagerly, see FStarC.Syntax.Syntax.mk), so it should be cheap: it used to be
   Bob Jenkins' 96-bit mix (http://burtleburtle.net/bob/hash/doobs.html),
   whose long dependency chain cost about three times as much, and which had
   more collisions in our tests. Simpler mixes, e.g. the one from Lean (src/runtime/hash.h),
   produce many collisions on terms such as those in
   tests/FStar.Tests.Pars.test_hashes. *)
let murmur_m = 0x1bd1e9955bd1e995
let[@inline] mix (a: hash_code) (b: hash_code) =
  let k = b * murmur_m in
  let k = k lxor (k lsr 31) in
  let k = k * murmur_m in
  (a lxor k) * murmur_m

let string_of_hash_code h = string_of_int h
