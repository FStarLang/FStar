module CherrySharedGlobal
module U32 = FStar.UInt32
module A = FStar.ImmutableArray
open FStar.All

(* A global whose value was held by a global reference before the global
   was computed: [a] is stored into one and taken out again, so that the
   global holds its only reference.  (The store used to mark [a] shared; it
   no longer does before the program starts a thread, see
   CherryGlobalRefShare.)  Persisting the global makes it persistent, shared
   or not (cherry.h, [cherry_mark_ref]): a global is read without an inc, so
   [set g] hands the global's reference to [upd], which would otherwise take
   it for the only one and change the global in place, or with the count
   dropping to zero free it. *)
let hide (#a: Type) (x: a) : ML a = x

let r : ref (option (A.t string)) = alloc None

#push-options "--admit_smt_queries true"
let g : A.t string =
  let a = hide (A.of_list ["x"; "y"]) in
  r := Some a;
  r := None;
  a
#pop-options

let set (#a: Type) (s: A.t a) (i: nat) (v: a) : A.t a =
  if i < A.length s then A.upd s i v else s

let rec cat (l: list string) : string =
  match l with [] -> "" | x :: r -> x ^ cat r

let main () : ML U32.t =
  let h = set g 0 (hide "w") in
  if cat (A.to_list g) = "xy" && cat (A.to_list h) = "wy" then 0ul else 1ul
