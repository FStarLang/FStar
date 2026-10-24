module CLetField
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

(* FStarLang/FStar#4630: a match on a constructor whose *nested* field is
   under a [let].  The binding hides the inner constructor from iota, so the
   whole tuple used to be built as a struct and read back out.  Floating the
   binding out in front of the match lets iota fire. *)
let f (x : U32.t) : U32.t =
  match (x, (let y = U32.div x 2ul in (y, y))) with
  | (a, (b, c)) -> U32.add_mod a (U32.add_mod b c)

(* The shape a recursive index builder leaves after inlining: every level a
   pair of bindings in front of the next pair, ending in [unit]. *)
inline_for_extraction noextract
let split (n : U32.t{U32.v n <> 0}) (i : U32.t) : U32.t & (U32.t & (U32.t & unit)) =
  let major = U32.div i n in
  let minor = U32.rem i n in
  (major, (let mm = U32.div minor 2ul in let ml = U32.rem minor 2ul in (mm, (ml, ()))))

let g (i : U32.t) : U32.t =
  match split 8ul i with
  | (a, (b, (c, ()))) -> U32.add_mod (U32.mul_mod a 8ul) (U32.add_mod (U32.mul_mod b 2ul) c)

let main () : ML I32.t =
  if U32.eq (f 6ul) 12ul && U32.eq (g 21ul) 21ul then 0l else 1l
