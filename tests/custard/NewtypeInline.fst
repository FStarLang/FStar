module NewtypeInline
open FStar.All

(* A single-constructor, single-field type whose field is a tuple, so the
   field is marked inline (section 5.7).  Newtype collapse (section 5.2) gets
   there first: [step] simply *is* the pair.  The inline marker has no
   constructor left to inline into and must not survive into the collapsed
   representation, where nothing would ever take it away again. *)
type step = | Step of bool & string

let snd_of (s: step) : string =
  match s with
  | Step (_, x) -> x

(* The collapsed representation as a type argument and as a binder type: the
   two positions the escaping marker used to reach. *)
let first (l: list step) : string =
  match l with
  | s :: _ -> snd_of s
  | [] -> "none"

let main () : ML unit =
  FStar.IO.print_string (first [Step (true, "ok")]);
  FStar.IO.print_string "\n"
