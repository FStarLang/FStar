module LocalPoly
open FStar.All

class emb (a:Type) = { un : int -> ML (option a) }

val try_unembed : {| emb 'a |} -> int -> ML (option 'a)
let try_unembed #a {| d : emb a |} (x:int) : ML (option a) = un x

instance e_int : emb int = { un = (fun x -> Some x) }
instance e_bool : emb bool = { un = (fun x -> Some (x > 0)) }

(* Exactly the FStarC.TypeChecker.Primops.Sealed.ops shape: a local helper
   that fixes some arguments of a specializing function and is used at
   several types. *)
let ops (n:int) : ML string =
  let tu (#a:Type) (e:emb a) (x:int) : ML (option a) = try_unembed #a #e x in
  match tu e_int n, tu e_bool n with
  | Some i, Some b -> string_of_int i ^ (if b then "t" else "f")
  | _ -> "none"

(* Monomorphic local helpers are *not* inlined.  Inlining them would be pure
   duplication -- they have no type argument to make concrete, which is the
   only thing inlining buys -- and because each is used twice and they nest,
   the cost is 2^n.  This shape is what made a real extraction run consume
   73GB; four levels here is enough for the .ml to give it away. *)
let nested (x:int) : ML int =
  let a (y:int) : ML int = y + x in
  let b (y:int) : ML int = a y + a (y + 1) in
  let c (y:int) : ML int = b y + b (y + 1) in
  let d (y:int) : ML int = c y + c (y + 1) in
  d 0 + d 1

let main () : ML unit =
  FStar.IO.print_string (ops 3);
  FStar.IO.print_string (string_of_int (nested 1));
  FStar.IO.print_string "\n"
