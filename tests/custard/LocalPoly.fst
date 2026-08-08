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

let main () : ML unit =
  FStar.IO.print_string (ops 3);
  FStar.IO.print_string "\n"
