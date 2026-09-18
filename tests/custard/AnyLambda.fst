module AnyLambda

(* Section 126.6.  Two coercion failures that only appear together, and only
   in a program whose types are computed by a type-level [match].

   [arg_type] is such a match, so Custard works a binder of that type out to
   exactly [TAny] --- not to a compound type that happens to contain one.  A
   lambda binder is not printed, so nothing in the output tells the target
   what it is, and a use of it that is not coerced lets the target infer a
   type from one [match] branch that the next branch contradicts.

   [go]'s result type is computed too, so a call that supplies an argument for
   a computed arrow over-applies a head whose type peels to fewer arrows than
   there are arguments, with a [TAny] where the rest should be. *)

type arg = | B | I

type dir = | Lit | Arg of arg

let arg_type (a:arg) : Tot Type0 =
  match a with
  | B -> bool
  | I -> int

let rec dir_type (ds:list dir) : Tot Type0 =
  match ds with
  | [] -> string
  | Lit :: ds' -> dir_type ds'
  | Arg a :: ds' -> arg_type a -> Tot (dir_type ds')

(* The lambda's binder is the [TAny]; the two branches of the inner match
   would give it two different types if neither use were coerced. *)
let rec go (ds:list dir) (k:string -> Tot string) : dir_type ds =
  match ds with
  | [] -> k ""
  | Lit :: ds' -> go ds' k <: normalize_term (dir_type ds')
  | Arg a :: ds' ->
    fun (x : arg_type a) ->
      go ds' (fun res ->
        (match a with | B -> string_of_bool x | I -> string_of_int x) ^ res)

(* Applied where the expected type is known... *)
let direct () : Tot string = go [Arg I] (fun s -> s) 42

(* ...and where it is not, which is the case that needs the head coerced. *)
let bound () : Tot string =
  let s = go [Arg B] (fun s -> s) true in
  s

let main () : FStar.All.ML unit =
  FStar.IO.print_string (direct () ^ " " ^ bound () ^ "\n")
