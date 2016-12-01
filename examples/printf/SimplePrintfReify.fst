module SimplePrintfReify

open FStar.Char
open FStar.String

// A variant of SimplePrintf that uses reify on the Ex implementation
// of parse_format

// For a start here's an alpha renamed version of Ex to avoid clashes
// with the prims variant of Ex

(* The underlying representation type *)
let ex (a:Type) = unit -> M (option a)

(* Monad definition *)
val return_ex : (a:Type) -> (x:a) -> Tot (ex a)
let return_ex a x = fun _ -> Some x

val bind_ex : (a:Type) -> (b:Type) -> (f:ex a) -> (g:a -> Tot (ex b)) -> Tot (ex b)
let bind_ex a b f g = fun _ ->
  let r = f () in
  match r with
  | None -> None
  | Some x -> g x ()

let raise_ex (a:Type) (e:exn) : Tot (ex a) = fun _ -> None

(* Define the new effect using DM4F *)
reifiable reflectable new_effect_for_free {
  XEXN : (a:Type) -> Effect
  with repr     = ex
     ; bind     = bind_ex
     ; return   = return_ex
  and effect_actions
       raise   = raise_ex
}

(* A lift from `Pure´ into the new effect *)
unfold let lift_pure_ex_wp (a:Type) (wp:pure_wp a) (_:unit) (p:XEXN.post a) =
  wp (fun a -> p (Some a))
sub_effect PURE ~> XEXN = lift_pure_ex_wp

(* TODO: this should work but Pure is not reifiable *)
(* sub_effect PURE ~> XEXN { *)
(*   lift_wp = lift_pure_ex_wp; *)
(*   lift = return_ex *)
(* } *)

(* An effect to alias easily write pre- and postconditions *)
(* Note: we use Type0 instead of XEXN.pre to avoid having to thunk everything. *)
effect Xexn (a:Type) (pre:Type0) (post:XEXN.post a) =
  XEXN a (fun (_:unit) (p:XEXN.post a) -> pre /\
          (forall (r:option a). (pre /\ post r) ==> p r))

(* Another alias. Ex a is the effect type for total exception-throwing
 * programs. i.e. Any program of type `Ex a´ will throw or finish
 * correctly, but never loop. *)
effect Xex (a:Type) = XEXN a (fun _ p -> forall (x:option a). p x)

// arguments to printf
type arg =
| Bool | Int | Char | String

// directives to printf
type dir =
| Lit : char -> dir
| Arg : arg  -> dir

let arg_type (a:arg) : Tot Type0 =
  match a with
  | Bool   -> bool
  | Int    -> int
  | Char   -> char
  | String -> string

let rec dir_type (ds:list dir) : Tot Type0 =
  match ds with
  | [] -> string
  | Lit c :: ds' -> dir_type ds'
  | Arg a :: ds' -> arg_type a -> Tot (dir_type ds')

let dir_type' ds = dir_type ds

let rec string_of_dirs ds (k:string -> Tot string) : Tot (dir_type ds) =
  match ds with
  | [] -> k ""
  | Lit c :: ds' -> 
    (string_of_dirs ds' (fun res -> k (string_of_char c ^ res))
     <: dir_type' ds' //this is an ugly workaround for #606
    )
  | Arg a :: ds' -> fun (x : arg_type a) ->
      string_of_dirs ds' (fun res -> k (match a with
                                        | Bool -> string_of_bool x
                                        | Int -> string_of_int x
                                        | Char -> string_of_char x
                                        | String -> x) ^ res)

let example1 : string =
  string_of_dirs [Arg Int; Arg String] (fun s -> s) 42 " answer"

(* TODO: This fails to extract:
./SimplePrintf.fst(45,2-45,64): Ill-typed application: application is (SimplePrintf.string_of_dirs (Prims.Cons (SimplePrintf.Arg SimplePrintf.Int) (Prims.Cons (SimplePrintf.Arg SimplePrintf.String) (Prims.Nil ))) (fun s -> s@0) 42 " answer") 
 remaining args are 42 " answer"
ml type of head is Prims.unit dir_type
*)

exception InvalidFormatString

(* reifiable let my_return (#a:Type) (x:a) : Xex a = *)
(*   XEXN.reflect (return_ex a x) *)

reifiable let rec parse_format (s:list char) : Xex (list dir) =
  match s with
  | [] -> []
  | '%' :: c :: s' ->
    let d = match c with
            | '%' -> Lit '%'
            | 'b' -> Arg Bool
            | 'd' -> Arg Int
            | 'c' -> Arg Char
            | 's' -> Arg String
            | _   -> XEXN.raise dir InvalidFormatString
    in d :: parse_format s'
  | '%' :: [] -> XEXN.raise (list dir) InvalidFormatString
  | c :: s' -> Lit c :: parse_format s'

let parse_format_pure (s:list char) : option (list dir) =
  reify (parse_format s) ()

(* let rec parse_format_string (s:string) : Tot (option (list dir)) = *)
(*   parse_format_pure (list_of_string s) *)

(* let sprintf (s:string{Some? (parse_format_string s)}) *)
(*   : Tot (dir_type (Some.v (parse_format_string s))) = *)
(*   string_of_dirs (Some.v (parse_format_string s)) (fun s -> s) *)

(* let example2 () = *)
(*   assert_norm (list_of_string "%d=%s" == ['%'; 'd'; '='; '%'; 's']) *)

(* (\* Can use assert_norm above to prove a lemma that F* cannot prove on its own *\) *)
(* let example2_lemma () : *)
(*   Lemma (list_of_string "%d=%s" == ['%'; 'd'; '='; '%'; 's']) = *)
(*     assert_norm (list_of_string "%d=%s" == ['%'; 'd'; '='; '%'; 's']) *)

(* (\* It might seem nicer to just call normalize in the lemma statement, *)
(*    but that doesn't allow using the lemma later on; *)
(*    so we're stuck with the duplication *\) *)
(* private let example2_lemma_looks_nicer_but_not_usable () : *)
(*   Lemma (normalize (list_of_string "%d=%s" == ['%'; 'd'; '='; '%'; 's'])) = () *)
(* (\* This also needs the private qualifier, otherwise getting this: *)
(* Interface of SimplePrintf violates its abstraction (add a 'private' *)
(* qualifier to *)
(* 'SimplePrintf.example2_lemma_looks_nicer_but_not_usable'?): Expected *)
(* expression of type "(Prims.list (?50858 uu___))"; got expression "%" *)
(* of type "FStar.Char.char" *\) *)

(* Doesn't work; why does reify-action not trigger?
   plus same problem with lift PURE->EXN as below *)
let example_error_lemma () :
  Lemma (parse_format_pure ['%'] == None) =
  assert_norm (parse_format_pure ['%'] == None)

(* Doesn't work; seems it's because missing lift PURE->EXN at
   expression level; tried to write that lift above but didn't manage
   because pure is not marked as reifiable -- dm4f compiler should
   automatically produce this lift *)
let example3_lemma () :
  Lemma (parse_format_pure ['%'; 'd'; '='; '%'; 's']
         == Some [Arg Int; Lit '='; Arg String]) =
  assert_norm (parse_format_pure ['%'; 'd'; '='; '%'; 's']
               == Some [Arg Int; Lit '='; Arg String])

(* let example4_lemma () : *)
(*   Lemma (parse_format_string "%d=%s" == Some [Arg Int; Lit '='; Arg String]) = *)
(*   assert_norm (parse_format_string "%d=%s" == Some [Arg Int; Lit '='; Arg String]) *)

(* let example5 : string = *)
(*   (\* Requiring such an assert_norm on each usage seems quite bad for usability *\) *)
(*   assert_norm (parse_format_string "%d=%s" == Some [Arg Int; Lit '='; Arg String]); *)
(*   (sprintf "%d=%s" <: int -> string -> Tot string) 42 " answer" *)
(*   (\* We also requires a pesky type annotation, but that seems more acceptable *\) *)
