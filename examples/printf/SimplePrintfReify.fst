module SimplePrintfReify

open FStar.Char
open FStar.String
module List = FStar.List.Tot

// A variant of SimplePrintf that uses reify on the Ex implementation
// of parse_format

// For a start here's an alpha renamed version of Ex to avoid clashes
// with the prims variant of Ex (which is not defined using dm4free
// and is not marked as `total`)

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

(* DMFF does not support yet polymorphic actions *)
(* Returning something in [False] allow to derive the usual raise below *)
let raise_ex (_:exn) : Tot (ex False) = fun _ -> None

(* Define the new effect using DM4F *)
total reifiable reflectable new_effect {
  XEXN : (a:Type) -> Effect
  with repr     = ex
     ; bind     = bind_ex
     ; return   = return_ex
     ; raise   = raise_ex
}

(* A lift from `Pure´ into the new effect *)
(* unfold let lift_pure_ex_wp (a:Type) (wp:pure_wp a) (_:unit) (p:XEXN?.post a) = *)
(*   wp (fun a -> p (Some a)) *)
(* sub_effect PURE ~> XEXN = lift_pure_ex_wp *)

reifiable
let raise (#a:Type0) (e:exn) : XEXN a (fun _ p -> p None)
= let x = XEXN?.raise e in begin match x with end

(* An effect to alias easily write pre- and postconditions *)
(* Note: we use Type0 instead of XEXN.pre to avoid having to thunk everything. *)
effect Xexn (a:Type) (pre:Type0) (post:XEXN?.post a) =
  XEXN a (fun (_:unit) (p:XEXN?.post a) -> pre /\
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

exception InvalidFormatString

(* TODO: can we get rid of the two `let x` or are they really required? *)
reifiable let rec parse_format (s:list char) : Xex (list dir) =
  match s with
  | [] -> []
  | '%' :: c :: s' ->
    let d =
      match c with
      | '%' -> Lit '%'
      | 'b' -> Arg Bool
      | 'd' -> Arg Int
      | 'c' -> Arg Char
      | 's' -> Arg String
      | _   -> raise InvalidFormatString
    in let x = parse_format s' in d :: x
  | '%' :: [] -> raise InvalidFormatString
  | c :: s' -> let x = parse_format s' in Lit c :: x

let parse_format_pure (s:list char) : option (list dir) =
  reify (parse_format s) ()

let rec parse_format_string (s:string) : Tot (option (list dir)) =
  parse_format_pure (list_of_string s)

let sprintf (s:string{Some? (parse_format_string s)})
  : Tot (dir_type (Some?.v (parse_format_string s))) =
  string_of_dirs (Some?.v (parse_format_string s)) (fun s -> s)

let yyy = parse_format_pure ['%'] == None
let xxx = parse_format_pure ['%'; 'd'; '='; '%'; 's']

let example_error_lemma () :
  Lemma (parse_format_pure ['%'] == None) =
  ()
  (* Bad interaction with raise, results in a Failure("Impossible") *)
  (* assert_norm (parse_format_pure ['%'] == None) *)

let example3_lemma () :
  Lemma (parse_format_pure ['%'; 'd'; '='; '%'; 's']
         == Some [Arg Int; Lit '='; Arg String]) =
  assert_norm (parse_format_pure ['%'; 'd'; '='; '%'; 's']
               == Some [Arg Int; Lit '='; Arg String])

let example4_lemma () :
  Lemma (parse_format_string "%d=%s" == Some [Arg Int; Lit '='; Arg String]) =
  assert_norm (parse_format_string "%d=%s" == Some [Arg Int; Lit '='; Arg String])

let example5 : string =
  (* Requiring such an assert_norm on each usage seems quite bad for usability *)
  assert_norm (parse_format_string "%d=%s" == Some [Arg Int; Lit '='; Arg String]);
  (sprintf "%d=%s" <: int -> string -> Tot string) 42 " answer"
  (* We also requires a pesky type annotation, but that seems more acceptable *)

let rec concat_lemma (s1 s2 : list char) (l1 l2:list dir)
  : Lemma (requires (reify (parse_format s1) () = Some l1 /\ reify (parse_format s2) () = Some l2))
      (ensures (reify (parse_format (s1 @ s2)) () = Some (l1@l2)))
      (decreases s1)
= match s1 with
  | [] -> ()
  | ['%'] -> ()
  | '%' :: c :: s1' ->
    begin match c with
    | '%' | 'b' | 'd' | 'c' |'s' ->
      begin match l1 with
      | _ :: l1' -> concat_lemma s1' s2 l1' l2
      end
    | _ -> ()
    end
  | c :: s1' ->
    begin match l1 with
    | _ :: l1' -> concat_lemma s1' s2 l1' l2
    end


