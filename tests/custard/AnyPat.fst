module AnyPat

open FStar.All

(* Section 125.8 and 125.9.  Three ways a value whose type is [any] reaches a
   position that needs a real one.  Each is a legacy bug report, and each
   produced OCaml that did not compile. *)

(* {1 A match whose branches disagree (section 125.8)}

   [arg_type] returns a different type in each branch, so the match node has
   no type of its own.  Taking the first branch's made [def_value]'s declared
   return type [bool], and [def_value Fun] was then applied to an argument
   that the signature said was not there. *)

type dir = | DBool | DInt | DFun

let arg_type (d:dir) : Tot Type0 =
  match d with
  | DBool -> bool
  | DInt -> int
  | DFun -> int -> Tot int

let def_value (d:dir) : Tot (arg_type d) =
  match d with
  | DBool -> true
  | DInt -> 42
  | DFun -> (fun (x:int) -> x + 1)

let use_bool : bool = def_value DBool
let use_int : int = def_value DInt
let use_fun : int = def_value DFun 41

(* {1 A constant pattern as evidence about the scrutinee (section 125.8)}

   [choose A] is eta-expanded, and the coercion pass reads a match's
   scrutinee type off the patterns.  It consulted constructor and record
   patterns only, so a match on integer literals left the scrutinee at [any]
   and the coercion that the application needed was never inserted. *)

type tag = | TA | TB

let dec : tag -> Type0 = function
  | TA -> int
  | TB -> bool

let fun_a (x:int) (s:int) : int = x
let fun_b (x:bool) (s:int) : bool = x

let choose : a:tag -> dec a -> int -> dec a = function
  | TA -> fun_a
  | TB -> fun_b

(* 2 rather than 0 here is the eta-expansion shadowing its own binder. *)
let const_pat : int =
  match choose TA 0 2 with
  | 0 -> 0
  | n -> n

(* {1 A structured pattern under an [any] field (section 125.9)}

   The second component of the dependent pair is [any], and a coercion cannot
   be inserted inside a pattern.  Section 115 already splits such a
   sub-pattern into an inner match, but it read the field's *declared* type,
   which for [dtuple2] is a type variable and never [any]; the answer is in
   the scrutinee's own type, [(bool, any) dtuple2]. *)

noeq
type pair_result =
  | PStrings : string -> string -> pair_result
  | PNats : nat -> nat -> pair_result

let split_tuple (x:(b:bool & (if b then (nat & nat) else (string & string))))
  : pair_result
  = match x with
    | (|false, (y, z)|) -> PStrings y z
    | (|true, (y, z)|) -> PNats y z

noeq
type boxed (a:Type) = | Boxed : a -> int -> boxed a

noeq
type boxed_result =
  | BString : string -> int -> boxed_result
  | BNat : nat -> int -> boxed_result

let split_ctor (x:(b:bool & (if b then boxed string else boxed nat)))
  : boxed_result
  = match x with
    | (|true, Boxed s z|) -> BString s z
    | (|false, Boxed n z|) -> BNat n z

(* A concrete field type takes the path it always did: no split, no inner
   match, no coercion. *)
let no_split (x:(b:bool & (nat & y:int{b ==> y > 17}))) : pair_result =
  match x with
  | (|true, (z, _)|) -> PNats z z
  | (|false, (z, _)|) -> PNats z z

let show_pair (r:pair_result) : string =
  match r with
  | PStrings a b -> "strings " ^ a ^ " " ^ b
  | PNats a b -> "nats " ^ string_of_int a ^ " " ^ string_of_int b

let show_boxed (r:boxed_result) : string =
  match r with
  | BString s z -> "string " ^ s ^ " " ^ string_of_int z
  | BNat n z -> "nat " ^ string_of_int n ^ " " ^ string_of_int z

let line (s:string) : ML unit =
  FStar.IO.print_string s; FStar.IO.print_string "\n"

let main () : ML unit =
  line (string_of_bool use_bool);
  line (string_of_int use_int);
  line (string_of_int use_fun);
  line (string_of_int const_pat);
  line (show_pair (split_tuple (|false, ("a", "b")|)));
  line (show_pair (split_tuple (|true, (1, 2)|)));
  line (show_boxed (split_ctor (|true, Boxed "s" 3|)));
  line (show_boxed (split_ctor (|false, Boxed 4 5|)));
  line (show_pair (no_split (|true, (6, 18)|)))
