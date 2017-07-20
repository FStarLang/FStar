module SimplePrintf

open FStar.Char
open FStar.String

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

(* Below we write parse_format returning option
   (see SimplePrintfReify for more interesting version) *)

type hoption (a:Type) : Type = | Nothing : hoption a | Just : v:a -> hoption a

unfold
let just (#a:Type) (x:hoption a{Just? x}) = match x with Just y -> y

let add_dir (d:dir) (ods : hoption (list dir)) : Tot (hoption (list dir)) =
  match ods with
  | Nothing -> Nothing
  | Just ds -> Just (d::ds)

let rec parse_format_pure (s:list char) : Tot (hoption (list dir)) =
  match s with
  | [] -> Just []
  | '%' :: c :: s' -> (match c with
                      | '%' -> add_dir (Lit '%') (parse_format_pure s')
                      | 'b' -> add_dir (Arg Bool) (parse_format_pure s')
                      | 'd' -> add_dir (Arg Int) (parse_format_pure s')
                      | 'c' -> add_dir (Arg Char) (parse_format_pure s')
                      | 's' -> add_dir (Arg String) (parse_format_pure s')
                      | _   -> Nothing)
  | '%' :: [] -> Nothing
  | c :: s' -> add_dir (Lit c) (parse_format_pure s')

let rec parse_format_string (s:string) : Tot (hoption (list dir)) =
  parse_format_pure (list_of_string s)


let valid_string : Type0 = s:string{Just? (parse_format_string s)}

let sprintf (#a:Type) (s:string)
  : Pure a (requires (Just? (normalize_term (parse_format_string s)) /\ a == normalize_term (dir_type (just (parse_format_string s))))) (ensures (fun _ -> True)) =
  string_of_dirs (just (parse_format_string s)) (fun s -> s)

(* trying to make sure that it's not the SMT solver doing the reduction *)
#reset-options "--initial_fuel 0 --max_fuel 0"

let example2 () =
  assert_norm (list_of_string "%d=%s" == ['%'; 'd'; '='; '%'; 's'])

(* Can use assert_norm above to prove a lemma that F* cannot prove on its own *)
let example2_lemma () :
  Lemma (list_of_string "%d=%s" == ['%'; 'd'; '='; '%'; 's']) =
    assert_norm (list_of_string "%d=%s" == ['%'; 'd'; '='; '%'; 's'])

(* It might seem nicer to just call normalize in the lemma statement,
   but that doesn't allow using the lemma later on; so we're stuck with the duplication *)
private let example2_lemma_looks_nicer_but_not_usable () :
  Lemma (normalize_term (list_of_string "%d=%s" == ['%'; 'd'; '='; '%'; 's'])) = ()
(* This also needs the private qualifier, otherwise getting this:
Interface of SimplePrintf violates its abstraction (add a 'private'
qualifier to
'SimplePrintf.example2_lemma_looks_nicer_but_not_usable'?): Expected
expression of type "(Prims.list (?50858 uu___))"; got expression "%"
of type "FStar.Char.char" *)

let example3_lemma () :
  Lemma (parse_format_pure ['%'; 'd'; '='; '%'; 's']
         == Just [Arg Int; Lit '='; Arg String]) =
  assert_norm (parse_format_pure ['%'; 'd'; '='; '%'; 's']
               == Just [Arg Int; Lit '='; Arg String])

let example4_lemma () :
  Lemma (parse_format_string "%d=%s" == Just [Arg Int; Lit '='; Arg String]) =
  assert_norm (parse_format_string "%d=%s" == Just [Arg Int; Lit '='; Arg String])

// #reset-options "--z3timeout 10"

let id (#a #b:Type) (x:a) : Pure b (requires (a == b)) (ensures (fun _ -> True)) = x

let example5 : string =
  (* Requiring such an assert_norm on each usage seems quite bad for usability *)
  (* assert_norm (parse_format_string "%d=%s" == Just [Arg Int; Lit '='; Arg String]); *)
  (* assert ((int -> Tot (string -> Tot string)) == normalize_term (dir_type (just (parse_format_string "%d=%s")))) ; *)
  sprintf #(int -> Tot (string -> Tot string)) "%d=%s" 42 " answer"
  (* We also requires a pesky type annotation, but that seems more acceptable *)

(* A (so far failed) attempt at getting rid of assert_norm:
   - added normalize to the type of sprintf *)

(* Take 1: *)
(* let example6 : string = *)
(*   (sprintf "%d=%s" <: int -> string -> Tot string) 42 " answer" *)
(* ./SimplePrintf.fst(140,3-140,18): Subtyping check failed; expected type (uu___:Prims.int -> uu___:Prims.string -> Tot Prims.string); got type (((match (Prims.Just?.v (match (FStar.String.list_of_string "%d=%s") with *)
(* 	| (Prims.Nil #.uu___#12770)  -> (Prims.Just (Prims.Nil )) *)
(* 	|(Prims.Cons #.uu___#12974 % (Prims.Cons #.uu___#12970 c#39352 s'#39353))  -> ((match c@1 with *)
(* 	| %  -> (SimplePrintf.add_dir (SimplePrintf.Lit %) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|b  -> (SimplePrintf.add_dir (SimplePrintf.Arg SimplePrintf.Bool) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|d  -> (SimplePrintf.add_dir (SimplePrintf.Arg SimplePrintf.Int) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|c  -> (SimplePrintf.add_dir (SimplePrintf.Arg SimplePrintf.Char) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|s  -> (SimplePrintf.add_dir (SimplePrintf.Arg SimplePrintf.String) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|_  -> (Prims.Nothing )) : (Prims.hoption (Prims.list SimplePrintf.dir))) *)
(* 	|(Prims.Cons #.uu___#14938 % (Prims.Nil #.uu___#14934))  -> (Prims.Nothing ) *)
(* 	|(Prims.Cons #.uu___#15706 c#39355 s'#39356)  -> (SimplePrintf.add_dir (SimplePrintf.Lit c@1) (SimplePrintf.parse_format_pure s'@0)))) with *)
(* 	| (Prims.Nil #.uu___#1757)  -> Prims.string *)
(* 	|(Prims.Cons #.uu___#1919 (SimplePrintf.Lit c#39357) ds'#39358)  -> (SimplePrintf.dir_type ds'@0) *)
(* 	|(Prims.Cons #.uu___#2414 (SimplePrintf.Arg a#39359) ds'#39360)  -> (uu___:(SimplePrintf.arg_type a@1) -> Tot (SimplePrintf.dir_type ds'@1))) : Type) : Type) *)

(* Take 2: without the type annotation error message gets even more horrible *)
(* let example6 : string = *)
(*   sprintf "%d=%s" 42 " answer" *)
(* ./SimplePrintf.fst(162,18-162,20) : Error *)
(* Too many arguments to function of type (s:(s#17162:Prims.string{(Prims.eq2 (Prims.Just? (match (FStar.String.list_of_string s@0) with *)
(* 	| (Prims.Nil #.uu___#12770)  -> (Prims.Just (Prims.Nil )) *)
(* 	|(Prims.Cons #.uu___#12974 % (Prims.Cons #.uu___#12970 c#38766 s'#38767))  -> ((match c@1 with *)
(* 	| %  -> (SimplePrintf.add_dir (SimplePrintf.Lit %) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|b  -> (SimplePrintf.add_dir (SimplePrintf.Arg SimplePrintf.Bool) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|d  -> (SimplePrintf.add_dir (SimplePrintf.Arg SimplePrintf.Int) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|c  -> (SimplePrintf.add_dir (SimplePrintf.Arg SimplePrintf.Char) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|s  -> (SimplePrintf.add_dir (SimplePrintf.Arg SimplePrintf.String) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|_  -> (Prims.Nothing )) : (Prims.hoption (Prims.list SimplePrintf.dir))) *)
(* 	|(Prims.Cons #.uu___#14938 % (Prims.Nil #.uu___#14934))  -> (Prims.Nothing ) *)
(* 	|(Prims.Cons #.uu___#15706 c#38769 s'#38770)  -> (SimplePrintf.add_dir (SimplePrintf.Lit c@1) (SimplePrintf.parse_format_pure s'@0)))) true)}) -> Tot (((match (Prims.Just?.v (match (FStar.String.list_of_string s@0) with *)
(* 	| (Prims.Nil #.uu___#12770)  -> (Prims.Just (Prims.Nil )) *)
(* 	|(Prims.Cons #.uu___#12974 % (Prims.Cons #.uu___#12970 c#38755 s'#38756))  -> ((match c@1 with *)
(* 	| %  -> (SimplePrintf.add_dir (SimplePrintf.Lit %) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|b  -> (SimplePrintf.add_dir (SimplePrintf.Arg SimplePrintf.Bool) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|d  -> (SimplePrintf.add_dir (SimplePrintf.Arg SimplePrintf.Int) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|c  -> (SimplePrintf.add_dir (SimplePrintf.Arg SimplePrintf.Char) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|s  -> (SimplePrintf.add_dir (SimplePrintf.Arg SimplePrintf.String) (SimplePrintf.parse_format_pure s'@0)) *)
(* 	|_  -> (Prims.Nothing )) : (Prims.hoption (Prims.list SimplePrintf.dir))) *)
(* 	|(Prims.Cons #.uu___#14938 % (Prims.Nil #.uu___#14934))  -> (Prims.Nothing ) *)
(* 	|(Prims.Cons #.uu___#15706 c#38758 s'#38759)  -> (SimplePrintf.add_dir (SimplePrintf.Lit c@1) (SimplePrintf.parse_format_pure s'@0)))) with *)
(* 	| (Prims.Nil #.uu___#1757)  -> Prims.string *)
(* 	|(Prims.Cons #.uu___#1919 (SimplePrintf.Lit c#38760) ds'#38761)  -> (SimplePrintf.dir_type ds'@0) *)
(* 	|(Prims.Cons #.uu___#2414 (SimplePrintf.Arg a#38762) ds'#38763)  -> (uu___:(SimplePrintf.arg_type a@1) -> Tot (SimplePrintf.dir_type ds'@1))) : Type) : Type)); got 3 arguments *)
