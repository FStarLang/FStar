module ViewPatterns

(*** Matching over terms *)
open FStar.Tactics

/// Sadly, seems like [term] to [term_view] automatic coercion kicks
/// wrongly in pattern views, for now I just wrap terms into [t] to
/// disable the coercion (since there's no subtyping on inductives)
type t 'a = | T of 'a
let inspect_ln': term -> t term_view = fun x -> T (inspect_ln x)

/// Small helper
let string_of_fv (f: fv): string = implode_qn (inspect_fv f)

/// [extract_foo_int_payload] expects a term [foo n] with [n] a
/// constant integer, and returns that [n]
let foo (x: int) = x
let extract_foo_int_payload t 
  = match inspect_ln t with
  | Tv_App ((T (Tv_FVar (`%foo <- string_of_fv))) <- inspect_ln')
           (T (Tv_Const (C_Int n)) <- inspect_ln', _)
      -> Some n
  | _ -> None

/// Works as expected
let _ = assert_norm (extract_foo_int_payload (`(foo 123)) == Some 123)

(*** matching integers, modulo *)
let mod6 (n:int) = n % 4
let plus1 (n:int) = match n with
                | 5 <- mod6 -> 0
                | n <- mod6 -> n + 1

let _ = assert_norm (plus1 12 == 1)

(*** [as] patterns *)
open FStar.List.Tot
let y = match [[1;2];[3]] with
  | ((1::_) as hello) :: _ -> 
    assert (List.Tot.length hello > 0);
    assert (List.Tot.hd hello == 1);
    0::hello
  | ((2::_) as hello) :: _ -> 1::hello
  | _ -> []
  
(*** [if] clauses *)
open FStar.List.Tot
let yy = match Some 1 with
  | Some (x if (x > 3)) -> x
  | Some x -> 3
  | _ -> 0

(*** disjunctive patterns *)
/// Say we want to sum the two integers of a list of length 3,
/// otherwise return 0
let disj0 (x: list (either int int)) = match x with
    | [Inl a; Inl b; Inl c] | [Inl a; Inl b; Inr c]
    | [Inl a; Inr b; Inl c] | [Inl a; Inr b; Inr c]
    | [Inr a; Inl b; Inl c] | [Inr a; Inl b; Inr c]
    | [Inr a; Inr b; Inl c] | [Inr a; Inr b; Inr c] -> a + b + c
    | _ -> 0

/// Easier with nested disjunctive patterns
let disj1 (x: list (either int int)) = match x with
    | [(Inl a | Inr a); (Inl b | Inr b); (Inl c | Inr c)] -> a + b + c
    | _ -> 0

/// [disj1] is desugared to [disj2]
let disj2 (x: list (either int int)) = match x with
    | [ (Some a) <- (function | Inl n | Inr n -> Some n | _ -> None)
      ; (Some b) <- (function | Inl n | Inr n -> Some n | _ -> None)
      ; (Some c) <- (function | Inl n | Inr n -> Some n | _ -> None)
      ] ->  a + b + c
    | _ -> 0

let disj_test = map (fun f -> f [Inl 10; Inr 30; Inr 2]) [disj0; disj1; disj2]
let _ = assert_norm (disj_test == [42; 42; 42])

(*** Match ends of lists *)

let splitAt_rev (#a:Type) (n:nat) (l:list a): list a * list a 
  = let n = length l - n in
    splitAt (if n > 0 then n else 0) l

let dotdot = match [10;2; 999; 888; 3;4] with
  | (Some ((a,b), middle, (c,d))) <- (fun (l: list int) -> 
         match l with
       | a::b::((middle, [c;d]) <- (splitAt_rev 2)) -> 
         Some ((a, b), [0], (c, d))
       | _ -> None
    ) -> a + b + c + d
  // we could easily have syntax like:
  // | [a;b; ...; c; d] -> a + b + c + d
  | _ -> 0

let _ = assert_norm (dotdot == 10 + 2 + 3 + 4)


(*** Match ranges *)

let range (a:int) (b:int): int -> bool = fun x -> x >= a && x <= b

let x y = match [y] with
  | [((true <- (range 0 4)) | (true <- (range 6 10))) as n] -> 
    n + 100
  // we could add the syntax:
  // | [(0..4 | 6..10) as n] -> n + 100
  | _ -> 1


(*** Pattern match on abstract types *)
assume type json
assume val json_null: json -> option unit
assume val json_bool: json -> option bool
assume val json_int: json -> option int
assume val json_string: json -> option string
assume val json_assoc: json -> option (list (string * json))
assume val json_list: json -> option (list json)
assume val exhaustiveness: x:json -> Lemma ( Some? (json_null  x) || Some? (json_bool   x)
                                          || Some? (json_int   x) || Some? (json_string x)
                                          || Some? (json_assoc x) || Some? (json_list   x) )

// Example without a view: building a view
noeq type json_view = | Null | String of string | Int of int | Bool of bool
                      | Assoc of list (string * json) | List of list json

let open_json (x: json): json_view = 
  match x with
  | (Some _) <- json_null   -> Null
  | (Some x) <- json_bool   -> Bool x
  | (Some x) <- json_int    -> Int x
  | (Some x) <- json_string -> String x
  | (Some x) <- json_assoc  -> Assoc x
  | (Some x) <- json_list   -> List x
  | _ -> exhaustiveness x;
        // that doesn't work for some reason
        magic ()

type vector2 = {x: int; y: int}

class has_view (a: Type) (b: Type) = {
  view: a -> b
}

instance view_json: has_view json json_view = {
  view = open_json
}

let parse_vector2 (x: json): vector2 =
  match x with
  | Assoc [ "x", Int x <-
          ; "y", Int y <-] <-
    -> {x; y}
  | _ -> {x = 0; y = 0}

