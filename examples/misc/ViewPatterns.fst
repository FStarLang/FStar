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
           ((T (Tv_Const (C_Int n))) <- inspect_ln', _)
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
  | ((1::_) as hello) :: _ -> 0::hello
  | ((2::_) as hello) :: _ -> 1::hello
  | _ -> []
