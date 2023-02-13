module Parsing

open FStar.Tactics
open FStar.Reflection
open FStar.Reflection.Builtins

let term_to_string_to_term (value: 'a): Tac unit
  = let t: term = quote value in
    let s: string = term_to_string t in
    print ("[original term] '" ^ s ^ "'");
    let t': term = string_to_term (top_env ()) (term_to_string t) in
    print ("[produced term] '" ^ term_to_string t' ^ "'");
    exact t'

let equals (#t: Type) (v: t) (#[term_to_string_to_term #t v] v': t) (): Type0
  = v == v'

let _ = assert (equals 42 ())

let _ = assert (equals (unit * unit) ())
let _ = assert (equals (unit * (unit * unit)) ())
let _ = assert (equals ((unit * unit) * unit) ())

let _ = assert (equals (fun x -> x + 3) ())

[@expect_failure] // as issue #2245
let _ = assert (equals (unit * unit * unit) ())

[@expect_failure] // as issue #1865
let _ = assert (equals (forall (x: (y: int{y>0})). True) ())

[@expect_failure] // as PR #2186
let _ = assert (equals (fun (#_: int) -> 0) ())
[@expect_failure]
let _ = assert (equals (fun x (#y: int) -> x + 3) ())

#push-options "--print_implicits"
let _ = assert (equals (fun (#_: int) -> 0) ())
let _ = assert (equals (fun x #y -> x + y) ())
let _ = assert (equals (fun x (#y: int) -> x + 3) ())
#pop-options
