module Fail

[@ fail]
let _ = 1 + 'a'

[@ (fail [189])]
let _ = 1 + 'a'

[@ fail]
let _ = assert False

[@ (fail [19])]
let _ = assert False

(* Now for interaction with --lax *)
#set-options "--lax"

(* These are ignored, since we're laxing and using the ordinary `fail` *)
[@fail]
let _ = assert False
[@fail]
let _ = assert True

(* We can use fail_lax to ask for a lax-checking failure *)
[@fail_lax]
let _ = 1 + 'a'

(* These two would fail, since they lax-check correctly *)
//[@fail_lax]
//let _ = assert False
//
//[@fail_lax]
//let _ = assert True

(* We can also specify the expected errors *)
[@ fail_lax (fail [189])]
let _ = 1 + 'a'
