module InlineLet
open FStar.HyperStack
open FStar.HyperStack.ST

noeq 
type pkg (a:Type) = 
  | Pkg : something: (a -> St (a * int))
        -> pkg a

inline_for_extraction
let pkg_something = function
    | Pkg s -> s

noeq 
type local_pkg (a:Type) = 
  | LocalPkg : local_something: (a -> St int)
        -> local_pkg a

inline_for_extraction
let local_something = function
  | LocalPkg s -> s

inline_for_extraction
let pkg_of_local_pkg #a (r:ref a) (lp:local_pkg a) =
  [@inline_let]
  let wrapper (x:a) =
      let v = !r in
      r := x;
      let b = local_something lp x in
      v, b
  in
  Pkg wrapper

assume val some_stateful_operation: int -> St int

inline_for_extraction
let ideal = false

inline_for_extraction
let maybe_ideal_op (i:int) =
    if ideal
    then some_stateful_operation i
    else i + 1

let test (r:rid) (x:bool) =
  let r : ref int = FStar.HyperStack.ST.ralloc r 0 in
  [@inline_let]
  let pkg = pkg_of_local_pkg r (LocalPkg maybe_ideal_op) in
  pkg_something pkg 16
