module Macro

open FStar.Attributes

(* Section 68.  A protocol constant is exported as a preprocessor [#define],
   not as a variable, so that a caller can use it where C requires a constant
   expression: a [case] label, an initializer for an object with static
   storage duration, and [#if]. *)

[@@ CMacro ]
let major_type_uint64 : UInt8.t = 0uy

[@@ CMacro ]
let major_type_text_string : UInt8.t = 3uy

[@@ CMacro ]
let max_simple_value : UInt8.t = 23uy

(* Private, so it is a macro in the source rather than in the header. *)
[@@ CMacro ]
private
let internal_limit : UInt32.t = 65535ul

(* The three uses the attribute exists for.  A [case] label and a static
   initializer are both constant expressions; a variable is neither. *)
let classify (x : UInt8.t) : UInt32.t =
  match x with
  | 0uy -> 10ul
  | 3uy -> 20ul
  | _ -> 30ul

let table : UInt8.t = max_simple_value

let main () : FStar.All.ML Int32.t =
  let _ = classify major_type_uint64 in
  let _ = classify major_type_text_string in
  let _ = table in
  let _ = internal_limit in
  0l
