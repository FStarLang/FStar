(*
   Documentation on a module that has no interface, covering the cases
   the interface fixture cannot: a documented [let], a private
   declaration, and a [doc] payload that is well-typed but is not a
   string literal.
*)
module DocsNoIface

[@@doc ["Doubles 'x'.";
        "Documentation may also be attached to a definition in a module with";
        "no interface."]]
let double (x:int) : int = x + x

(* The empty list is documentation that says nothing. It is still a 'doc'
   attribute, so the declaration appears in the index, with no lines --
   which is different from having no attribute at all, like 'greeting'
   below. *)
[@@doc []]
let silent (x:int) : int = x

(* Documented, but private: not part of what the module exports, so not
   part of what is exported as documentation either. *)
[@@doc ["Private to the module, and so absent from the exported index."]]
private
let secret (x:int) : int = x

let greeting : string = "hello"

(* Well-typed -- 'doc' takes a list of strings and this is a list of
   strings -- but attributes are recorded in the checked module
   unnormalized, so what is stored is a list containing an unevaluated
   application, not a list of literals. The export warns (warning 278)
   and skips this declaration rather than inventing text for it. *)
[@@doc [greeting ^ ", world"]]
let shout (x:int) : int = x

(* The same, one level up: the list itself is not a literal list. *)
let lines : list string = ["a"; "b"]
[@@doc lines]
let murmur (x:int) : int = x
