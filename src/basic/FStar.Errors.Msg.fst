module FStar.Errors.Msg

open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.Util
open FStar.Pprint

let vconcat (ds:list document) : document =
  match ds with
  | h::t ->
    List.fold_left (fun l r -> l ^^ hardline ^^ r) h t
  | [] ->
    empty

let text (s:string) : document =
  flow (break_ 1) (words s)

let sublist (h:document) (ds:list document) : document =
  nest 2 (hardline ^^ align (ds |> List.map (fun d -> h ^^ d) |> vconcat))

let bulleted (ds:list document) : document =
  sublist (doc_of_string "- ") ds

let mkmsg (s:string) : list document =
  [arbitrary_string s]

let renderdoc (d : document) : string =
  let one = float_of_string "1.0" in
  pretty_string one 80 d

let backtrace_doc () : document =
  let s = stack_dump () in
  text "Stack trace:" ^/^
  arbitrary_string s

let subdoc d =
  (* NOTE: slight hack here, using equality on Pprint documents. This works
  fine, particularly for this case, since empty is just a constructor Empty.
  There is even a new function to check if a document is empty, added two weeks ago!
    https://github.com/fpottier/pprint/commit/afecb1a6a2751648f62147660ea8fee7a2dee054
  So I don't expect this to fail any time soon, and when it does we could just
  switch to using that function. (I won't right now as it is not released). *)
  if d = empty
  then empty
  else blank 2 ^^ doc_of_string "-" ^^ blank 1 ^^ align d ^^ hardline

let rendermsg (ds : list document) : string =
  renderdoc (concat (List.map (fun d -> subdoc (group d)) ds))
