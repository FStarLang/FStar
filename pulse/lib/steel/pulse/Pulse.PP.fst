module Pulse.PP

include FStar.Stubs.Pprint

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Stubs.Pprint
open Pulse.Typing
open Pulse.Syntax.Base
open Pulse.Syntax.Printer

open Pulse.Show

(* A helper to create wrapped text *)
val text : string -> FStar.Stubs.Pprint.document
let text (s:string) : FStar.Stubs.Pprint.document =
  flow (break_ 1) (words s)

(* Nests a document 2 levels deep, as a block. It inserts a hardline
before the doc, so if you want to format something as

  hdr
    subdoc
  tail

  you should write  hdr ^^ indent (subdoc) ^/^ tail.  Note the ^^ vs ^/^.
*)
val indent : document -> document
let indent d =
  nest 2 (hardline ^^ align d)

class printable (a:Type) = {
  pp : a -> Tac document;
}

(* Repurposing a show instance *)
let from_show #a {| d : tac_showable a |} : printable a = {
  pp = (fun x -> arbitrary_string (show x));
}

instance _ : printable string = from_show
instance _ : printable unit   = from_show
instance _ : printable bool   = from_show
instance _ : printable int    = from_show

instance _ : printable ctag = from_show

instance showable_option (a:Type) (_ : printable a) : printable (option a) = {
  pp = (function None -> doc_of_string "None"
                 | Some v -> doc_of_string "Some" ^/^ pp v);
}

// Cannot use Pprint.separate_map, it takes a pure func
private
let rec separate_map (sep: document) (f : 'a -> Tac document) (l : list 'a) : Tac document =
  match l with
  | [] -> empty
  | [x] -> f x
  | x::xs -> f x ^^ sep ^/^ separate_map sep f xs

instance showable_list (a:Type) (_ : printable a) : printable (list a) = {
  pp = (fun l -> brackets (separate_map comma pp l))
}

instance _ : printable term = from_show
instance _ : printable universe = from_show
instance _ : printable comp = from_show

instance _ : printable env = {
  pp = Pulse.Typing.Env.env_to_doc;
}

let pp_record (flds : list (string & document)) : Tac document =
  braces (
    separate_map (doc_of_string ";") (fun (s, d) -> doc_of_string s ^/^ equals ^/^ d) flds)

instance _ : printable post_hint_t = {
  pp = (fun (h:post_hint_t) ->
          pp_record [ "g", pp h.g
                    ; "ctag_hint", pp h.ctag_hint
                    ; "ret_ty", pp h.ret_ty
                    ; "u", pp h.u
                    ; "post", pp h.post ]);
}
