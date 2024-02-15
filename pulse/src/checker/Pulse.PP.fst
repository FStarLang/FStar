(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

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
let text (s:string) : FStar.Stubs.Pprint.document =
  flow (break_ 1) (words s)

(* Nests a document 2 levels deep, as a block. It inserts a hardline
before the doc, so if you want to format something as

  hdr
    subdoc
  tail

  you should write  hdr ^^ indent (subdoc) ^/^ tail.  Note the ^^ vs ^/^.
*)
let indent d =
  nest 2 (hardline ^^ align d)

(* Repurposing a show instance *)
let from_show #a {| d : tac_showable a |} : printable a = {
  pp = (fun x -> arbitrary_string (show x));
}

instance printable_string : printable string = from_show
instance printable_unit   : printable unit   = from_show
instance printable_bool   : printable bool   = from_show
instance printable_int    : printable int    = from_show

instance printable_ctag : printable ctag = from_show

instance printable_option (a:Type) (_ : printable a) : printable (option a) = {
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

instance printable_list (a:Type) (_ : printable a) : printable (list a) = {
  pp = (fun l -> brackets (separate_map comma pp l))
}

instance printable_term     : printable term = from_show
instance printable_universe : printable universe = from_show
instance printable_comp     : printable comp = from_show

instance printable_env : printable env = {
  pp = Pulse.Typing.Env.env_to_doc;
}

instance pp_effect_annot : printable effect_annot = from_show

let pp_record (flds : list (string & document)) : Tac document =
  let flds_doc =
    separate_map (doc_of_string ";") (fun (s, d) -> group (doc_of_string s ^/^ equals ^/^ group d)) flds
  in
  braces (align flds_doc)

instance printable_post_hint_t : printable post_hint_t = {
  pp = (fun (h:post_hint_t) ->
          pp_record [ "g", pp h.g
                    ; "effect_annot", pp h.effect_annot
                    ; "ret_ty", pp h.ret_ty
                    ; "u", pp h.u
                    ; "post", pp h.post ]);
}

// FIXME: use term_to_doc when available
instance printable_fstar_term : printable Reflection.V2.term = {
  pp = (fun t -> doc_of_string (Tactics.V2.term_to_string t))
}

instance printable_tuple2 (a b:Type)
          (_:printable a) (_:printable b) : printable (a * b) = {
    pp = (fun (x, y) -> parens (separate comma [pp x; pp y]));
  }
  
instance printable_tuple3 (a b c:Type)
          (_:printable a) (_:printable b) (_:printable c) : printable (a * b * c) = {
    pp = (fun (x, y, z) -> parens (separate comma [pp x; pp y; pp z]));
  }
  
instance printable_tuple4 (a b c d:Type)
          (_:printable a) (_:printable b) (_:printable c) (_:printable d) : printable (a * b * c * d) = {
    pp = (fun (x, y, z, w) -> parens (separate comma [pp x; pp y; pp z; pp w]));
  }
