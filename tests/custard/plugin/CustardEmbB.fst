module CustardEmbB

(* Issue #4689, section 13.7.  The downstream unit, linked against
   CustardEmbA's: its plugin reuses the embedding CustardEmbA generated, and
   [plugin_embedding] names that embedding from F*.  See the Makefile. *)

open FStarC
open FStarC.Effect
open CustardEmbA
module EB = FStarC.Syntax.Embeddings.Base

[@@plugin]
irreducible
let paint (c:color) : color =
  match c with
  | Blue n -> Blue (n + 10)
  | _ -> Blue 0

let e_color : EB.embedding color = EB.plugin_embedding
let e_colors : EB.embedding (list color) = EB.plugin_embedding

let _ =
  let t = EB.extracted_embed e_colors [Red; Blue 3] in
  let back =
    match EB.extracted_unembed e_color (EB.extracted_embed e_color (Blue 7)) with
    | Some (Blue 7) -> "ok"
    | _ -> "bad" in
  FStarC.Format.print_string
    ("CustardEmbB: " ^ FStarC.Class.Show.show #_ #FStarC.Syntax.Print.showable_term t ^ " " ^ back ^ "\n")
