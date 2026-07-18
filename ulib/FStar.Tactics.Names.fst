module FStar.Tactics.Names

open FStar.Tactics.NamedView
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Stubs.Reflection.V2.Builtins
module V = FStar.Tactics.Visit

exception Appears

(** Decides whether a top-level name [nm] syntactically
appears in the term [t]. *)
let name_appears_in (nm:name) (t:term) : Tac bool =
  let ff (t : term) : Tac term =
    match inspect t with
    | Tv_FVar fv ->
      if inspect_fv fv = nm then
        raise Appears;
      t
    | _ -> t
  in
  match catch (fun () -> ignore (V.visit_tm ff t); false) with
  | Inr x -> x
  | Inl Appears -> true
  | Inl e -> raise e