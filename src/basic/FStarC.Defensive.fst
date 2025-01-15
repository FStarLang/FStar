module FStarC.Defensive

open FStarC
open FStarC.Effect
open FStarC.Util
open FStarC.Class.Binders
open FStarC.Class.Show
open FStarC.Class.Ord
open FStarC.Errors
open FStarC.Errors.Msg
open FStarC.Pprint
open FStarC.Class.Setlike

let () = let open FStarC.Syntax.Print in ()

val __def_check_scoped :
  #env_t:Type -> #thing_t:Type ->
  {| hasBinders env_t |} ->
  {| hasNames thing_t |} ->
  {| pretty thing_t |} ->
  range -> string ->
  env_t -> thing_t -> unit

instance pp_bv : pretty FStarC.Syntax.Syntax.bv = {
  pp = (fun bv -> arbitrary_string (show bv));
}

instance pp_set #a (_ : ord a) (_ : pretty a) : Tot (pretty (FlatSet.t a)) = {
  pp = (fun s ->
    let doclist (ds : list Pprint.document) : Pprint.document =
      surround_separate 2 0 (doc_of_string "[]") lbracket (semi ^^ break_ 1) rbracket ds
    in
    doclist (elems s |> List.map pp))
}

let __def_check_scoped rng msg env thing =
  let free = freeNames thing in
  let scope = boundNames env in
  if not (subset free scope) then
    Errors.log_issue rng Errors.Warning_Defensive [
         text "Internal: term is not well-scoped " ^/^ parens (doc_of_string msg);
         text "t =" ^/^ pp thing;
         text "FVs =" ^/^ pp free;
         text "Scope =" ^/^ pp scope;
         text "Diff =" ^/^ pp (diff free scope);
       ]

let def_check_scoped rng msg env thing =
  if Options.defensive () then
    __def_check_scoped rng msg env thing
