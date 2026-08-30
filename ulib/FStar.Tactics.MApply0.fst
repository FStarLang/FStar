module FStar.Tactics.MApply0

open FStar.Stubs.Reflection.Types
open FStar.Reflection.V2
open FStar.Reflection.V2.Formula

open FStar.Tactics.Effect
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Tactics.NamedView
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Tactics.V2.Derived
open FStar.Tactics.V2.SyntaxCoercions

let push1 #p #q f u = ()
let push1' #p #q f u = ()

(*
 * Some easier applying, which should prevent frustration
 * (or cause more when it doesn't do what you wanted to)
 *)
(* [collect_arr] does not push the arrow's binders into the environment, so
   the codomain it returns is an open term: normalizing it may fail with
   "Variable n not found" for a dependent signature such as
   [#n:pos -> #x:uint_t n -> ... -> Lemma (x == y)].  Normalization is only
   ever an attempt to expose an implication here, so fall back on the
   un-normalized term rather than failing with an error that points into the
   lemma being applied. *)
private
let norm_term_or_id (t:term) : Tac term =
  try norm_term [] t with | _ -> t

val apply_squash_or_lem : d:nat -> term -> Tac unit
let rec apply_squash_or_lem d t =
    (* Before anything, try a vanilla apply and apply_lemma *)
    try apply t with | _ ->
    // try apply (`FStar.Squash.return_squash); apply t with | _ ->
    try apply_lemma t with | _ ->

    // Fuel cutoff, just in case.
    if d <= 0 then fail "mapply: out of fuel" else begin

    let ty = tc (cur_env ()) t in
    let tys, c = collect_arr ty in
    match inspect_comp c with
    | C_Lemma pre post _ ->
       begin
       let post = `((`#post) ()) in (* unthunk *)
       let post = norm_term_or_id post in
       (* Is the lemma an implication? We can try to intro *)
       match term_as_formula' post with
       | Implies p q ->
           apply_lemma (`push1);
           apply_squash_or_lem (d-1) t

       | _ ->
           fail "mapply: can't apply (1)"
       end
    | C_Total rt ->
       begin match unsquash_term rt with
       (* If the function returns a squash, just apply it, since our goals are squashed *)
       | Some rt ->
        // DUPLICATED, refactor!
         begin
         let rt = norm_term_or_id rt in
         (* Is the lemma an implication? We can try to intro *)
         match term_as_formula' rt with
         | Implies p q ->
             apply_lemma (`push1);
             apply_squash_or_lem (d-1) t

         | _ ->
             fail "mapply: can't apply (2)"
         end

       (* If not, we can try to introduce the squash ourselves first *)
       | None ->
        // DUPLICATED, refactor!
         begin
         let rt = norm_term_or_id rt in
         (* Is the lemma an implication? We can try to intro *)
         match term_as_formula' rt with
         | Implies p q ->
             apply_lemma (`push1);
             apply_squash_or_lem (d-1) t

         | _ ->
            //  apply (`FStar.Squash.return_squash);
             apply t
         end
       end
    | _ -> fail "mapply: can't apply (3)"
    end

(* `m` is for `magic` *)
let mapply0 (t : term) : Tac unit =
  apply_squash_or_lem 10 t
