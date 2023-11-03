module FStar.Tactics.MApply

open FStar.Reflection.V2
open FStar.Reflection.V2.Formula

open FStar.Tactics.Effect
open FStar.Tactics.V2.Builtins
open FStar.Tactics.NamedView
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Tactics.V2.Derived
open FStar.Tactics.V2.SyntaxCoercions

open FStar.Tactics.Typeclasses

private val push1 : (#p:Type) -> (#q:Type) ->
                        squash (p ==> q) ->
                        squash p ->
                        squash q
private let push1 #p #q f u = ()

private val push1' : (#p:Type) -> (#q:Type) ->
                         (p ==> q) ->
                         squash p ->
                         squash q
private let push1' #p #q f u = ()

(*
 * Some easier applying, which should prevent frustration
 * (or cause more when it doesn't do what you wanted to)
 *)
val apply_squash_or_lem : d:nat -> term -> Tac unit
let rec apply_squash_or_lem d t =
    (* Before anything, try a vanilla apply and apply_lemma *)
    try apply t with | _ ->
    try apply (`FStar.Squash.return_squash); apply t with | _ ->
    try apply_lemma t with | _ ->

    // Fuel cutoff, just in case.
    if d <= 0 then fail "mapply: out of fuel" else begin

    let ty = tc (cur_env ()) t in
    let tys, c = collect_arr ty in
    match inspect_comp c with
    | C_Lemma pre post _ ->
       begin
       let post = `((`#post) ()) in (* unthunk *)
       let post = norm_term [] post in
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
         let rt = norm_term [] rt in
         (* Is the lemma an implication? We can try to intro *)
         match term_as_formula' rt with
         | Implies p q ->
             apply_lemma (`push1);
             apply_squash_or_lem (d-1) t

         | _ ->
             fail "mapply: can't apply (1)"
         end

       (* If not, we can try to introduce the squash ourselves first *)
       | None ->
        // DUPLICATED, refactor!
         begin
         let rt = norm_term [] rt in
         (* Is the lemma an implication? We can try to intro *)
         match term_as_formula' rt with
         | Implies p q ->
             apply_lemma (`push1);
             apply_squash_or_lem (d-1) t

         | _ ->
             apply (`FStar.Squash.return_squash);
             apply t
         end
       end
    | _ -> fail "mapply: can't apply (2)"
    end

class termable (a : Type) = {
  to_term : a -> Tac term
}

instance termable_term : termable term = {
  to_term = (fun t -> t);
}

instance termable_binding : termable binding = {
  to_term = (fun b -> binding_to_term b);
}

(* `m` is for `magic` *)
let mapply0 (t : term) : Tac unit =
  apply_squash_or_lem 10 t

let mapply (#ty:Type) {| termable ty |} (x : ty) : Tac unit =
  let t = to_term x in
  apply_squash_or_lem 10 t
