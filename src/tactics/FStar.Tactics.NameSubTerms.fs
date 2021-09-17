#light "off"
module FStar.Tactics.NameSubTerms
open FStar.Compiler.Effect
open FStar.Compiler
open FStar.Compiler.List
open FStar.Syntax.Syntax
open FStar.Tactics.Types
open FStar.Tactics.Monad

module TcTerm = FStar.TypeChecker.TcTerm
module Z = FStar.BigInt
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module Env = FStar.TypeChecker.Env
module U = FStar.Syntax.Util
module BU = FStar.Compiler.Util
module Print = FStar.Syntax.Print
type subterm_identifier = term -> tac<option<int>>
type imap_entry = (int * binder * term)
type identifier_map = list<imap_entry>

let find_identifier (i:int) (imap:identifier_map) 
  : option<imap_entry>
  = List.tryFind (fun (j, _, _) -> i=j) imap
  
let rec build_term_imap (env:Env.env)
                          (cb:subterm_identifier)
                          (imap:identifier_map)
                          (t:term)
  : tac<(term * identifier_map)>
  = bind (cb t) (fun x ->
      match x with
      | None -> //recurse on sub-terms
        build_subterms_imap env cb imap t
      
      | Some i ->
        match find_identifier i imap with
        | Some (_, x, t') ->
          if U.term_eq t t'
          then (
            // a name was already generated for this subterm
            // just use it
            ret (S.bv_to_name x.binder_bv, imap)
          ) else (
            fail (BU.format2 "Inconsistent naming for a term: %s and %s" 
                             (Print.term_to_string t)
                             (Print.term_to_string t'))
          )

        | None ->
          // generate a new name for it
          match TcTerm.typeof_tot_or_gtot_term_fastpath env t false with
          | None -> fail "Subterm could not be typed"
          | Some t_ty -> 
            let x = S.new_bv (Some t.pos) t_ty in
            ret (S.bv_to_name x, ((i, S.mk_binder x, t)::imap)))

and build_subterms_imap (env:Env.env)
                        (cb:subterm_identifier)
                        (imap:identifier_map)
                        (t:term)            
  : tac<(term * identifier_map)>
  = let rec aux_args imap args =
        match args with
        | [] -> ret (args, imap)
        | hd::tl -> 
          bind (build_term_imap env cb imap (fst hd)) (fun (hd_t, imap) ->
          bind (aux_args imap tl) (fun (tl, imap) ->
          ret ((hd_t, snd hd)::tl, imap)))
    in
    match (SS.compress t).n with
    | Tm_bvar _ -> failwith "Impossible: locally nameless"
    | Tm_delayed _ -> failwith "Impossible: compressed"

    | Tm_let _ ->
      fail "let bindings in the goal are not supported for renaming: Please normalize the goal first"
      
    | Tm_name _
    | Tm_fvar _
    | Tm_uinst _
    | Tm_constant _
    | Tm_type _ 
    | Tm_uvar _ 
    | Tm_lazy _ 
    | Tm_quoted _
    | Tm_unknown ->
      //no sub-terms to descend into
      ret (t, imap) 

    | Tm_app (head, args) ->
      bind (build_term_imap env cb imap head) (fun (head', imap) ->
      bind (aux_args imap args) (fun (args', imap) ->
      ret (S.mk_Tm_app head' args' t.pos, imap)))

    | Tm_ascribed (head, (Inl annot, None), lopt) ->
      bind (build_term_imap env cb imap head) (fun (head, imap) ->
      bind (build_term_imap env cb imap annot) (fun (annot, imap) ->
      ret (S.mk (Tm_ascribed(head, (Inl annot, None), lopt)) t.pos, imap)))

    | Tm_ascribed _ ->
      fail "This form of ascription is not supported for renaming"

    | Tm_abs _
    | Tm_arrow _
    | Tm_refine _
    | Tm_match _ ->
      fail "Terms with bindings are not supported for renaming"

let binders_and_equalities env (imap:identifier_map) 
  : binders *
    binders *
    subst_t
  = List.map (fun (_, b, _) -> b) imap, 
    List.map 
      (fun (_, b, t) -> 
        let t = 
          U.mk_eq2 (TcTerm.universe_of env b.binder_bv.sort)
                   b.binder_bv.sort
                   (S.bv_to_name b.binder_bv)
                   t
        in
        let bv = S.new_bv None t in
        S.mk_binder bv)
      imap, 
    List.map (fun (_, b, t) -> NT(b.binder_bv, t)) imap

let close_goal (subst:subst_t)
  : tac<unit>
  = bind cur_goal (fun goal ->
    let t = SS.subst subst (goal_type goal) in
    bind dismiss (fun _ -> 
    add_goals [goal_with_type goal t]))

  
let name_sub_terms 
      (cb: subterm_identifier)
      (cont: identifier_map -> (unit -> tac<unit>) -> tac<unit>)
  : tac<unit>
  = bind cur_goal (fun goal ->
    bind (build_term_imap (goal_env goal) cb [] (goal_type goal)) (fun (t, imap) ->
    let binders, eq_binders, subst = binders_and_equalities (goal_env goal) imap in
    let env' = Env.push_binders (goal_env goal) (binders @ eq_binders) in
    //introduce a new goal with t in an extended environment
    bind (new_uvar "name subterms" env' t (range_of goal)) (fun (new_goal_witness, ctx_uvar_new_goal) ->
    //immediately unify the old goal with the new one, to ensure
    //that any solution to the new goal does not contain the newly bound variable
    bind (FStar.Tactics.Basic.solve goal new_goal_witness) (fun _ -> 
    let g = mk_goal env' ctx_uvar_new_goal goal.opts goal.is_guard goal.label in
    bind (add_goals [g]) (fun _ ->
    cont imap (fun () -> close_goal subst))))))
