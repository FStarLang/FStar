module STLC.Infer
module T = FStar.Tactics
module R = FStar.Reflection
module L = FStar.List.Tot
module RT = FStar.Reflection.Typing
open STLC.Core

noeq
type stlc_exp 'a =
  | EUnit : stlc_exp 'a
  | EBVar : index -> stlc_exp 'a
  | EVar  : var -> stlc_exp 'a
  | ELam  : 'a -> stlc_exp 'a -> stlc_exp 'a
  | EApp  : stlc_exp 'a -> stlc_exp 'a -> stlc_exp 'a


let rec open_exp' (e:stlc_exp 'a) (v:var) (n:index)
  : stlc_exp 'a
  = match e with
    | EUnit -> EUnit
    | EVar m -> EVar m
    | EBVar m -> if m = n then EVar v else EBVar m
    | ELam t e -> ELam t (open_exp' e v (n + 1))
    | EApp e1 e2 -> EApp (open_exp' e1 v n) (open_exp' e2 v n)

let rec close_exp' (e:stlc_exp 'a) (v:var) (n:nat)
  : stlc_exp 'a
  = match e with
    | EUnit -> EUnit
    | EVar m -> if m = v then EBVar n else EVar m
    | EBVar m -> EBVar m
    | ELam t e -> ELam t (close_exp' e v (n + 1))
    | EApp e1 e2 -> EApp (close_exp' e1 v n) (close_exp' e2 v n)

let open_exp e v = open_exp' e v 0
let close_exp e v = close_exp' e v 0

let new_hole (g:R.env)
  : T.Tac R.term
  = T.uvar_env g (Some (`stlc_ty))
    
let rec infer (g:R.env)
              (sg:list (var & R.term))
              (e:stlc_exp unit)
  : T.Tac (e:stlc_exp R.term & R.term)
  = match e with
    | EBVar _ -> 
      T.fail "Not locally nameless!"
      
    | EUnit ->
      (| EUnit, `TUnit |)


    | EVar x ->
      begin
      match lookup sg x with
      | None -> T.fail "Unbound variable"
      | Some ht -> (| EVar x, ht |)
      end

    | ELam _ e ->
      let t0 = new_hole g in
      let x = fresh sg in
      let (| e, t |) = infer g ((x, t0) :: sg) (open_exp e x) in
      (| ELam t0 (close_exp e x), `(TArrow (`#(t0)) (`#(t))) |)

    | EApp e1 e2 ->
      let (| e1, t1 |) = infer g sg e1 in
      let (| e2, t2 |) = infer g sg e2 in
      let res = new_hole g in
      let ht = (`TArrow (`#(t2)) (`#(res))) in
      if T.unify_env g t1 ht
      then (| EApp e1 e2, res |)
      else T.fail ("Expected arrow type " ^ T.term_to_string res ^ 
                   " Got " ^ T.term_to_string t1)

let is_fv (t:R.term) (n:R.name)
  : T.Tac bool
  = match T.inspect t with
    | R.Tv_FVar fv ->
      R.inspect_fv fv = n
    | _ -> false
   
let rec read_back (g:R.env) (t:R.term)
  : T.Tac stlc_ty
  = let tt = T.inspect t in
    match tt with
    | R.Tv_Uvar _ _ -> 
      if T.unify_env g t (`TUnit)
      then read_back g t
      else T.fail "Impossible: Unresolved uvar must be unifiable with TUnit"
      
    | R.Tv_FVar _ ->
      if is_fv t ["STLC"; "Core"; "TUnit"]
      then TUnit
      else T.fail "Got an FV of type stlc_ty, but it is not a TUnit"

    | R.Tv_App _ _ ->
      begin
      let head, args = T.collect_app t in
      if not (is_fv head ["STLC"; "Core"; "TArrow"])
      then T.fail "Got an application of type stlc_ty, but head is not a TArrow"
      else match args with
           | [t1;t2] ->
             let t1 = read_back g (fst t1) in
             let t2 = read_back g (fst t2) in
             TArrow t1 t2
             
           | _ -> T.fail "Impossible: Incorrect arity of arrow"
      end

    | _ -> 
      T.fail "Unexpected constructor of stlc_ty"

let rec elab_core g (e:stlc_exp R.term)
  : T.Tac Core.stlc_exp
  = match e with
    | EUnit -> Core.EUnit
    | EBVar i -> Core.EBVar i
    | EVar x -> Core.EVar x
    | ELam t e -> Core.ELam (read_back g t) (elab_core g e)
    | EApp e1 e2 -> Core.EApp (elab_core g e1) (elab_core g e2)

let main (e:stlc_exp unit)
  : RT.dsl_tac_t
  = fun g -> 
      let (| e, _ |) = infer g [] e in
      let e = elab_core g e in
      Core.main e g

(***** Tests *****)

#set-options "--ugly"

%splice_t[foo] (main (ELam () (EBVar 0)))

#push-options "--no_smt"
let test_id () = assert (foo () == ()) by (T.compute ())
#pop-options

let bar_s = (ELam () (ELam () (EBVar 1)))
%splice_t[bar] (main bar_s)

let baz_s = EApp bar_s EUnit
%splice_t[baz] (main bar_s)
