module Pulse.Main

module T = FStar.Tactics
module R = FStar.Reflection
module RT = Refl.Typing
open FStar.Tactics
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker
open Pulse.Elaborate.Pure
open Pulse.Elaborate
open Pulse.Soundness

open Pulse.Parser
module P = Pulse.Syntax.Printer

let main' (t:term) (pre:term) (g:RT.fstar_top_env)
  : T.Tac (r:(R.term & R.typ){RT.typing g (fst r) (snd r)})
  = match Pulse.Soundness.Common.check_top_level_environment g with
    | None -> T.fail "pulse main: top-level environment does not include stt at the expected types"
    | Some g ->
      let (| pre, ty, pre_typing |) = Pulse.Checker.Pure.check_tot true g [] pre in
      if eq_tm ty Tm_VProp
      then let pre_typing : tot_typing g [] pre Tm_VProp = E pre_typing in
           let (| t, c, t_typing |) = check g [] t pre pre_typing None in
           let refl_e = elab_src_typing t_typing in
           let refl_t = elab_pure_comp c in
           soundness_lemma g [] t c t_typing;
           (refl_e, refl_t)
      else T.fail "pulse main: cannot typecheck pre at type vprop"

let main t pre : RT.dsl_tac_t = main' t pre

[@@plugin]
let parse_and_check (s:string) : RT.dsl_tac_t = main (parse s) Tm_Emp

let err a = either a string

let error #a msg : T.Tac (err a) = Inr msg

let (let?) (o:err 'a) (f:'a -> T.Tac (err 'b)) 
  : T.Tac (err 'b)
  = match o with
    | Inr msg -> Inr msg
    | Inl v -> f v

let unexpected_term msg t = 
  error (Printf.sprintf "Unexpected term (%s): %s"
                            msg
                            (T.term_to_string t))

let is_elim_exists (g:RT.fstar_top_env) (t:R.term)
  : T.Tac (option (R.universe & R.term & R.term)) =
  let open R in
  match inspect_ln t with
  | Tv_App hd (arg2, _) ->
    (match inspect_ln hd with
     | Tv_App hd (arg1, _) ->
       (match inspect_ln hd with
        | Tv_UInst v _
        | Tv_FVar v ->
          if inspect_fv v = elim_exists_lid
          then match inspect_ln arg2 with
               | Tv_Abs _ body ->
                 let uopt = T.universe_of g arg1 in
                 (match uopt with
                  | None -> None
                  | Some u -> Some (u, arg1, body))
               | _ -> None
          else None
        | _ -> None)
     | _ -> None)
  | _ -> None

let is_intro_exists (g:RT.fstar_top_env) (t:R.term)
  : T.Tac (option (R.universe & R.term & R.term & R.term)) =
  let open R in
  match inspect_ln t with
  | Tv_App hd (arg3, _) ->
    (match inspect_ln hd with
     | Tv_App hd (arg2, _) ->
       (match inspect_ln hd with
        | Tv_App hd (arg1, _) ->
          (match inspect_ln arg2 with
           | Tv_Abs _ body ->
             (match inspect_ln hd with
              | Tv_UInst fv _
              | Tv_FVar fv ->
                if inspect_fv fv = intro_exists_lid
                then let uopt = T.universe_of g arg1 in
                     match uopt with
                     | None -> None
                     | Some u -> Some (u, arg1, body, arg3)
                else None
              | _ -> None)
           | _ -> None)
        | _ -> None)
     | _ -> None)
  | _ -> None

let readback_universe (u:R.universe) : T.Tac (err universe) =
  try match Readback.readback_universe u with
      | None -> 
        error (Printf.sprintf "Unexpected universe : %s"
                              (T.universe_to_ast_string u))
      | Some u -> Inl u
  with
      | TacticFailure msg ->
        error (Printf.sprintf "Unexpected universe (%s) : %s"
                              msg
                              (T.universe_to_ast_string u))
      | _ ->
        error (Printf.sprintf "Unexpected universe : %s"
                              (T.universe_to_ast_string u))

let readback_ty (t:R.term)
  : T.Tac (err term)
  = try match Readback.readback_ty t with
        | None -> unexpected_term "readback_ty failed" t
        | Some t -> Inl #term t
    with 
      | TacticFailure msg -> 
        unexpected_term msg t
      | _ ->
        unexpected_term "readback failed" t

let readback_comp (t:R.term)
  : T.Tac (err comp)
  = try match Readback.readback_comp t with
        | None -> unexpected_term "computation" t
        | Some c -> Inl #comp c
    with
      | TacticFailure msg -> 
        unexpected_term msg t
      | _ ->
        unexpected_term "readback failed" t

let transate_binder (b:R.binder)
  : T.Tac (err (binder & option qualifier))
  = let {binder_bv=bv; binder_qual=aq; binder_attrs=attrs} =
        R.inspect_binder b
    in
    match attrs, aq with
    | _::_, _ -> error "Unexpected attribute"
    | _, R.Q_Meta _ -> error "Unexpected binder qualifier"
    | _ -> 
      let q = Readback.readback_qual aq in
      let bv_view = R.inspect_bv bv in
      assume (bv_view.bv_index == 0);
      let? b_ty' = readback_ty bv_view.bv_sort in      
      Inl ({binder_ty=b_ty';binder_ppname=bv_view.bv_ppname}, q)

let is_head_fv (t:R.term) (fv:list string) : option (list R.argv) = 
  let head, args = R.collect_app t in
  match R.inspect_ln head with
  | R.Tv_FVar fv' -> 
    if inspect_fv fv' = fv
    then Some args
    else None
  | _ -> None

let expects_fv = ["Pulse";"Tests";"expects"]
let provides_fv = ["Pulse";"Tests";"provides"]

//
// shift bvs > n by -1
//
// When we translate F* syntax to Pulse,
//   the else branch when translating if (i.e. Tm_match)
//   are an issue, as the pattern there is Pat_Wild bv,
//   which eats up 0th bv index
//
let rec shift_bvs_in_else (t:term) (n:nat) : Tac term =
  match t with
  | Tm_BVar bv ->
    if n < bv.bv_index
    then Tm_BVar {bv with bv_index = bv.bv_index - 1}
    else t
  | Tm_Var _
  | Tm_FVar _
  | Tm_UInst _ _
  | Tm_Constant _ -> t
  | Tm_Refine b t ->
    Tm_Refine {b with binder_ty=shift_bvs_in_else b.binder_ty n}
              (shift_bvs_in_else t (n + 1))
  | Tm_Abs _ _ _ _ _ ->
    T.fail "Did not expect an Tm_Abs in shift_bvs_in_else"
  | Tm_PureApp head q arg ->
    Tm_PureApp (shift_bvs_in_else head n)
               q
               (shift_bvs_in_else arg n)
  | Tm_Let t e1 e2 ->
    Tm_Let (shift_bvs_in_else t n)
           (shift_bvs_in_else e1 n)
           (shift_bvs_in_else e2 (n + 1))
  | Tm_STApp head q arg ->
    Tm_STApp (shift_bvs_in_else head n)
             q
             (shift_bvs_in_else arg n)
  | Tm_Bind e1 e2 ->
    Tm_Bind (shift_bvs_in_else e1 n)
            (shift_bvs_in_else e2 (n + 1))
  | Tm_Emp -> t
  | Tm_Pure p -> Tm_Pure (shift_bvs_in_else p n)
  | Tm_Star l r ->
    Tm_Star (shift_bvs_in_else l n)
            (shift_bvs_in_else r n)
  | Tm_ExistsSL u t body ->
    Tm_ExistsSL u (shift_bvs_in_else t n)
                  (shift_bvs_in_else body (n + 1))
  | Tm_ForallSL u t body ->
    Tm_ForallSL u (shift_bvs_in_else t n)
                  (shift_bvs_in_else body (n + 1))
  | Tm_Arrow _ _ _ ->
    T.fail "Unexpected Tm_Arrow in shift_bvs_in_else"
  | Tm_Type _
  | Tm_VProp -> t
  | Tm_If b e1 e2 post ->
    Tm_If (shift_bvs_in_else b n)
          (shift_bvs_in_else e1 n)
          (shift_bvs_in_else e2 n)
          (match post with
           | None -> None
           | Some post -> Some (shift_bvs_in_else post (n + 1)))
  | Tm_Inames
  | Tm_EmpInames -> t
  | Tm_ElimExists t ->
    Tm_ElimExists (shift_bvs_in_else t n)
  | Tm_IntroExists t e ->
    Tm_IntroExists (shift_bvs_in_else t n)
                   (shift_bvs_in_else e n)
  | Tm_UVar _ -> t

let rec translate_term' (g:RT.fstar_top_env) (t:R.term)
  : T.Tac (err term)
  = match R.inspect_ln t with
    | R.Tv_Abs x body -> (
      let? b, q = transate_binder x in
      let aux () = 
        let? body = translate_term g body in
        Inl (Tm_Abs b q (Some Tm_Emp) body None)
      in
      match R.inspect_ln body with
      | R.Tv_AscribedT body t None false -> (
        match? readback_comp t with
        | C_ST st ->
          let? body = translate_st_term g body in
          Inl (Tm_Abs b q (Some st.pre) body (Some st.post))
        | _ -> 
          aux ()
      )

      | R.Tv_App _ _ ->  (
        match is_head_fv body expects_fv with
        | None -> aux ()
        | Some args -> (
          match args with
          | [(expects_arg, _); (provides, _); (body, _)] -> (
            match is_head_fv provides provides_fv with
            | Some [provides_arg, _] ->
              let? pre = readback_ty expects_arg in
              let? post = 
                match R.inspect_ln provides_arg with
                | Tv_Abs _ provides_body ->
                  readback_ty provides_body
                | _ -> 
                  unexpected_term "'provides' should be an abstraction" provides_arg
              in
              let? body = translate_st_term g body in
              Inl (Tm_Abs b q (Some pre) body (Some post))
            
            | _ -> aux ()
          )

          | [(expects_arg, _); (body, _)] -> (  
            let? pre = readback_ty expects_arg in
            let? body = translate_st_term g body in
            Inl (Tm_Abs b q (Some pre) body None)
          )

          | _ -> aux ()
        )
      )
        
      | _ -> 
        aux ()
    )

    | _ -> 
      unexpected_term "translate_term'" t

and translate_st_term (g:RT.fstar_top_env) (t:R.term)
  : T.Tac (err term)
  = match R.inspect_ln t with 
    | R.Tv_App _ _ -> (
      let ropt = is_elim_exists g t in
      (match ropt with
       | None ->
         let ropt = is_intro_exists g t in
         (match ropt with
          | None ->
            let? t = readback_ty t in
            (match t with
             | Tm_PureApp head q arg -> Inl (Tm_STApp head q arg)
             | _ -> Inl t)
          | Some (u, t, p, e) ->
            let? u = readback_universe u in
            let? t = readback_ty t in
            let? p = readback_ty p in
            let? e = readback_ty e in
            Inl (Tm_IntroExists (Tm_ExistsSL u t p) e))
       | Some (u, t, p) ->
         let? u = readback_universe u in
         let? t = readback_ty t in
         let? p = readback_ty p in
         Inl (Tm_ElimExists (Tm_ExistsSL u t p)))
    )

    | R.Tv_Let false [] bv def body ->
      let? def = translate_st_term g def in 
      let? body = translate_st_term g body in 
      Inl (Tm_Bind def body)

    | R.Tv_Match b _ [(Pat_Constant C_True, then_);
                      (Pat_Wild _, else_)] ->
      let? b = readback_ty (pack_ln (inspect_ln_unascribe b)) in
      let? then_ = translate_st_term g then_ in
      let? else_ = translate_st_term g else_ in
      let else_ = shift_bvs_in_else else_ 0 in
      Inl (Tm_If b then_ else_ None)

    | _ ->
      unexpected_term "st_term" t
  
and translate_term (g:RT.fstar_top_env) (t:R.term)
  : T.Tac (err term)
  = match readback_ty t with
    | Inl t -> Inl t
    | _ -> translate_term' g t

let check' (t:R.term) (g:RT.fstar_top_env)
  : T.Tac (r:(R.term & R.typ){RT.typing g (fst r) (snd r)})
  = match translate_term g t with
    | Inr msg -> T.fail (Printf.sprintf "Failed to translate term: %s" msg)
    | Inl t -> 
      T.print (Printf.sprintf "Translated term is\n%s\n" (P.term_to_string t));
      main t Tm_Emp g

[@@plugin]
let check (t:R.term) : RT.dsl_tac_t = check' t
