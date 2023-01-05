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
  = T.print (P.term_to_string t);
    match Pulse.Soundness.Common.check_top_level_environment g with
    | None -> T.fail "pulse main: top-level environment does not include stt at the expected types"
    | Some g ->
      let (| pre, ty, pre_typing |) = Pulse.Checker.Pure.check_tot g [] pre in
      if ty = Tm_VProp
      then let pre_typing : tot_typing g [] pre Tm_VProp = E pre_typing in
           let (| t, c, t_typing |) = check g [] t pre pre_typing None in
           let refl_e = elab_src_typing t_typing in
           let refl_t = elab_pure_comp c in
           soundness_lemma g [] t c t_typing;
           (refl_e, refl_t)
      else T.fail "pulse main: cannot typecheck pre at type vprop"

let main t pre : RT.dsl_tac_t = main' t pre

let erased_lid = ["Pulse"; "Steel"; "Wrapper"; "erased"]
let hide_lid = ["Pulse"; "Steel"; "Wrapper"; "hide"]
let reveal_lid = ["Pulse"; "Steel"; "Wrapper"; "reveal"]
let u32_lid = ["Pulse"; "Steel"; "Wrapper"; "u32"]
let ref_lid = ["Pulse"; "Steel"; "Wrapper"; "ref"]
let pts_to_lid = ["Pulse"; "Steel"; "Wrapper"; "pts_to"]
let read_lid = ["Pulse"; "Steel"; "Wrapper"; "read"]
let write_lid = ["Pulse"; "Steel"; "Wrapper"; "write"]

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
  = let bv, (aq, attrs) = R.inspect_binder b in
    match attrs, aq with
    | _::_, _ -> error "Unexpected attribute"
    | _, R.Q_Meta _ -> error "Unexpected binder qualifier"
    | _ -> 
      let q = Readback.readback_qual aq in
      RT.pack_inspect_binder b;  // This does not have SMTPat
      let bv_view = R.inspect_bv bv in
      assume (bv_view.bv_ppname == "_" /\ bv_view.bv_index == 0);
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

let rec translate_term' (t:R.term)
  : T.Tac (err term)
  = match R.inspect_ln t with
    | R.Tv_Abs x body -> (
      let? b, q = transate_binder x in
      let aux () = 
        let? body = translate_term body in
        Inl (Tm_Abs b q Tm_Emp body None)
      in
      match R.inspect_ln body with
      | R.Tv_AscribedT body t None false -> (
        match? readback_comp t with
        | C_ST st ->
          let? body = translate_st_term body in
          Inl (Tm_Abs b q st.pre body (Some st.post))
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
              let? body = translate_st_term body in
              Inl (Tm_Abs b q pre body (Some post))
            
            | _ -> aux ()
          )

          | [(expects_arg, _); (body, _)] -> (  
            let? pre = readback_ty expects_arg in
            let? body = translate_st_term body in
            Inl (Tm_Abs b q pre body None)
          )

          | _ -> aux ()
        )
      )
        
      | _ -> 
        aux ()
    )

    | _ -> 
      unexpected_term "translate_term'" t

and translate_st_term (t:R.term)
  : T.Tac (err term)
  = match R.inspect_ln t with 
    | R.Tv_App _ _ -> (
      let? t = readback_ty t in
      match t with
      | Tm_PureApp head q arg -> Inl (Tm_STApp head q arg)
      | _ -> Inl t
    )

    | R.Tv_Let false [] bv def body ->
      let? def = translate_st_term def in 
      let? body = translate_st_term body in 
      Inl (Tm_Bind def body)

    | _ ->
      unexpected_term "st_term" t
  
and translate_term (t:R.term)
  : T.Tac (err term)
  = match readback_ty t with
    | Inl t -> Inl t
    | _ -> translate_term' t

let check' (t:R.term) (g:RT.fstar_top_env)
  : T.Tac (r:(R.term & R.typ){RT.typing g (fst r) (snd r)})
  = match translate_term t with
    | Inr msg -> T.fail (Printf.sprintf "Failed to translate term: %s" msg)
    | Inl t -> 
      T.print (Printf.sprintf "Translated term is\n%s\n" (P.term_to_string t));
      main t Tm_Emp g

[@@plugin]
let check (t:R.term) : RT.dsl_tac_t = check' t
