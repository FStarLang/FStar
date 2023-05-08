module Pulse.Main

module T = FStar.Tactics
module R = FStar.Reflection
module RT = FStar.Reflection.Typing
open FStar.Tactics
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Checker
open Pulse.Elaborate.Pure
open Pulse.Elaborate
open Pulse.Soundness

// open Pulse.Parser
module P = Pulse.Syntax.Printer

let main' (t:st_term) (pre:term) (g:RT.fstar_top_env)
  : T.Tac (r:(R.term & R.typ){RT.tot_typing g (fst r) (snd r)})
  = T.print (Printf.sprintf "About to check pulse term:\n%s\n" (P.st_term_to_string t));
    match Pulse.Soundness.Common.check_top_level_environment g with
    | None -> T.fail "pulse main: top-level environment does not include stt at the expected types"
    | Some g ->
      let (| pre, ty, pre_typing |) = Pulse.Checker.Pure.check_tot g [] pre in
      if eq_tm ty Tm_VProp
      then let pre_typing : tot_typing g [] pre Tm_VProp = E pre_typing in
           let (| t, c, t_typing |) = check g [] t pre pre_typing None in
           let refl_e = elab_st_typing t_typing in
           let refl_t = elab_comp c in
           soundness_lemma g [] t c t_typing;
           (refl_e, refl_t)
      else T.fail "pulse main: cannot typecheck pre at type vprop"

let main t pre : RT.dsl_tac_t = main' t pre

// [@@plugin]
// let parse_and_check (s:string) : RT.dsl_tac_t = main (parse s) Tm_Emp

let tuple2_lid = ["FStar"; "Pervasives"; "Native"; "tuple2"]
let tuple3_lid = ["FStar"; "Pervasives"; "Native"; "tuple3"]
let tuple4_lid = ["FStar"; "Pervasives"; "Native"; "tuple4"]
let tuple5_lid = ["FStar"; "Pervasives"; "Native"; "tuple5"]
let tuple6_lid = ["FStar"; "Pervasives"; "Native"; "tuple6"]
let tuple7_lid = ["FStar"; "Pervasives"; "Native"; "tuple7"]

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

let readback_maybe_unknown_ty t =
  match Readback.readback_ty t with
  | Some t -> t
  | None -> Tm_Unknown


let readback_ty (g:R.env) (t:R.term)
  : T.Tac (err term)
  = match Readback.readback_ty t with
    | None ->
      unexpected_term "readback failed" t    
    | Some t -> Inl t

let mk_star (l:list term) : term =
  match l with
  | [] -> Tm_Emp
  | [x] -> x
  | [x; y] -> Tm_Star x y
  | x::y::tl ->
    List.Tot.fold_left (fun t x -> Tm_Star t x) (Tm_Star x y) tl

let is_ntuple (s:R.name) : bool =
  s = tuple2_lid || s = tuple3_lid || s = tuple4_lid ||
  s = tuple5_lid || s = tuple6_lid || s = tuple7_lid

let rec translate_vprop (g:R.env) (t:R.term)
  : T.Tac (err vprop)
  = let hd, args = collect_app t in
    match inspect_ln hd with
    | Tv_FVar fv ->
      let qn = inspect_fv fv in
      if qn = exists_lid
      then translate_exists g t
      else if qn = exists_qn
      then translate_exists_formula g t
      else if qn = star_lid
      then translate_star g t
      else if is_ntuple qn
      then let? l = translate_vprop_list g (List.Tot.map fst args) in
           Inl (mk_star l)
      else if qn = pure_lid
      then translate_pure g t     
      else readback_ty g t

    | _ -> 
      readback_ty g t

and translate_exists (g:R.env) (t:R.term)
  : T.Tac (err term)
  = match inspect_ln t with
    | Tv_App hd (arg, _) ->
      (match inspect_ln hd with
       | Tv_FVar fv ->
         if inspect_fv fv = exists_lid
         then translate_exists_sl_body g arg
         else Inr "try readback exists: not an exists lid"
       | _ -> Inr "try readback exists: head not an fvar")
    | _ -> Inr "try readback exists: not an app"

and translate_exists_sl_body (g:R.env) (t:R.term) 
  : T.Tac (err term)
  = match inspect_ln t with
    | Tv_Abs b body ->
      let sort = (inspect_binder b).binder_sort in
      let u = U_unknown in
      let t = readback_maybe_unknown_ty sort in
      let? body = translate_vprop g body in
      Inl (Tm_ExistsSL u t body should_elim_true)
    | _ -> Inr "in readback exists: the arg not a lambda"

and translate_exists_formula (g:R.env) (t:R.term)
  : T.Tac (err term)
  = let fail () = 
        Inr (Printf.sprintf "Not an exists formula: %s"
                            (term_to_string t))
    in
    match term_as_formula t with
    | Exists bv sort body ->
      let bv = inspect_bv bv in
      let t = readback_maybe_unknown_ty sort in
      let? body = translate_vprop g body in
      Inl (Tm_ExistsSL U_unknown t body should_elim_true)
    | _ -> 
      let hd, args = collect_app t in
      match inspect_ln hd, args with
      | Tv_FVar fv, [(arg, _)] ->
        if inspect_fv fv = exists_qn
        then translate_exists_sl_body g arg
        else fail()
      | _ -> fail()

and translate_star (g:R.env) (t:R.term)
  : T.Tac (err term)
  = let hd, args = collect_app t in
    match inspect_ln hd, args with
    | Tv_FVar fv, [(l, _); (r, _)] ->
      let lid = inspect_fv fv in
      if lid = star_lid
      then let? l = translate_vprop g l in
           let? r = translate_vprop g r in
           Inl (mk_star [l; r])
      else Inr "Not a star"
    | _ ->  Inr "Not a star"

and translate_pure (g:R.env) (t:R.term)
  : T.Tac (err term)
  = let hd, args = collect_app t in
    match inspect_ln hd, args with
    | Tv_FVar fv, [(p, _)] ->
      if inspect_fv fv = pure_lid
      then let? p = readback_ty g p in
           Inl (Tm_Pure p)
      else Inr "Not a pure"
    | _ ->  Inr "Not a pure"

and translate_vprop_list (g:R.env) (l:list R.term) : T.Tac (err (list term)) =
  match l with
  | [] -> Inl []
  | hd::tl ->
    let? hd = translate_vprop g hd in
    let? tl = translate_vprop_list g tl in
    Inl (hd::tl)

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

let translate_binder (g:R.env) (b:R.binder)
  : T.Tac (err (binder & option qualifier))
  = let {binder_bv=bv; binder_qual=aq; binder_attrs=attrs;binder_sort=sort} =
        R.inspect_binder b
    in
    match attrs, aq with
    | _::_, _ -> error "Unexpected attribute"
    | _, R.Q_Meta _ -> error "Unexpected binder qualifier"
    | _ -> 
      let q = Readback.readback_qual aq in
      let bv_view = R.inspect_bv bv in
      assume (bv_view.bv_index == 0);
      let b_ty' = readback_maybe_unknown_ty sort in
      Inl ({binder_ty=b_ty';binder_ppname=bv_view.bv_ppname}, q)

let is_head_fv (t:R.term) (fv:list string) : T.Tac (option (list R.argv)) = 
  let head, args = T.collect_app t in
  match R.inspect_ln head with
  | R.Tv_FVar fv' -> 
    if inspect_fv fv' = fv
    then Some args
    else None
  | _ -> None

let mk_tests_lid s = ["Tests"; "Common"; s]

let expects_fv = mk_tests_lid "expects"
let provides_fv = mk_tests_lid "provides"
let intro_fv = mk_tests_lid "intro"
let elim_fv = mk_tests_lid "elim"
let while_fv = mk_tests_lid "while"
let invariant_fv = mk_tests_lid "invariant"
let par_fv = mk_tests_lid "par"
let rewrite_fv = mk_tests_lid "rewrite"
let local_fv = mk_tests_lid "local"
let tot_fv = mk_tests_lid "tot"

//
// shift bvs > n by -1
//
// When we translate F* syntax to Pulse,
//   the else branch when translating if (i.e. Tm_match)
//   are an issue, as the pattern there is Pat_Var bv,
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
  | Tm_PureApp head q arg ->
    Tm_PureApp (shift_bvs_in_else head n)
               q
               (shift_bvs_in_else arg n)
  | Tm_Let t e1 e2 ->
    Tm_Let (shift_bvs_in_else t n)
           (shift_bvs_in_else e1 n)
           (shift_bvs_in_else e2 (n + 1))
  | Tm_Emp -> t
  | Tm_Pure p -> Tm_Pure (shift_bvs_in_else p n)
  | Tm_Star l r ->
    Tm_Star (shift_bvs_in_else l n)
            (shift_bvs_in_else r n)
  | Tm_ExistsSL u t body se ->
    Tm_ExistsSL u (shift_bvs_in_else t n)
                  (shift_bvs_in_else body (n + 1))
                  se
  | Tm_ForallSL u t body ->
    Tm_ForallSL u (shift_bvs_in_else t n)
                  (shift_bvs_in_else body (n + 1))
  | Tm_Arrow _ _ _ ->
    T.fail "Unexpected Tm_Arrow in shift_bvs_in_else"
  | Tm_FStar _ ->
    T.fail "Embedded host terms are not fully handled in shift_bvs_in_else"
  | Tm_Type _
  | Tm_VProp
  | Tm_Inames
  | Tm_EmpInames
  | Tm_UVar _
  | Tm_Unknown -> t

let shift_bvs_in_else_opt (t:option term) (n:nat) : Tac (option term) =
    match t with
    | None -> None
    | Some t -> Some (shift_bvs_in_else t n)

let rec shift_bvs_in_else_list (t:list term) (n:nat) : Tac (list term) =
    match t with
    | [] -> []
    | hd::tl ->
      shift_bvs_in_else hd n ::
      shift_bvs_in_else_list tl n


let rec shift_bvs_in_else_st (t:st_term) (n:nat) : Tac st_term =
  match t with
  | Tm_Return c use_eq t -> Tm_Return c use_eq (shift_bvs_in_else t n)
  | Tm_Abs _ _ _ _ _ ->
    T.fail "Did not expect an Tm_Abs in shift_bvs_in_else_st"
  | Tm_STApp head q arg ->
    Tm_STApp (shift_bvs_in_else head n)
             q
             (shift_bvs_in_else arg n)
  | Tm_Bind e1 e2 ->
    Tm_Bind (shift_bvs_in_else_st e1 n)
            (shift_bvs_in_else_st e2 (n + 1))
  | Tm_If b e1 e2 post ->
    Tm_If (shift_bvs_in_else b n)
          (shift_bvs_in_else_st e1 n)
          (shift_bvs_in_else_st e2 n)
          (shift_bvs_in_else_opt post (n + 1))
  | Tm_ElimExists t ->
    Tm_ElimExists (shift_bvs_in_else t n)
  | Tm_IntroExists b t e ->
    Tm_IntroExists b (shift_bvs_in_else t n)
                     (shift_bvs_in_else_list e n)
  | Tm_While inv cond body ->
    Tm_While (shift_bvs_in_else inv (n + 1))
             (shift_bvs_in_else_st cond n)
             (shift_bvs_in_else_st body n)

  | Tm_Par preL eL postL preR eR postR ->
    Tm_Par (shift_bvs_in_else preL n)
           (shift_bvs_in_else_st eL n)
           (shift_bvs_in_else postL (n + 1))
           (shift_bvs_in_else preR n)
           (shift_bvs_in_else_st eR n)
           (shift_bvs_in_else postR (n + 1))

  | Tm_Rewrite p q ->
		Tm_Rewrite (shift_bvs_in_else p n)
				       (shift_bvs_in_else q n)

  | Tm_WithLocal init e ->
    Tm_WithLocal (shift_bvs_in_else init n)
                 (shift_bvs_in_else_st e (n + 1))

  | Tm_Admit c u t post ->
    Tm_Admit c u (shift_bvs_in_else t n)
                 (match post with
                  | None -> None
                  | Some post -> Some (shift_bvs_in_else post (n + 1)))

  | Tm_Protect t ->
    Tm_Protect (shift_bvs_in_else_st t n)

let try_seq (fs: list (R.term -> T.Tac (err 'b))) (x:R.term)
  : T.Tac (err 'b)
  = let rec aux msgs (fs:list (R.term -> T.Tac (err 'b)))
      : T.Tac (err 'b)
      = match fs with
        | [] -> 
          Inr (Printf.sprintf "Failed to parse term %s\n%s" (T.term_to_string x) msgs)
        | f::fs -> 
           match f x with
           | Inl r -> Inl r
           | Inr msg -> aux (msg ^ " \n " ^ msgs) fs
    in
    aux "" fs

let translate_elim (g:RT.fstar_top_env) (t:R.term)
  : T.Tac (err st_term)
  = let open R in
    match inspect_ln t with
    | Tv_App hd (arg, _) ->
      (match inspect_ln hd with
      | Tv_UInst v _
      | Tv_FVar v ->
        if inspect_fv v = elim_fv
        then let? ex = translate_vprop g arg in
             Inl (Tm_ElimExists ex)
        else Inr "ELIM_EXISTS: Not elim_exists"
      | _ -> Inr "ELIM_EXISTS: Not a fv application")
    | _ -> Inr "ELIM_EXISTS: Not an application"

let rec map_err (f:'a -> T.Tac (err 'b)) (l:list 'a)
  : T.Tac (err (list 'b))
  = match l with
    | [] -> Inl []
    | hd::tl ->
      let? hd = f hd in
      let? tl = map_err f tl in
      Inl (hd :: tl)

let translate_intro (g:RT.fstar_top_env) (t:R.term)
  : T.Tac (err st_term)
  = let open R in
    let head, args = T.collect_app t in
    match inspect_ln head with
    | Tv_UInst fv _
    | Tv_FVar fv ->
      if inspect_fv fv = intro_fv
      then match args with
           | (exists_body, _)::witnesses -> (
             let? ex = translate_vprop g exists_body in
             let? w = map_err (fun (w, _) -> readback_ty g w) witnesses in
             match ex with
             | Tm_ExistsSL _ _ _ _ ->
               Inl (Tm_IntroExists false ex w)
             | _ -> Inr "INTRO: Unexpected formula, not an existential"
           )
           | _ -> Inr "INTRO: Wrong number of arguments to intro_exists"
      else Inr "INTRO: Not an intro"
    | _ -> Inr "INTRO: Not an application"

//
// The last option term is post,
//   if we want admit in the middle of the code
// TODO: add code to parse it
//
let translate_admit (g:RT.fstar_top_env) (t:R.term)
  : T.Tac (err st_term)
  = let open R in
    let head, args = T.collect_app t in
    match inspect_ln head, args with
    | Tv_UInst v _, [(t, _)]
    | Tv_FVar v, [(t, _)] ->  
      let? t = readback_ty g t in
      let u = U_unknown in
      let l = inspect_fv v in
      if l = stt_admit_lid
      then Inl (Tm_Admit STT u t None)
      else if l = stt_atomic_admit_lid
      then Inl (Tm_Admit STT_Atomic u t None)
      else if l = stt_ghost_admit_lid
      then Inl (Tm_Admit STT_Ghost u t None)
      else Inr "ADMIT: Unknown admit flavor"
    | _ -> Inr "ADMIT: Unrecognized application"

let translate_st_app_or_return (g:R.env) (t:R.term)
  : T.Tac (err st_term)
  = let? t = readback_ty g t in
    match t with
    | Tm_PureApp head q arg ->
      (match head with
       | Tm_FVar {fv_name=l} ->
         if l = return_stt_lid
         then Inl (Tm_Return STT true arg)
         else if l = return_stt_noeq_lid
         then Inl (Tm_Return STT false arg)
         else if l = return_stt_atomic_lid
         then Inl (Tm_Return STT_Atomic true arg)
         else if l = return_stt_atomic_noeq_lid
         then Inl (Tm_Return STT_Atomic false arg)
         else if l = return_stt_ghost_lid
         then Inl (Tm_Return STT_Ghost true arg)
         else if l = return_stt_ghost_noeq_lid
         then Inl (Tm_Return STT_Ghost false arg)
         else Inl (Tm_STApp head q arg)
      | _ -> Inl (Tm_STApp head q arg))
    | _ -> Inl (Tm_Return STT false t)

let rec translate_term' (g:RT.fstar_top_env) (t:R.term)
  : T.Tac (err st_term)
  = match R.inspect_ln t with
    | R.Tv_Abs x body -> (
      let? b, q = translate_binder g x in
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
              let? pre = translate_vprop g expects_arg in
              let? post = 
                match R.inspect_ln provides_arg with
                | Tv_Abs _ provides_body ->
                  translate_vprop g provides_body
                | _ -> 
                  unexpected_term "'provides' should be an abstraction" provides_arg
              in
              let? body = translate_st_term g body in
              Inl (Tm_Abs b q (Some pre) body (Some post))
            
            | _ -> aux ()
          )

          | [(expects_arg, _); (body, _)] -> (  
            let? pre = readback_ty g expects_arg in
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
  : T.Tac (err st_term)
  = match R.inspect_ln t with 
    | R.Tv_Const _ ->
      translate_st_app_or_return g t
      
    | R.Tv_App _ _ ->
      try_seq [translate_elim g;
               translate_intro g;
               translate_while g;
               translate_par g;
               translate_admit g;
															translate_rewrite g;
               translate_st_app_or_return g]
              t
               
    | R.Tv_Let false [] bv ty def body ->
      let def_has_qual def qual_fv : bool & R.term =
        match (inspect_ln def) with
        | Tv_App hd arg ->
          (match (inspect_ln hd) with
           | Tv_FVar fv ->
             if inspect_fv fv = qual_fv then (true, fst arg)
             else false, def
           | _ -> false, def)
        | _ -> false, def in

      let? body = translate_st_term g body in
      T.print (Printf.sprintf ("Checking for Tot fv"));
      let has_mut, def = def_has_qual def local_fv in
      if has_mut
      then let? def = readback_ty g def in
           Inl (Tm_WithLocal def body)
      else let has_tot, def = def_has_qual def tot_fv in
           if has_tot
           then let? def = readback_ty g def in
                Inl (Tm_TotBind def body) 
           else let? def = translate_st_term g def in
                begin
                match def with
                | Tm_IntroExists _ _ _ -> 
                  Inl (Tm_Bind (Tm_Protect def) (Tm_Protect body))
                | _ ->
                  Inl (Tm_Bind def body)
                end

    | R.Tv_Match b _ [(Pat_Constant C_True, then_);
                      (Pat_Var _ _, else_)] ->
      let? b = readback_ty g (pack_ln (inspect_ln_unascribe b)) in
      let? then_ = translate_st_term g then_ in
      let? else_ = translate_st_term g else_ in
      let else_ = shift_bvs_in_else_st else_ 0 in
      Inl (Tm_If b then_ else_ None)

    | _ ->
      unexpected_term "st_term" t
  
and translate_term (g:RT.fstar_top_env) (t:R.term)
  : T.Tac (err st_term)
  = match readback_ty g t with
    | Inl t -> Inl (Tm_Return STT false t)
    | _ -> translate_term' g t

and translate_while (g:RT.fstar_top_env) (t:R.term)
  : T.Tac (err st_term)
  = let open R in
    let head, args = T.collect_app t in
    match inspect_ln head with
    | Tv_FVar v ->
      if inspect_fv v = while_fv
      then match args with
           | [(inv, _); (cond, _); (body, _)] -> 
             let? inv = 
               let hd, args = collect_app inv in
               match inspect_ln hd, args with
               | Tv_FVar fv, [(inv, _)] -> (
                 if inspect_fv fv <> invariant_fv
                 then Inr "WHILE: Expected while to be decorated with an invariant"
                 else (
                   match inspect_ln inv with
                   | Tv_Abs _ body -> translate_vprop g body
                   | _ ->
                     Inr (Printf.sprintf 
                           "WHILE: Expected inv to be an abstraction, got %s"
                           (T.term_to_string inv))
                 )
               )
               | _ -> 
                  Inr "WHILE: Expected while to be decorated with an invariant"
             in
             let? cond = translate_st_term g cond in
             let? body = translate_st_term g body in
             Inl (Tm_While inv cond body)
           | _ -> Inr "WHILE: Wrong number of arguments to while"
      else Inr "WHILE: Not while"
    | _ -> Inr "WHILE: Not a variable at the head"

and translate_rewrite (g:RT.fstar_top_env) (t:R.term)
  : T.Tac (err st_term) =

  let open R in
		let head, args = T.collect_app t in
		match inspect_ln head with
		| Tv_FVar v ->
			 if inspect_fv v = rewrite_fv
			 then match args with
					    | [(p, _); (q, _)] ->
						     let? p = readback_ty g p in
						     let? q = readback_ty g q in
						     Inl (Tm_Rewrite p q)
					    | _ -> Inr "REWRITE: Wrong number of arguments to rewrite"
			 else Inr "REWRITE: Not rewrite"
	 | _ ->	Inr "REWRITE: Not a variable at the head" 

and translate_par (g:RT.fstar_top_env) (t:R.term)
  : T.Tac (err st_term) =

  let open R in
  let head, args = T.collect_app t in
  match inspect_ln head with
  | Tv_FVar v ->
    if inspect_fv v = par_fv
    then match args with
         | [(preL, _); (eL, _); (postL, _);
            (preR, _); (eR, _); (postR, _)] ->

           let? preL = readback_ty g preL in
           let? eL = translate_st_term g eL in
           let? postL =
             match inspect_ln postL with
             | Tv_Abs _ body -> readback_ty g body
             | _ -> Inr "par: Expected postL to be an abstraction" in

           let? preR = readback_ty g preR in
           let? eR = translate_st_term g eR in
           let? postR =
             match inspect_ln postR with
             | Tv_Abs _ body -> readback_ty g body
             | _ -> Inr "par: Expected postR to be an abstraction" in

           Inl (Tm_Par preL eL postL preR eR postR)
         | _ -> Inr "par: Wrong number of arguments"
    else Inr "par: not a par"
  | _ -> Inr "par: Not a variable at the head"

let check' (t:R.term) (g:RT.fstar_top_env)
  : T.Tac (r:(R.term & R.typ){RT.tot_typing g (fst r) (snd r)})
  = match translate_term g t with
    | Inr msg -> T.fail (Printf.sprintf "Failed to translate term: %s" msg)
    | Inl t -> 
      T.print (Printf.sprintf "Translated term is\n%s\n" (P.st_term_to_string t));
      main t Tm_Emp g

[@@plugin]
let check (t:R.term) : RT.dsl_tac_t = check' t
  
[@@plugin]
let check_pulse (namespaces:list string)
                (module_abbrevs:list (string & string))
                (content:string)
                (file_name:string)
                (line col:int)
  : RT.dsl_tac_t
  = fun env ->
      match Pulse.ASTBuilder.parse_pulse env namespaces module_abbrevs content file_name line col with
      | Inl st_term ->
        main st_term Tm_Emp env
      | Inr (msg, range) ->
        T.fail (Printf.sprintf "Error @ %s: %s"
                  (T.range_to_string range)
                  msg)
