module MiniSteel
module RT = Refl.Typing
module R = FStar.Reflection

type lident = R.name

type constant =
  | Unit
  | Bool of bool
  | Int of int

let var = nat
let index = nat  
 
type term =
  | Tm_BVar     : i:index -> term
  | Tm_Var      : v:var -> term
  | Tm_FVar     : l:lident -> term
  | Tm_Constant : c:constant -> term
  | Tm_PureApp  : head:term -> arg:term -> term
  | Tm_Let      : t:typ -> e1:term -> e2:term -> term  
  | Tm_Emp      : term
  | Tm_Pure     : p:term -> term
  | Tm_Star     : l:term -> r:term -> term
  | Tm_ExistsSL : t:typ -> body:term -> term
  | Tm_ForallSL : t:typ -> body:term -> term
  | Tm_Arrow    : t:typ -> body:comp -> term 
  | Tm_Type     : term
  | Tm_VProp    : term
  | Tm_STApp    : head:term -> arg:term -> term  
  | Tm_Bind     : t:typ -> e1:term -> e2:term -> term
  | Tm_If       : b:term -> then_:term -> else_:term -> term

and comp = 
  | C_Tot : typ -> comp
  | C_ST  : st_comp -> comp

and st_comp = {
  res:typ;
  pre:term;
  post:term
}

and typ = term

let rec open_term' (t:term) (v:var) (i:index)
  : term
  = admit()
and open_comp' (c:comp) (v:var) (i:index)
  : comp
  = admit()

let open_term t v = open_term' t v 0

let rec close_term' (t:term) (v:var) (i:index)
  : term
  = admit()
and close_comp' (c:comp) (v:var) (i:index)
  : comp
  = admit()

let close_term t v = close_term' t v 0
let close_comp t v = close_comp' t v 0

assume
val open_comp_with' (c:comp) (x:term) (v:index)
  : c':comp{ C_ST? c' <==> C_ST? c }
let open_comp_with c x = open_comp_with' c x 0

let fstar_env =
  g:R.env { 
    RT.lookup_fvar g RT.bool_fv == Some (RT.tm_type RT.u_zero)
    ///\ vprop etc
  }

let fstar_top_env =
  g:fstar_env { 
    forall x. None? (RT.lookup_bvar g x )
  }

let eqn = term & term
let binding = either typ eqn
let env = list (var & binding)

assume
val elab_term (t:term) : R.term

assume
val elab_comp (c:comp) : R.comp

assume
val extend_env_l (f:fstar_top_env) (g:env) : fstar_env

let rec lookup (e:list (var & 'a)) (x:var)
  : option 'a
  = match e with
    | [] -> None
    | (y, v) :: tl -> if x = y then Some v else lookup tl x

let lookup_ty (e:env) (x:var)
  : option typ
  = match lookup e x with
    | Some (Inl t) -> Some t
    | _ -> None

let comp_ty (c:comp) 
  : typ
  = match c with
    | C_Tot t -> t
    | C_ST c -> c.res

let add_frame (s:st_comp) (frame:term) = 
   { s with pre = Tm_Star s.pre frame;
            post = Tm_Star s.post frame }

assume
val freevars (t:term) : FStar.Set.set var


[@@erasable]
noeq
type bind_comp (f:fstar_top_env) : env -> st_comp -> var -> st_comp -> st_comp -> Type =
  | Bind_comp :
      g:env ->
      c1:st_comp ->
      x:var ->
      c2:st_comp {
        open_term c1.post x == c2.pre /\
        ~(x `Set.mem` freevars c2.post) /\
        ~(x `Set.mem` freevars c2.res) 
      } ->
      bind_comp f g c1 x c2 ({res = c2.res; pre = c1.pre; post=c2.post})


[@@erasable]
noeq
type vprop_equiv (f:fstar_top_env) : env -> term -> term -> Type =
  | VE_Refl:
     g:env ->
     t:term ->
     vprop_equiv f g t t

  | VE_Unit:
     g:env ->
     t:term ->
     vprop_equiv f g (Tm_Star Tm_Emp t) t

  | VE_Comm:
     g:env ->
     t0:term ->
     t1:term ->
     vprop_equiv f g (Tm_Star t0 t1) (Tm_Star t1 t0)
     
  | VE_Assoc:
     g:env ->
     t0:term ->
     t1:term ->
     t2:term ->
     vprop_equiv f g (Tm_Star t0 (Tm_Star t1 t2)) (Tm_Star (Tm_Star t0 t1) t2)

  | VE_Ex:
     g:env ->
     x:var { None? (lookup_ty g x) } ->
     ty:typ ->
     t0:term ->
     t1:term ->
     vprop_equiv f g (open_term t0 x) (open_term t1 x) ->
     vprop_equiv f g (Tm_ExistsSL ty t0) (Tm_ExistsSL ty t1)

  | VE_Fa:
     g:env ->
     x:var { None? (lookup_ty g x) } ->
     ty:typ ->
     t0:term ->
     t1:term ->
     vprop_equiv f g (open_term t0 x) (open_term t1 x) ->
     vprop_equiv f g (Tm_ForallSL ty t0) (Tm_ForallSL ty t1)


[@@erasable]
noeq
type st_equiv (f:fstar_top_env) : env -> st_comp -> st_comp -> Type =
  | ST_Equiv :
      g:env ->
      c1:st_comp ->
      c2:st_comp { c1.res == c2.res } -> 
      x:var { None? (lookup_ty g x) } ->
      vprop_equiv f g c1.pre c2.pre ->
      vprop_equiv f ((x, Inl c1.res)::g) (open_term c1.post x) (open_term c2.post x) ->      
      st_equiv f g c1 c2

assume
val tm_bool : term
assume
val tm_true : term
assume
val tm_false : term
let mk_eq2 t (e0 e1:term) 
  : term
  = Tm_PureApp
         (Tm_PureApp (Tm_PureApp (Tm_FVar R.eq2_qn) t)
                      e0) e1

let return_comp (t:typ) (e:term) =
  { res = t;
    pre = Tm_Emp;
    post = Tm_Pure (mk_eq2 t (Tm_BVar 0) e) }

[@@erasable]
noeq
type src_typing (f:fstar_top_env) : env -> term -> comp -> Type =
  | T_Tot: 
      g:env ->
      e:term ->
      ty:typ ->
      RT.typing (extend_env_l f g) (elab_term e) (elab_term ty) ->
      src_typing f g e (C_Tot ty)

  | T_STApp :
      g:env ->
      head:term -> 
      formal:typ ->
      res:st_comp ->
      arg:term ->
      tot_typing f g head (Tm_Arrow formal (C_ST res)) ->
      tot_typing f g arg formal ->
      src_typing f g (Tm_STApp head arg) (open_comp_with (C_ST res) arg)

  | T_Return:
      g:env ->
      e:term -> 
      t:typ -> 
      tot_typing f g e t ->
      src_typing f g e (C_ST (return_comp t e))
      
  | T_Bind:
      g:env ->
      e1:term ->
      e2:term ->
      c1:st_comp ->
      c2:st_comp ->
      x:var { None? (lookup g x) (*  /\ ~(x `Set.mem` freevars e2) *) } ->
      c:st_comp ->
      src_typing f g e1 (C_ST c1) ->
      src_typing f ((x, Inl c1.res)::g) (open_term e2 x) (C_ST c2) ->
      bind_comp f g c1 x c2 c ->
      src_typing f g (Tm_Bind c1.res e1 e2) (C_ST c)

  | T_If:
      g:env ->
      b:term -> 
      e1:term ->
      e2:term -> 
      c:comp ->
      hyp:var { None? (lookup g hyp) // /\ ~ (hyp `Set.mem` freevars e1) /\ ~ (hyp `Set.mem` freevars e2)
  } ->
      tot_typing f g b tm_bool ->
      src_typing f ((hyp, Inr (b, tm_true)) :: g) e1 c ->
      src_typing f ((hyp, Inr (b, tm_false)) :: g) e2 c ->
      src_typing f g (Tm_If b e1 e2) c

  | T_Frame:
      g:env ->
      e:term ->
      c:st_comp ->
      frame:term ->
      tot_typing f g frame Tm_VProp ->
      src_typing f g e (C_ST c) ->
      src_typing f g e (C_ST (add_frame c frame))

  | T_Equiv:
      g:env ->
      e:term ->
      c:st_comp ->
      c':st_comp ->      
      src_typing f g e (C_ST c) ->
      st_equiv f g c c' ->
      src_typing f g e (C_ST c')

and tot_typing (f:fstar_top_env) (g:env) (e:term) (t:typ) = 
  src_typing f g e (C_Tot t)

and st_typing (f:fstar_top_env) (g:env) (e:term) (st:st_comp) = 
  src_typing f g e (C_ST st)

module L = FStar.List.Tot
let max (n1 n2:nat) = if n1 < n2 then n2 else n1

let rec fresh (e:list (var & 'a))
  : var
  = match e with
    | [] -> 0
    | (y, _) :: tl ->  max (fresh tl) y + 1
    | _ :: tl -> fresh tl

let rec fresh_not_mem (e:list (var & 'a)) (elt: (var & 'a))
  : Lemma (ensures L.memP elt e ==> fresh e > fst elt)
  = match e with
    | [] -> ()
    | hd :: tl -> fresh_not_mem tl elt
  
let rec lookup_mem (e:list (var & 'a)) (x:var)
  : Lemma
    (requires Some? (lookup e x))
    (ensures exists elt. L.memP elt e /\ fst elt == x)
  = match e with
    | [] -> ()
    | hd :: tl -> 
      match lookup tl x with
      | None -> assert (L.memP hd e)
      | _ -> 
        lookup_mem tl x;
        eliminate exists elt. L.memP elt tl /\ fst elt == x
        returns _
        with _ . ( 
          introduce exists elt. L.memP elt e /\ fst elt == x
          with elt
          and ()
        )

let fresh_is_fresh (e:env)
  : Lemma (None? (lookup e (fresh e)))
          [SMTPat (lookup e (fresh e))]
  =  match lookup e (fresh e) with
     | None -> ()
     | Some _ ->
       lookup_mem e (fresh e);
       FStar.Classical.forall_intro (fresh_not_mem e)
module RT = Refl.Typing

module T = FStar.Tactics      

assume
val tc_meta_callback (f:fstar_env) (e:R.term) 
  : T.Tac (option (t:R.term & RT.typing f e t))

assume
val readback_ty (t:R.term)
  : T.Tac (option (ty:typ { elab_term ty == t }))
  
let check_tot (f:fstar_top_env) (g:env) (t:term)
  : T.Tac (ty:typ &
           tot_typing f g t ty)
  = let f = extend_env_l f g in
    match tc_meta_callback f (elab_term t) with
    | None -> T.fail "Not typeable"
    | Some (| ty', tok |) ->
      match readback_ty ty' with
      | None -> T.fail "Inexpressible type"
      | Some ty -> (| ty, T_Tot g t ty tok |)

let try_split_vprop (f:fstar_top_env)
                    (g:env)
                    (ctxt:term)
                    (ctxt_typing: tot_typing f g ctxt Tm_VProp)
                    (req:term)
   : T.Tac (frame:term &
            tot_typing f g frame Tm_VProp &
            vprop_equiv f g (Tm_Star req frame) ctxt)
   = admit()            

let try_frame_pre (#f:fstar_top_env)
                  (#g:env)
                  (#t:term)
                  (#pre:term)
                  (pre_typing: tot_typing f g pre Tm_VProp)
                  (#c:comp { C_ST? c })
                  (t_typing: src_typing f g t c)
  : T.Tac (c':st_comp { c'.pre == pre } &
           src_typing f g t (C_ST c'))
  = let C_ST s = c in
    let (| frame, frame_typing, ve |) = try_split_vprop f g pre pre_typing s.pre in
    let t_typing
      : st_typing f g t (add_frame s frame)
      = T_Frame g t s frame frame_typing t_typing in
    let x = fresh g in
    let s' = add_frame s frame in
    let ve: vprop_equiv f g s'.pre pre = ve in
    let s'' = { s' with pre = pre } in
    let st_equiv = ST_Equiv g s' s'' x ve (VE_Refl _ _) in
    let t_typing = T_Equiv _ _ _ _ t_typing st_equiv in
    (| s'', t_typing |)

let rec check (f:fstar_top_env)
              (g:env)
              (t:term)
              (pre:term)
              (pre_typing: tot_typing f g pre Tm_VProp)
  : T.Tac (c:st_comp { c.pre == pre } &
           src_typing f g t (C_ST c))
  = match t with
    | Tm_BVar _ -> T.fail "not locally nameless"
    | Tm_Var _
    | Tm_FVar _ 
    | Tm_Constant _
    | Tm_PureApp _ _
    | Tm_Let _ _ _ 
    | Tm_Emp
    | Tm_Pure _
    | Tm_Star _ _ 
    | Tm_ExistsSL _ _
    | Tm_ForallSL _ _
    | Tm_Arrow _ _
    | Tm_Type
    | Tm_VProp ->
      let (| ty, d |) = check_tot f g t in
      let d = T_Return _ _ _ d in
      let d = T_Frame _ _ _ pre pre_typing d in
      let c = add_frame (return_comp ty t) pre in
      let d : src_typing f g t (C_ST c) = d in
      let c' = { c with pre = pre } in
      let x = fresh g in
      let eq : st_equiv f g c c' = ST_Equiv g c c' x (VE_Unit g pre) (VE_Refl _ _) in
      (| c', T_Equiv _ _ _ _ d eq |)

    | Tm_STApp head arg ->
      let (| ty_head, dhead |) = check_tot f g head in
      let (| ty_arg, darg |) = check_tot f g arg in      
      begin
      match ty_head with
      | Tm_Arrow formal (C_ST res) ->
        if ty_arg <> formal
        then T.fail "Type of formal parameter does not match type of argument"
        else let d = T_STApp g head formal res arg dhead darg in
             try_frame_pre pre_typing d
      | _ -> T.fail "Unexpected head type in impure application"
      end

    | Tm_Bind t e1 e2 ->
      let (| c1, d1 |) = check f g e1 pre pre_typing in
      if t <> c1.res 
      then T.fail "Annotated type of let-binding is incorrect"
      else (
        let x = fresh g in
        let next_pre = open_term c1.post x in
        let g' = (x, Inl c1.res)::g in
        let next_pre_typing : tot_typing f g' next_pre Tm_VProp =
          //would be nice to prove that this is typable as a lemma,
          //without having to re-check it
          match check_tot f g' next_pre with
          | (| Tm_VProp, nt |) -> nt
          | _ -> T.fail "next pre is not typable"
        in
        let (| c2, d2 |) = check f g' (open_term e2 x) next_pre next_pre_typing in
        if x `Set.mem` freevars c2.post
        ||  x `Set.mem` freevars c2.res
        then T.fail "Let-bound variable escapes its scope"
        else 
          let b : bind_comp f g c1 x c2 _ = 
            Bind_comp _ _ _ _
          in
          (| _, T_Bind _ _ _ _ _ _ _ d1 d2 b |)
     )

    | Tm_If _ _ _ ->
      T.fail "Not handling if yet"

