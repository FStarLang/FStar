module Elab
open Ast
open FStar.Tactics
module L = FStar.List.Tot
module A = Ast
module R = FStar.Reflection
//This should be some abstract effect which includes some exception mechanism
//
//It represents calling back into typechecker, but does not involve
//manipulating and proofstate.
//
// As such, it is distinct from the Tac effect.
// For now, just assuming that it is a Dv
effect Meta (t:Type) = Dv t

assume
val raise (s:string) : Meta 'a


// The type env encapsulates the typechecker's state
// It includes bindings for all the free names, as usual
// A token from F* for `g |- e : Tot t`
assume
val fstar_tc_tc_typing (g:env) (e:term) (c:comp) : Type0

//This is really meant to not have any observable side-effects on g or e
//  So, it only succeeds with neither e, e', nor t have any free uvars
assume
val fstar_tc_tc (g:R.env) (e:R.term)
  : Meta (c:R.comp & fstar_tc_tc_typing g e c)

assume
val lookup_bvar (e:env) (x:bv) : option term

assume
val lookup_fvar (e:env) (x:fv) : option term

// See R.push_binder
assume
val push_var (e:env) (x:A.ident) (t:A.term) : env

assume
val inspect_binder (g:env)
                   (_:R.binder)
  : Tot (R.bv & (R.aqualv & list R.term))


assume
val inspect (g:env)
            (t:R.term)
  : Tot (tv:R.term_view { smaller tv t })



let mk_total (t:R.term)
  = pack_comp (C_Total t [])

[@@erasable]
noeq
type typing : R.env -> R.term -> R.comp -> Type =
  | T_TC : #g:_ -> #e:_ -> #c:_ ->
           fstar_tc_tc_typing g e c ->
           typing g e c


(* option as a monad, to make the notation a bit lighter *)
let return #a (x:a) : option a = Some x
let fail #a (x:string) : option a = None
let bind #a #b (x:option a) (y: a -> option b)
  : option b
  = match x with
    | None -> None
    | Some v -> y v

let elab_constant (c:constant)
  : vconst
  = match c with
    | A.Unit -> C_Unit
    | A.Bool true -> C_True
    | A.Bool false -> C_False
    | A.Int i -> C_Int i

let elab_ident (e:A.ident) : bv = admit()
let elab_lident (e:A.lident) : fv = admit()

let lookup_var (e:env) (x:A.var)
  : option (either bv fv & R.term)
  = match x with
    | Bound _ -> fail "Not found"
    | Free i ->
      let bv = elab_ident i in
      t <--  lookup_bvar e bv;
      return (Inl bv, t)

    | Qualified q ->
      let fv = elab_lident q in
      t <--  lookup_fvar e fv;
      return (Inr fv, t)


let rec inspect_tot_arrow (g:env)
                          (t:R.term)
  : Tot (option (list bv & R.term))
        (decreases t)
  = match inspect g t with
    | Tv_Arrow b c ->
      let g = push_binder g b in
      let head, _ = inspect_binder g b in
      begin
      match inspect_comp c with
      | C_Total r _ ->
        tl_r <-- inspect_tot_arrow g r;
        let tl, r = tl_r in
        return (head::tl, r)

      | _ ->
        fail "Not a total arrow"
      end
    | _ -> return ([], t)

let elab_var (g:env) (x:A.var)
  : option R.term
  = y <-- lookup_var g x;
    match y with
    | Inl bv, _ ->
      return (pack_ln (Tv_Var bv))
    | Inr fv, _ ->
      return (pack_ln (Tv_FVar fv))

let steel_vprop_star (t0 t1:R.term)
  : R.term
  = admit()

let rec elab_term (g:env)
                      (src:A.term)
  : Tot (option R.term)
        (decreases src)
  = match src with
    | TConstant c ->
      let tgt0 = pack_ln (R.Tv_Const (elab_constant c)) in
      return tgt0

    | TVar x ->
      elab_var g x

    | TApp head args ->
      head_t <-- lookup_var g head;
      let _, t = head_t in
      formals_res <-- inspect_tot_arrow g t;
      if L.length (fst formals_res) <> L.length args
      then fail "Arity mismatch"
      else (
        head <-- elab_var g head;
        args <-- elab_terms g args;
        return (L.fold_left
                   (fun head arg -> pack_ln (Tv_App head (arg, Q_Explicit)))
                   head args)
      )

    | TStar t0 t1 ->
      t0 <-- elab_term g t0;
      t1 <-- elab_term g t1;
      return (steel_vprop_star t0 t1)

    | _ ->
      fail "Not yet implemented"

and elab_terms (g:env) (srcs:list A.term)
  : Tot (option (list R.term))
        (decreases srcs)
  = match srcs with
    | [] -> return []
    | hd :: tl ->
      hd <-- elab_term g hd;
      tl <-- elab_terms g tl;
      return (hd::tl)

let elab_app (g:env) (head:A.var) (args:list A.term)
  : Tot (option R.term)
  = head <-- elab_var g head;
    args <-- elab_terms g args;
    return (L.fold_left
                   (fun head arg -> pack_ln (Tv_App head (arg, Q_Explicit)))
                   head args)

let elab_term_tc (g:env) (src:A.term)
  : Meta (tgt:R.term & t:R.term & typing g tgt (mk_total t))
  = match elab_term g src with
    | None -> raise "Elab failed"
    | Some tgt ->
      let (| c, tct |) = fstar_tc_tc g tgt in
      match inspect_comp c with
      | C_Total t [] ->
        assume (mk_total t == c);
        (| tgt, t, T_TC tct |)
      | _ -> raise "Not total"

let elab_st_comp (g:env) (_:st_comp)
  : option R.comp
  = admit()

// g |- ST a p q ~ ST a p' q'
assume
val st_comp_equiv : g:env -> A.st_comp -> A.st_comp -> Type

let frame_st_comp (c:st_comp) (frame:A.term)
  : st_comp
  = { c with pre = TStar c.pre frame;
             post = TStar c.post frame }


let elab_atomic_stmt g (s:atomic_stmt)
  : option R.term
  = admit()

noeq
type atomic_stmt_typing
  : env ->
    atomic_stmt ->
    st_comp ->
    Type =
  | ST_Atomic:
      g:env ->
      a:atomic_stmt { Some? (elab_atomic_stmt g a) } ->
      c:st_comp { Some? (elab_st_comp g c) } ->
      (* The elaboration is typable in F* at a type corresponding to app_comp *)
      typing g (Some?.v (elab_atomic_stmt g a))
               (Some?.v (elab_st_comp g c)) ->
      atomic_stmt_typing g a c

let close_let_binding (s:stmt {LetBinding? s}) : stmt = admit()
let open_comp_with (x:A.ident) (s:st_comp) : st_comp = admit()

noeq
type stmt_typing
  : env ->
    stmt ->
    st_comp ->
    Type =
  | ST_AtomicStmt :
      g:env ->
      a:atomic_stmt { Some? (elab_atomic_stmt g a) }->
      c:st_comp { Some? (elab_st_comp g c) } ->
      (* The elaboration is typable in F* at a type corresponding to app_comp *)
      atomic_stmt_typing g a c ->
      stmt_typing g (A.Atomic a) c

  | ST_Frame:
      g:env ->
      s:stmt ->
      c:st_comp ->
      stmt_typing g s c ->
      pre:A.term ->
      frame:A.term ->
      st_comp_equiv g (frame_st_comp c frame)
                      ({ frame_st_comp c frame with pre = pre }) ->
      (* And we put a frame around it to make it callable in a context with pre *)
      stmt_typing g s ({ frame_st_comp c frame with pre = pre })

  | ST_Let:
      g:env ->
      x:A.ident ->
      head:atomic_stmt ->
      head_c:st_comp -> //the same name binding the result type
      atomic_stmt_typing g head head_c ->
      pre:A.term ->
      frame:A.term ->
      st_comp_equiv g (frame_st_comp head_c frame)
                      ({frame_st_comp head_c frame with pre}) ->
      body:stmt ->
      body_c:st_comp { body_c.pre == TStar (open_comp_with x head_c).post frame } ->
      stmt_typing (push_var g x head_c.typ) body body_c ->
      stmt_typing g (close_let_binding (LetBinding x head body))
                    ({ body_c with pre })


assume
val back_translate_comp (g:env) (c:comp)
  : option (x:A.st_comp { elab_st_comp g x == Some c })

let elab_atomic_stmt_typing (g:env) (a:atomic_stmt)
  : Meta (c:st_comp & atomic_stmt_typing g a c)
  = match elab_atomic_stmt g a with
    | None -> raise "Elaboration failed"
    | Some tgt ->
      let (| c, tct |)  = fstar_tc_tc g tgt in
      match back_translate_comp g c with
      | None -> raise "Unexpected comp type for atomic stmt"
      | Some st_c ->
        (| st_c, ST_Atomic g a st_c (T_TC tct) |)

assume
val open_let_binding (g:env) (s:stmt { LetBinding? s })
  : s':stmt { LetBinding? s' /\ close_let_binding s' == s}

let find_frame (g:env)
               (pre:A.term)
               (c:st_comp)
  : Meta (frame:A.term &
          st_comp_equiv g (frame_st_comp c frame)
                          ({ frame_st_comp c frame with pre }))
  = admit()


let rec elab_stmt (g:env) (s:stmt) (pre:A.term)
  : Meta (c:st_comp { c.pre == pre } & stmt_typing g s c)
  = match s with
    | Atomic a ->
      let (| c, atyping |) = elab_atomic_stmt_typing g a in
      let (| frame, equiv |) = find_frame g pre c in
      let c' = { frame_st_comp c frame with pre } in
      let st_typing = ST_Frame _ _ _ (ST_AtomicStmt _ _ _ atyping) pre frame equiv in
      (| c', st_typing |)

    | LetBinding _ _ _ ->
      let LetBinding x head body = open_let_binding g s in
      let (| head_c, t_head |) = elab_atomic_stmt_typing g head in
      let (| frame, equiv |) = find_frame g pre head_c in
      let g' = push_var g x head_c.typ in
      let head_c' = open_comp_with x head_c in
      let (| body_c, t_body |) = elab_stmt g' body (TStar head_c'.post frame) in
      let c = { body_c with pre } in
      (| c, ST_Let g x head head_c t_head pre frame equiv body body_c t_body |)

    | _ ->
      raise "NYI"
