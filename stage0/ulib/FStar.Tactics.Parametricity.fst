module FStar.Tactics.Parametricity

open FStar.List
open FStar.Tactics.V2.Bare

type bvmap = list (namedv & (binder & binder & binder))
let fvmap =  list (fv & fv)

noeq
type param_state = {
  bvmap : bvmap;
  fresh : int;
  recs  : fvmap;
}

let rec fold_right2 (f : 'a -> 'b -> 'c -> Tac 'c) (l1:list 'a) (l2:list 'b) (c:'c) : Tac 'c =
  match l1, l2 with
  | h1::t1, h2::t2 -> f h1 h2 (fold_right2 f t1 t2 c)
  | [], [] -> c
  | _ -> fail "fold_right2"

let rec zip3 (l1 : list 'a) (l2 : list 'b) (l3 : list 'c) : list ('a & 'b & 'c) =
  match l1, l2, l3 with
  | h1::t1, h2::t2, h3::t3 -> (h1, h2, h3) :: (zip3 t1 t2 t3)
  | _ -> []

let last (xs:list 'a) : Tac 'a =
  match List.Tot.rev xs with
  | h::_ -> h
  | [] -> fail "last: empty list"

(* Override it to add freshness. The code for typechecking an inductive
raises a failure if two binders of the same constructor have the same name. *)
//noeq type t = | A of x:int -> x:int -> x:int -> t
// but this doesn't fail nor warn... why??

let app_binders (t:term) (bs:list binder) : Tac term =
  mk_e_app t (List.Tot.map binder_to_term bs)

let push_var_to_state (v:namedv) (b0 b1 b2 : binder) (s:param_state) : param_state =
  { s with bvmap = (v, (b0, b1, b2)) :: s.bvmap }

exception NotARecFV
exception NotFoundBV of namedv

let lookup_rec_fv (s:param_state) (f:fv) : Tac fv =
  let rec aux (m:fvmap) : Tac fv =
    match m with
    | [] -> raise NotARecFV
    | (f1, k)::fs -> if compare_fv f f1 = Order.Eq
                   then k
                   else aux fs
  in
  aux s.recs

let push_fv (f1 f2 : fv) (s:param_state) : param_state =
 { s with recs = (f1,f2)::s.recs }

let lookup (s:param_state) (v:namedv) : Tac (binder & binder & binder) =
  let rec aux (bvm : bvmap) : Tac (binder & binder & binder) =
    match bvm with
    | [] ->
      raise (NotFoundBV v)
    | (v', r)::tl ->
      if (inspect_namedv v).uniq = (inspect_namedv v').uniq
      then r
      else aux tl
  in
  aux s.bvmap

let replace_var (s:param_state) (b:bool) (t:term) : Tac term =
  match inspect t with
  | Tv_Var v ->
    begin try
      let (x, y, _) = lookup s v in
      let bv = binder_to_namedv (if b then y else x) in
      pack (Tv_Var bv)
    with
    (* Maybe we traversed a binder and there are variables not in the state.
     * The right thing here would be to track them... but this should do for now. *)
    | NotFoundBV _ -> t
    | e -> raise e
    end
  | _ -> t

let replace_by (s:param_state) (b:bool) (t:term) : Tac term =
  let r = visit_tm (replace_var s b) t in
  //print ("rep " ^ string_of_bool b ^ " " ^ term_to_string t ^ " = " ^ term_to_string r);
  r

let tapp q t1 t2 = pack (Tv_App t1 (t2, q))
let tabs b t : Tac term = pack (Tv_Abs b t)

let rec param' (s:param_state) (t:term) : Tac term =
  let r =
  match inspect t with
  | Tv_Type _u -> // t = Type
    (* It's this: 
        `(fun (s r : (`#t)) -> s -> r -> Type)
      just working around extraction bug. *)
    let s = fresh_binder_named "s" t in
    let r = fresh_binder_named "r" t in
    let xs = fresh_binder_named "xs" (Tv_Var s) in
    let xr = fresh_binder_named "xr" (Tv_Var r) in
    pack <| Tv_Abs s <| Tv_Abs r <| Tv_Arrow xs (C_Total <| Tv_Arrow xr (C_Total <| Tv_Type Uv_Unk))

  | Tv_Var bv ->
    let (_, _, b) = lookup s bv in
    binder_to_term b

  | Tv_Arrow b c -> //      t1 -> t2   ===  (x:t1) -> Tot t2
    begin match inspect_comp c with
    | C_Total t2 ->
      let (s', (bx0, bx1, bxR)) = push_binder b s in
      let q = b.qual in

      let bf0 = fresh_binder_named "f0" (replace_by s false t) in
      let bf1 = fresh_binder_named "f1" (replace_by s true t) in
      let b2t = binder_to_term in
      let res = `((`#(param' s' t2)) (`#(tapp q (b2t bf0) (b2t bx0))) (`#(tapp q (b2t bf1) (b2t bx1)))) in
      tabs bf0 (tabs bf1 (mk_tot_arr [bx0; bx1; bxR] res))
    | _ -> raise (Unsupported "effects")
    end

  | Tv_App l (r, q) ->
    let lR = param' s l in
    let l0 = replace_by s false r in
    let l1 = replace_by s true r in
    let rR = param' s r in
    mk_app lR [(l0, q); (l1, q); (rR, q)]

 | Tv_Abs b t ->
    let abs b t : Tac term = pack (Tv_Abs b t) in
    let (s', (bx0, bx1, bxR)) = push_binder b s in

    let t = param' s' t in
    abs bx0 (abs bx1 (abs bxR t))

  | Tv_Match t None brs ->
    pack (Tv_Match (param' s t) None (map (param_br s) brs))

  | Tv_UInst fv _
  | Tv_FVar fv ->
    pack (Tv_FVar (param_fv s fv))

  | Tv_Const c ->
    `()

  | Tv_AscribedT t _ _ _
  | Tv_AscribedC t _ _ _ -> param' s t

  | _ ->
    raise (Unsupported (Tactics.Print.term_to_ast_string t))
  in
  r

and param_fv (s:param_state) (f : fv) : Tac fv =
  (* first of all look for recursive knots *)
  try lookup_rec_fv s f
  with
  | _ ->

  (* try to get it from the same module the FV is defined *)
  let nm' = explode_qn (implode_qn (inspect_fv f) ^ "_param") in
  //dump ("nm' = " ^ implode_qn nm');
  match lookup_typ (top_env ()) nm' with
  | Some se' -> pack_fv nm'
  | None ->

  (* or this module, where the translation is defined... *)
  let nm' = ["FStar"; "Tactics"; "Parametricity"; last (inspect_fv f) ^ "_param"] in
  //dump ("nm' = " ^ implode_qn nm');
  match lookup_typ (top_env ()) nm' with
  | Some se' -> pack_fv nm'
  | None ->

  (* otherwise, try to get it from the *current* module, where we're running the tactic *)
  let nm' = cur_module () @ [last (inspect_fv f) ^ "_param"] in
  //dump ("nm' = " ^ implode_qn nm');
  match lookup_typ (top_env ()) nm' with
  | Some se' -> pack_fv nm'

  (* TODO: lookup in env *)

  | None ->
    raise (NotFoundFV f)

and param_pat (s:param_state) (p : pattern) : Tac (param_state & (pattern & pattern & pattern)) =
  let is_dot_pat (p:pattern) : Tac bool =
    match p with
    | Pat_Dot_Term _ -> true
    | _ -> false
  in
  //dump ("param_pat of " ^ term_to_string (quote p));
  match p with
  | Pat_Cons {head=fv; univs=us; subpats=pats} ->
    let fv' = param_fv s fv in
    let (s', (pats0, pats1, patsr)) =
      fold_left (fun (s, (pats0, pats1, patsr)) (p, i) ->
                    if is_dot_pat p then (s, (pats0, pats1, patsr))
                    else
                    let (s', (p0, p1, pr)) = param_pat s p in
                    (s', (
                         (p0,i)::pats0,
                         (p1,i)::pats1,
                         (pr,false)::(p1,i)::(p0,i)::patsr)))
                 (s, ([], [], []))
                 pats
    in
    let pats0 = List.Tot.rev pats0 in
    let pats1 = List.Tot.rev pats1 in
    let patsr = List.Tot.rev patsr in
    (s', (Pat_Cons {head=fv;  univs=us; subpats=pats0},
          Pat_Cons {head=fv;  univs=us; subpats=pats1},
          Pat_Cons {head=fv'; univs=us; subpats=patsr}))

  | Pat_Var {v; sort} ->
    let b = namedv_to_binder v (unseal sort) in
    let (s', (b0, b1, bR)) = push_binder b s in
    (s', (Pat_Var {v=binder_to_namedv b0; sort = Sealed.seal (binder_sort b0)},
          Pat_Var {v=binder_to_namedv b1; sort = Sealed.seal (binder_sort b1)},
          Pat_Var {v=binder_to_namedv bR; sort = Sealed.seal (binder_sort bR)}))

  | Pat_Dot_Term t ->
    fail "no dot pats"
    //let (s', (b0, b1, bR)) = push_binder (pack_binder bv Q_Explicit) s in
    //(s', (Pat_Dot_Term (bv_of_binder b0) (replace_by s' false t),
    //      Pat_Dot_Term (bv_of_binder b1) (replace_by s' true t),
    //      Pat_Dot_Term (bv_of_binder bR) (param' s' t)))

  | Pat_Constant c ->
    let b = fresh_binder_named "cR" (`_) in
    (s, (Pat_Constant c,
         Pat_Constant c,
         Pat_Var {v=binder_to_namedv b; sort=seal (`_)}))

and param_br (s:param_state) (br : branch) : Tac branch =
  let (pat, t) = br in
  let (s', (_, _, pat')) = param_pat s pat in
  (pat', param' s' t)

and push_binder (b:binder) (s:param_state) : Tac (param_state & (binder & binder & binder)) =
  let q = b.qual in
  let typ = b.sort in
  let name = unseal b.ppname in
  let decor (s : string) (t : string) : Tac string = (s ^ t) in
  let bx0 = fresh_binder_named (decor name "0") (replace_by s false typ) in
  let bx1 = fresh_binder_named (decor name "1") (replace_by s true typ) in
  let bxr = fresh_binder_named (decor name "R") (`(`#(param' s typ)) (`#(binder_to_term bx0)) (`#(binder_to_term bx1))) in

  (* respect implicits *)
  let bx0 = { bx0 with qual = q } in
  let bx1 = { bx1 with qual = q } in
  let bxr = { bxr with qual = q } in

  let s = push_var_to_state (binder_to_namedv b) bx0 bx1 bxr s in
  (s, (bx0, bx1, bxr))

let init_param_state : param_state = {
  bvmap = [];
  fresh = 0;
  recs  = [];
}

[@@plugin]
let param (t:term) : Tac term =
  let t = param' init_param_state t in
  //dump ("res = " ^ term_to_string t);
  t

let fv_to_tm (f:fv) : Tac term = pack (Tv_FVar f)

let param_ctor (nm_ty:name) (s:param_state) (c:ctor) : Tac ctor =
  (* dump ("ctor0: " ^ term_to_string (quote c)); *)
  let nm, ty = c in
  let nm' = cur_module () @ [last nm ^ "_param"] in
  let bs, c = collect_arr_bs ty in

  let orig = app_binders (fv_to_tm (pack_fv nm)) bs in

  let (s, bs) =
      fold_left (fun (s, bvs) b -> let (s, (bx0, bx1, bxr)) = push_binder b s in
                                (s, bxr::bx1::bx0::bvs)) (s, []) bs
  in
  let bs = List.Tot.rev bs in

  let cod =
    match inspect_comp c with
    | C_Total ty -> ty
    | _ -> fail "param_ctor got a non-tot comp"
  in

  let cod = mk_e_app (param' s cod) [replace_by s false orig; replace_by s true orig] in

  let ty' = mk_tot_arr bs cod in

  let r = (nm', ty') in
  (* dump ("ctor1: " ^ term_to_string (quote r)); *)
  r

//let absN (bs : list binder) (t : term) : Tac term =
//  Tactics.Util.fold_right (fun b t -> tabs b t) bs t

let param_inductive (se:sigelt) (fv0 fv1 : fv) : Tac decls =
  match inspect_sigelt se with
  | Sg_Inductive {nm; univs; params; typ; ctors} ->
    (* dump ("typ = " ^ term_to_string typ); *)
    let s = push_fv fv0 fv1 init_param_state in
    let orig = app_binders (fv_to_tm (pack_fv nm)) params in
    (* dump ("orig = " ^ term_to_string orig); *)
    let (s, param_bs) =
        fold_left (fun (s, bvs) b -> let (s, (bx0, bx1, bxr)) = push_binder b s in
                                  //dump ("bx0 = " ^ term_to_string (quote bx0));
                                  //dump ("bx1 = " ^ term_to_string (quote bx1));
                                  //dump ("bxr = " ^ term_to_string (quote bxr));
                                  (s, bxr::bx1::bx0::bvs)) (s, []) params
    in
    let param_bs = List.Tot.rev param_bs in
    //Tactics.Util.iter (fun bv -> dump ("param bv = " ^ binder_to_string bv)) param_bs;
    let typ = mk_e_app (param' s typ) [replace_by s false orig; replace_by s true orig] in
    (* dump ("new typ = " ^ term_to_string typ); *)
    let ctors = Tactics.Util.map (param_ctor nm s) ctors in
    let se = Sg_Inductive {nm=inspect_fv fv1; univs; params=param_bs; typ; ctors} in
    (* dump ("param_ind : " ^ term_to_string (quote se)); *)
    [pack_sigelt se]
  | _ -> fail ""

let param_letbinding (se:sigelt) (fv0 fv1 : fv) : Tac decls =
  match inspect_sigelt se with
  | Sg_Let {isrec=r; lbs=[lb]} ->
    let rrr = param lb.lb_typ in
    let expected_typ = norm_term [] (mk_e_app rrr [fv_to_tm fv0; fv_to_tm fv0]) in
    let se' = Sg_Let {isrec=r; lbs=[{lb_fv=fv1; lb_us=lb.lb_us ; lb_typ=expected_typ; lb_def= (param lb.lb_def)}]} in
    [pack_sigelt se']
  | _ -> fail "no mutual recursion"

[@@plugin]
let paramd (nm:string) : Tac decls =
  let nm' = implode_qn (cur_module () @ [last (explode_qn nm) ^ "_param"]) in
  let fv0 = pack_fv (explode_qn nm) in
  let fv1 = pack_fv (explode_qn nm') in
  let se = lookup_typ (top_env ()) (explode_qn nm) in
  match se with | None -> fail "param_letbinding: not found" | Some se ->
  let decls =
   match inspect_sigelt se with
   | Sg_Let _ -> param_letbinding se fv0 fv1
   | Sg_Inductive _ -> param_inductive se fv0 fv1
   | _ -> fail "paramd: unsupported sigelt"
  in
  //dump ("returning : " ^ term_to_string (quote decls));
  decls

[@@plugin]
let paramds (nms:list string) : Tac decls =
  List.Tot.flatten (map paramd nms)
