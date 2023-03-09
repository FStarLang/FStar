module Param

open FStar.List
open FStar.Tactics

type bvmap = list (bv & (binder & binder & binder))
let fvmap =  list (fv * fv)

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

let rec zip3 (l1 : list 'a) (l2 : list 'b) (l3 : list 'c) : list ('a * 'b * 'c) =
  match l1, l2, l3 with
  | h1::t1, h2::t2, h3::t3 -> (h1, h2, h3) :: (zip3 t1 t2 t3)
  | _ -> []

let last (xs:list 'a) : Tac 'a =
  match List.Tot.rev xs with
  | h::_ -> h
  | [] -> fail "last: empty list"

(* Override it to add freshness. The code for typechecking an inductive
raises a failure if two binders of the same constructor have the same name. *)
// noeq type t = | A of x:int -> x:int -> x:int -> t
// but this doesn't fail nor warn... why??

let fresh_binder_named (nm:string) (t:typ) : Tac binder =
  // useful?
  //let n = fresh () in
  //let nm = nm ^ "_" ^ string_of_int n in
  Tactics.fresh_binder_named nm t

let app_binders (t:term) (bs:list binder) : Tac term =
  mk_e_app t (Tactics.map binder_to_term bs)

let push_bv_to_state (bv:bv) (b0 b1 b2 : binder) (s:param_state) : param_state =
  { s with bvmap = (bv, (b0, b1, b2)) :: s.bvmap }

exception NotARecFV
exception Unsupported of string
exception NotFoundBV of bv
exception NotFoundFV of fv

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

let lookup (s:param_state) (bv:bv) : Tac (binder & binder & binder) =
  let rec aux (bvm : bvmap) : Tac (binder & binder & binder) =
    match bvm with
    | [] ->
      raise (NotFoundBV bv)
    | (bv', r)::tl ->
      if compare_bv bv bv' = Order.Eq
      then r
      else aux tl
  in
  aux s.bvmap

let replace_var (s:param_state) (b:bool) (t:term) : Tac term =
  match inspect_ln t with
  | Tv_Var bv ->
    begin try
      let (x, y, _) = lookup bvmap bv in
      let bv = if b then (inspect_binder y).binder_bv else (inspect_binder x).binder_bv in
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

(* This should be definition for any eqtype. Would be nicer to see these
 * unfolded in the computed principles? *)
let param_of_eqtype (a:eqtype) : a -> a -> Type0 = (fun (x y : a) -> squash (x == y))
let int_param    = param_of_eqtype int
let bool_param   = param_of_eqtype bool
let unit_param   = param_of_eqtype unit
let string_param = param_of_eqtype string


let binder_set_qual (b:binder) (q:aqualv) : Tac binder =
  let bview = inspect_binder b in
  pack_binder {bview with binder_qual=q}

let admit_param : #a0:Type -> #a1:Type -> (#aR: (a0 -> a1 -> Type0)) ->
                  u1:unit -> u2:unit -> unit_param u1 u2 ->
                  aR (admit ()) (admit ()) =
 fun () () _ -> admit ()

let tapp q t1 t2 = pack (Tv_App t1 (t2, q))
let tabs b t : Tac term = pack (Tv_Abs b t)

let rec param' (s:param_state) (t:term) : Tac term =
  let r =
  match inspect t with
  | Tv_Type _u -> // t = Type
    `(fun (s t : (`#t)) -> s -> t -> Type)

  | Tv_Var bv ->
    let (_, _, b) = lookup s bv in
    binder_to_term b
  | Tv_Arrow b c -> //      t1 -> t2   ===  (x:t1) -> Tot t2
    begin match inspect_comp c with
    | C_Total t2 ->
      let bv, (q, _attrs) =
        let bview = inspect_binder b in
        bview.binder_bv, (bview.binder_qual, bview.binder_attrs) in

      let (s', (bx0, bx1, bxR)) = push_binder b s in

      let bf0 = fresh_binder_named "f0" (replace_by s false t) in
      let bf1 = fresh_binder_named "f1" (replace_by s true t) in
      let res = `((`#(param' s' t2)) (`#(tapp q bf0 bx0)) (`#(tapp q bf1 bx1))) in
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
    let q = inspect t in
    raise (Unsupported (term_to_string (quote q)))
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
  let nm' = ["Param_Inds"] @ [last (inspect_fv f) ^ "_param"] in
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
  | Pat_Cons fv us pats ->
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
    (s', (Pat_Cons fv us pats0,
          Pat_Cons fv us pats1,
          Pat_Cons fv' us patsr))

  | Pat_Var bv ->
    let (s', (b0, b1, bR)) = push_binder (mk_binder bv) s in
    (s', (Pat_Var (bv_of_binder b0),
          Pat_Var (bv_of_binder b1),
          Pat_Var (bv_of_binder bR)))

  | Pat_Wild bv ->
    let (s', (b0, b1, bR)) = push_binder (mk_binder bv) s in
    (s', (Pat_Wild (bv_of_binder b0),
          Pat_Wild (bv_of_binder b1),
          Pat_Wild (bv_of_binder bR)))

  | Pat_Dot_Term t ->
    fail "no dot pats"
    //let (s', (b0, b1, bR)) = push_binder (pack_binder bv Q_Explicit) s in
    //(s', (Pat_Dot_Term (bv_of_binder b0) (replace_by s' false t),
    //      Pat_Dot_Term (bv_of_binder b1) (replace_by s' true t),
    //      Pat_Dot_Term (bv_of_binder bR) (param' s' t)))

  | Pat_Constant c ->
    let b = fresh_bv_named "cR" (`_) in
    (s, (Pat_Constant c,
         Pat_Constant c,
         Pat_Wild b))

and param_br (s:param_state) (br : branch) : Tac branch =
  let (pat, t) = br in
  let (s', (_, _, pat')) = param_pat s pat in
  (pat', param' s' t)

and push_binder (b:binder) (s:param_state) : Tac (param_state & (binder & binder & binder)) =
  let (bv, (q, _)) = inspect_binder b in
  let typ = (inspect_bv bv).bv_sort in
  let name = (inspect_bv bv).bv_ppname in
  let bx0 = fresh_binder_named (name^"0") (replace_by s false typ) in
  let bx1 = fresh_binder_named (name^"1") (replace_by s true typ) in
  let bxr = fresh_binder_named (name^"R") (`(`#(param' s typ)) (`#bx0) (`#bx1)) in

  (* respect implicits *)
  let bx0 = binder_set_qual q bx0 in
  let bx1 = binder_set_qual q bx1 in
  let bxr = binder_set_qual q bxr in

  let s = push_bv_to_state bv bx0 bx1 bxr s in
  (s, (bx0, bx1, bxr))

let init_param_state : param_state = {
  bvmap = [];
  fresh = 0;
  recs  = [];
}

let param (t:term) : Tac term =
  let t = param' init_param_state t in
  //dump ("res = " ^ term_to_string t);
  t

let fv_to_tm (f:fv) : Tac term = Tv_FVar f

let param_ctor (nm_ty:name) (s:param_state) (c:ctor) : Tac ctor =
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
  //dump ("param_ctor : " ^ term_to_string (quote r));
  r

//let absN (bs : list binder) (t : term) : Tac term =
//  Tactics.Util.fold_right (fun b t -> tabs b t) bs t

let param_inductive (se:sigelt{Sg_Inductive? (inspect_sigelt se)}) (fv0 fv1 : fv) : Tac decls =
  match inspect_sigelt se with
  | Sg_Inductive nm us params typ ctors ->
    let s = push_fv fv0 fv1 init_param_state in
    let orig = app_binders (fv_to_tm (pack_fv nm)) params in
    //dump ("orig = " ^ term_to_string orig);
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
    let ctors = Tactics.map (param_ctor nm s) ctors in
    let se = Sg_Inductive (inspect_fv fv1) us param_bs typ ctors in
    //dump ("param_ind : " ^ term_to_string (quote se));
    [pack_sigelt se]

let param_letbinding (se:sigelt{Sg_Let? (inspect_sigelt se)}) (fv0 fv1 : fv) : Tac decls =
  match inspect_sigelt se with
  | Sg_Let r [lb] ->
    let lbv = inspect_lb lb in
    let rrr = param lbv.lb_typ in
    let expected_typ = norm_term [] (mk_e_app rrr [fv_to_tm fv0; fv_to_tm fv0]) in
    let se' = Sg_Let r [pack_lb {lb_fv=fv1; lb_us=lbv.lb_us ; lb_typ=expected_typ; lb_def= (param lbv.lb_def)}]
    in
    [pack_sigelt se']
  | _ -> fail "no mutual recursion"

let paramd (nm:string) : Tac decls =
  let nm' = implode_qn (cur_module () @ [last (explode_qn nm) ^ "_param"]) in
  let fv0 = pack_fv (explode_qn nm) in
  let fv1 = pack_fv (explode_qn nm') in
  let se = lookup_typ (top_env ()) (explode_qn nm) in
  match se with | None -> fail "param_letbinding: not found" | Some se ->
  let decls =
   match inspect_sigelt se with
   | Sg_Let _ _  -> param_letbinding se fv0 fv1
   | Sg_Inductive _ _ _ _ _ -> param_inductive se fv0 fv1
   | _ -> fail "paramd: unsupported sigelt"
  in
  //dump ("returning : " ^ term_to_string (quote decls));
  decls

let paramds (nms:list string) : Tac decls =
  List.Tot.flatten (map paramd nms)

(***** Unary nats *)

type nat = | Z | S of nat

%splice[nat_param; Z_param; S_param] (paramd (`%nat))

let safepred (x:nat) : nat =
  match x with
  | Z -> Z
  | S x -> x

%splice[safepred_param] (paramd (`%safepred))

(***** Pairs *)

// Universe polymorphism currently broken in tactics
let fst (#a #b : Type0) (p : a & b) : a =
  match p with
  | Mktuple2 x y -> x <: a

let snd (#a #b : Type0) (p : a & b) : b =
  match p with
  | Mktuple2 x y -> y <: b

%splice[tuple2_param] (paramd (`%tuple2))
%splice[fst_param] (paramd (`%fst))
%splice[snd_param] (paramd (`%snd))


(***** Lists *)

%splice[list_param; Nil_param; Cons_param] (paramd (`%list))

//[@@erasable]
//noeq
//type list_param (a1:Type u#aa) (a2:Type u#aa) (ar:a1 -> a2 -> Type0) : list a1 -> list a2 -> Type u#aa =
//  | Nil_param : list_param a1 a2 ar [] []
//  | Cons_param : (h1:a1) -> (h2:a2) -> (hr:ar h1 h2) ->
//                 (t1:list a1) -> (t2:list a2) -> (tr:list_param a1 a2 ar t1 t2) ->
//                 list_param a1 a2 ar (h1::t1) (h2::t2)

let safetail (#a:Type0) (x:list a) : list a =
  match x with
  | [] -> []
  | x::xs -> xs

let safetail_param_manual
  (#a #b : Type0) (#r : a -> b -> Type0)
  (l0:list a) (l1:list b) (lR : list_param a b r l0 l1)
: list_param a b r (safetail l0) (safetail l1)
// ^ needed!!!
=
  match lR with
  | Nil_param -> Nil_param
  | Cons_param _ _ _ _ _ r -> r

%splice[safetail_param] (paramd (`%safetail))


(***** Misc *)

let test0 : int = 2

%splice[test0_param] (paramd (`%test0))

let int_int_t = int -> int
%splice[int_int_t_param] (paramd (`%int_int_t))

let my_int : Type = Prims.int
%splice[my_int_param] (paramd (`%my_int))

let test1 : Type u#2 = Type u#1

[@@expect_failure] // FIXME
%splice[test1_param] (paramd (`%test1))

let test2 = bd1:Type -> bd2:Type -> bd1

[@@expect_failure] // FIXME
%splice[test2_param] (paramd (`%test2))

let id_t = #a:Type -> a -> a

[@@expect_failure] // FIXME
%splice[id_t_param] (paramd (`%id_t))

let id (#a:Type0) (x:a) : a = x
%splice[id_param] (paramd (`%id))

//let id_is_unique (f : (#a:Type -> a -> a)) (f_parametric : id_t_param f f) : Lemma (forall a (x:a). f x == x) =
//  let aux (a:Type) (x:a) : Lemma (f x == x) =
//    f_parametric (fun y () -> squash (x == y)) x () ()
//  in
//  Classical.forall_intro_2 aux

//let test () = id_is_unique id id_param

let binop_t = #a:Type -> a -> a -> a
//%splice[binop_t_param] (paramd (`%binop_t))

//let binop_is_fst_or_snd_pointwise (f : (#a:Type -> a -> a -> a)) (f_param : binop_t_param f f)
//  : Lemma (forall a (x y : a). f x y == x \/ f x y == y)
//  =
//  let aux a (x y : a) : Lemma (f x y == x \/ f x y == y) =
//   f_param (fun z () -> squash (z == x \/ z == y)) x () () y () ()
//  in
//  Classical.forall_intro_3 aux
//
//let binop_is_fst_or_snd_extensional (f : (#a:Type -> a -> a -> a)) (f_param : binop_t_param f f)
//  : Lemma ((forall a (x y : a). f x y == x) \/ (forall a (x y : a). f x y == y))
//  =
//  binop_is_fst_or_snd_pointwise f f_param;
//  assert (f 1 2 == 1 \/ f 1 2 == 2);
//  let aux1 (_ : squash (f 1 2 == 1))
//           a (x y : a) : Lemma (f x y == x) =
//   f_param (fun z i -> squash (i == 1 ==> z == x)) x 1 () y 2 ()
//  in
//  let aux2 (_ : squash (f 1 2 == 2))
//           a (x y : a) : Lemma (f x y == y) =
//   f_param (fun z i -> squash (i == 2 ==> z == y)) x 1 () y 2 ()
//  in
//  let aux1' () : Lemma (requires (f 1 2 == 1)) (ensures (forall a (x y : a). f x y == x)) =
//    Classical.forall_intro_3 (aux1 ())
//  in
//  let aux2' () : Lemma (requires (f 1 2 == 2)) (ensures (forall a (x y : a). f x y == y)) =
//    Classical.forall_intro_3 (aux2 ())
//  in
//  Classical.move_requires aux1' ();
//  Classical.move_requires aux2' ()

let test_int_to_int = int -> int
%splice [test_int_to_int_param] (paramd (`%test_int_to_int))

[@@(preprocess_with param)]
let test_list_0 = list

[@@(preprocess_with param)]
let test_list = list int

[@@(preprocess_with param)]
let rev_param = #a:Type -> list a -> list a

// GM: squash needed
let rel_of_fun #a #b (f : a -> b) : a -> b -> Type =
  fun x y -> squash (y == f x)

let rec list_rec_of_function_is_map_1 #a #b (f : a -> b) (l1 : list a) (l2 : list b)
                                            (p : list_param _ _ (rel_of_fun f) l1 l2)
        : Lemma (l2 == List.Tot.map f l1)
 = match p with
   | Nil_param -> ()
   | Cons_param _ _ _ _ _ t -> list_rec_of_function_is_map_1 _ _ _ t

let rec list_rec_of_function_is_map_2 #a #b (f : a -> b) (l1 : list a) (l2 : list b)
        : Pure (list_param _ _ (rel_of_fun f) l1 l2)
               (requires (l2 == List.Tot.map f l1))
               (ensures (fun _ -> True))
 = match l1, l2 with
   | Nil, Nil -> Nil_param
   | Cons h1 t1, Cons h2 t2 ->
     Cons_param h1 h2 () _ _ (list_rec_of_function_is_map_2 f t1 t2)

let reverse_commutes_with_map
    (rev : (#a:Type -> list a -> list a)) // doesn't really have to be "reverse"...
    (rev_is_param : rev_param rev rev)
    : Lemma (forall a b (f : a -> b) l. rev (List.Tot.map f l) == List.Tot.map f (rev l))
    =
  let aux a b f l : Lemma (rev (List.Tot.map f l) == List.Tot.map f (rev l)) =
    let rel_f : a -> b -> Type = rel_of_fun f in
    let rpf = list_rec_of_function_is_map_2 f l (List.Tot.map f l) in
    let rpf2 = rev_is_param #_ #_ #rel_f l (List.Tot.map f l) rpf in
    list_rec_of_function_is_map_1 f (rev l) (rev (List.Tot.map f l)) rpf2;
    ()
  in
  Classical.forall_intro_4 aux

let rec app (#a:Type) (l1 l2 : list a) : list a =
  match l1 with
  | [] -> l2
  | h::t -> h :: (app t l2)

let rec app_rel (#a0:Type) (#a1:Type) (aR : a0 -> a1 -> Type)
            (l11 : list a0) (l12 : list a1) (l1R : list_param _ _ aR l11 l12)
            (l21 : list a0) (l22 : list a1) (l2R : list_param _ _ aR l21 l22)
            : list_param a0 a1 aR (l11 `app` l21) (l12 `app` l22) =
   match l11, l12 with
   | [], [] -> l2R
   | h1::t1, h2::t2 ->
     begin match l1R with
     | Cons_param _ _ hr _ _ tr -> Cons_param h1 h2 hr (app t1 l21) (app t2 l22) (app_rel aR t1 t2 tr l21 l22 l2R)
     end


let rec reverse (#a:Type) (l : list a) : list a =
  match l with
  | [] -> []
  | x::xs -> reverse xs `app` [x]

let rec reverse_rel (#a0:Type) (#a1:Type) (#aR: a0 -> a1 -> Type)
                    (l0 : list a0) (l1 : list a1) (lR : list_param _ _ aR l0 l1)
                  : list_param _ _ aR (reverse l0) (reverse l1) =
  match l0, l1 with
  | [], [] -> Nil_param
  | h1::t1, h2::t2 ->
    begin match lR with
    | Cons_param _ _ hr _ _ tr ->
    app_rel aR (reverse t1) (reverse t2) (reverse_rel t1 t2 tr)
               [h1] [h2] (Cons_param h1 h2 hr Nil Nil Nil_param)
    end

(* Doesn't work by SMT, and tactic above does not handle fixpoints.
 * What to do about them? Is there a translation for general recursion?
 * Should read https://openaccess.city.ac.uk/id/eprint/1072/1/PFF.pdf in
 * more detail. *)
(* ^ stale comment, using inductive proofs right now *)

let real_reverse_commutes_with_map ()
  : Lemma (forall a b (f : a -> b) l. reverse (List.Tot.map f l) == List.Tot.map f (reverse l))
  = reverse_commutes_with_map reverse reverse_rel

(* 2020/07/23: This doesn't work from outside this module... why? *)

type label =
  | Low
  | High

%splice[label_param] (paramd (`%label))

noeq type labeled_interface : Type u#(1 + a) = {
  labeled : Type u#a -> Type u#a;
  mk_labeled : #a:Type u#a -> a -> label -> labeled a;
  label_of : #a:Type u#a -> labeled a -> label;
}

%splice[labeled_interface_param] (paramd (`%labeled_interface))

// From here onwards, every u#0 should be an u#a

let proj_labeled (r:labeled_interface u#0) : Type u#0 -> Type u#0 =
  match r with
  | Mklabeled_interface l m lo -> l

let proj_mk_labeled (r:labeled_interface u#0) : #a:Type u#0 -> a -> label -> (proj_labeled r) a =
  match r with
  | Mklabeled_interface l m lo -> m

let proj_label_of (r:labeled_interface u#0) : #a:Type u#0 -> (proj_labeled r) a -> label =
  match r with
  | Mklabeled_interface l m lo -> lo

%splice[proj_labeled_param] (paramd (`%proj_labeled))

%splice[proj_mk_labeled_param] (paramd (`%proj_mk_labeled))

%splice[proj_label_of_param] (paramd (`%proj_label_of))

let lab_impl : labeled_interface = {
  labeled = (fun (a:Type) -> a * label);
  mk_labeled = (fun (#a:Type) (x:a) (l:label) -> (x,l));
  label_of = (fun (#a:Type) x -> snd x);
}

%splice[lab_impl_param] (paramd (`%lab_impl))
