module FStar.Tactics.PrettifyType

(* The single thing you should call here is entry function,
as the body of a splice. We could make this a plugin eventually,
not doing it now to now complicate the build (and this is pretty
fast anyway). *)

open FStar.Tactics.V2.Bare
open FStar.List.Tot { (@), unsnoc }

let add_suffix (s:string) (nm:name) : name =
  explode_qn (implode_qn nm ^ s)

let add_prefix (s:string) (nm:name) : name =
  assume (List.length nm > 0);
  let first, last = unsnoc nm in
  first @ [s ^ last]

noeq
type prod_type =
  | Prod : list (string & atom) -> prod_type

noeq
type flat_type =
  | Sum : list (string & prod_type) -> flat_type

(* State for a run of the tactic, after parsing and flattening the type. *)
noeq
type cfg_t = {
  at : parsed_type;
  fat : flat_type;
  orig_tynm : name;
  pretty_tynm : name;
  ctors : list ctor;
}

let rec parsed_type_to_string (t:parsed_type) : Tac string =
  match t with
  | Atom t -> term_to_string t
  | Tuple2 a b ->
    "(" ^ parsed_type_to_string a ^ ", " ^ parsed_type_to_string b ^ ")"
  | Either a b ->
    "(" ^ parsed_type_to_string a ^ " + " ^ parsed_type_to_string b ^ ")"
  | Named s a ->
    "(" ^ s ^ ": " ^ parsed_type_to_string a ^ ")"

let rec parse_prod_type (t:term) : Tac parsed_type =
  let hd, args = collect_app t in
  match inspect hd, args with
  | Tv_UInst fv _, [(a1, Q_Explicit); (a2, Q_Explicit)]
  | Tv_FVar fv, [(a1, Q_Explicit); (a2, Q_Explicit)] -> (
    match inspect a1 with
    | Tv_Const (C_String s) ->
      Named s (parse_prod_type a2)
    | _ ->
      if inspect_fv fv = explode_qn (`%tuple2) then
        Tuple2 (parse_prod_type a1) (parse_prod_type a2)
      else
        Atom t
  )
  | _ ->
    Atom t

let rec parse_sum_type (t:term) : Tac parsed_type =
  let hd, args = collect_app t in
  match inspect hd, args with
  | Tv_UInst fv _, [(a1, Q_Explicit); (a2, Q_Explicit)]
  | Tv_FVar fv, [(a1, Q_Explicit); (a2, Q_Explicit)] -> (
    match inspect a1 with
    | Tv_Const (C_String s) ->
      Named s (parse_sum_type a2)
    | _ ->
      if inspect_fv fv = explode_qn (`%either) then
        Either (parse_sum_type a1) (parse_sum_type a2)
      else
        parse_prod_type t
  )
  | _ ->
    parse_prod_type t

let parse_type = parse_sum_type

let prod_type_to_string (t:prod_type) : Tac string =
  match t with
  | Prod ts ->
    let ts = ts |> Tactics.Util.map (fun (s,t) -> s ^ ":" ^ term_to_string t) in
    "{" ^ String.concat "; " ts ^ "}"

let flat_type_to_string (t:flat_type) : Tac string =
  match t with
  | Sum ts ->
    let ts = ts |> Tactics.Util.map (fun (s,t) -> s ^ " of " ^ prod_type_to_string t) in
    "(" ^ String.concat " | " ts ^ ")"

let rec as_prod_type (ctr:nat) (t : parsed_type) : Tac (nat & prod_type) =
  match t with
  | Tuple2 a b ->
    let ctr, Prod aa = as_prod_type ctr a in
    let ctr, Prod bb = as_prod_type ctr b in
    ctr, Prod (aa @ bb)
  | Named s (Atom t) ->
    ctr, Prod [(s,t)]
  | Atom t ->
    ctr+1, Prod [("_x" ^ string_of_int ctr, t)]
  | Either _ _ -> fail "as_prod_type: not a product type"
  | Named _ t -> as_prod_type ctr t

let rec flatten_type (pretty_tynm : name) (ctr:nat) (t:parsed_type) : Tac (nat & flat_type) =
  match t with
  | Either a b ->
    let ctr, Sum aa = flatten_type pretty_tynm ctr a in
    let ctr, Sum bb = flatten_type pretty_tynm ctr b in
    ctr, Sum (aa @ bb)
  | Named s t ->
    let _, p = as_prod_type 0 t in
    assume (List.length pretty_tynm > 0);
    let _, s0 = unsnoc pretty_tynm in
    ctr, Sum [("Mk" ^ s0 ^ "_" ^ s, p)]
  | t ->
    let _, p = as_prod_type 0 t in
    assume (List.length pretty_tynm > 0);
    let _, s = unsnoc pretty_tynm in
    ctr+1, Sum ["Mk" ^ s ^ string_of_int ctr, p]

// let unitv_                 : term = `()
// let unitt_                 : term = `(unit)
// let empty_                 : term = `(empty)
// let either_ (a b : term)   : term = `(either (`#a) (`#b))
// let tuple2_ (a b : term)   : term = `(tuple2 (`#a) (`#b))
// let mktuple2_ (a b : term) : term = `(Mktuple2 (`#a) (`#b))

let get_typ_def (nm : name) : Tac term =
  let e = top_env () in
  let se = lookup_typ e nm in
  match se with
  | None -> fail "ctors_of_typ: type not found"
  | Some se -> (
    let sev = inspect_sigelt se in
    match sev with
    | Sg_Let {lbs=[lb]} -> lb.lb_def
    | _ ->
      fail "get_typ_def: not a let binding?"
  )

let mk_ctor (tynm : name) (s:string) (fat : prod_type) : Tac ctor =
  let Prod fields = fat in
  let bs = fields |> Tactics.Util.map
    (function (s, f) -> let b = fresh_binder f in { b with ppname = Sealed.seal s })
  in
  let nm =
    assume (List.length tynm > 0);
    let mod, _ = unsnoc tynm in
    let nm = mod @ [s] in
    nm
    // let
    // add_prefix "Mk" tynm |> add_suffix (string_of_int i)
  in
  let ty = mk_tot_arr bs (pack (Tv_FVar (pack_fv tynm))) in
  nm, ty

(* Returns a singleton list with the definition of the fancy type. And the constructors
to be used by other calls. *)
let mk_fancy_type (cfg : cfg_t) : Tac decls =
  let sv = Sg_Inductive {
   nm = cfg.pretty_tynm;
   univs = [];
   params = [];
   typ = (`Type0);
   ctors = cfg.ctors;
  } in
  let se = pack_sigelt sv in
  [se]

let rec parsed_type_pat (at : parsed_type) : Tac (pattern & binders) =
  match at with
  | Atom t ->
    let b = fresh_binder t <: binder in
    Pat_Var { v=b; sort = Sealed.seal (`_) }, [b]
  | Tuple2 a b ->
    let p1, bs1 = parsed_type_pat a in
    let p2, bs2 = parsed_type_pat b in
    let mktuple2 = pack_fv (explode_qn (`%Mktuple2)) in
    let p =
      Pat_Cons {
        head = mktuple2;
        univs = None;
        subpats = [(p1, false); (p2, false)];
      }
    in
    p, bs1 @ bs2
  | Named _ t -> parsed_type_pat t
  | _ ->
    fail "should not happen: parsed_type_pat: not a product type"

let rec parsed_type_expr (at : parsed_type) (bs : binders) : Tac (term & binders) =
  // print ("parsed_type_expr of " ^ parsed_type_to_string at
  //   ^ " with len bs: " ^  string_of_int (List.length bs));
  match at with
  | Atom t ->
    guard (not (Nil? bs));
    let b::bs = bs in
    pack (Tv_Var b), bs
  | Tuple2 a b ->
    let e1, bs = parsed_type_expr a bs in
    let e2, bs = parsed_type_expr b bs in
    let mktuple2 = pack_fv (explode_qn (`%Mktuple2)) in
    let e : term = mk_e_app (Tv_FVar mktuple2) [e1; e2] in
    e, bs
  | Named _ t -> parsed_type_expr t bs
  | _ ->
    fail "should not happen: parsed_type_expr: not a product type"

let mk_right_case (cfg : cfg_t) (i : nat{i < List.Tot.length cfg.ctors}) (at : parsed_type) : Tac branch =
  let p, bs = parsed_type_pat at in
  let ctor_nm, _ = List.Tot.index cfg.ctors i in
  let body = pack (Tv_FVar (pack_fv ctor_nm)) in
  let body = mk_e_app body (Tactics.Util.map (fun (b:binder) -> pack (Tv_Var b)) bs) in
  p, body

let rec mk_right_body (cfg:cfg_t) (at : parsed_type) (i : nat) (sc : term) : Tac (nat & term) =
  match at with
  | Either l r ->
    let v1 = fresh_binder (`_) in
    let v2 = fresh_binder (`_) in
    let pat_inl = Pat_Cons {
      head = pack_fv (explode_qn (`%Inl));
      univs = None;
      subpats = [(Pat_Var {v=v1; sort=Sealed.seal (`_)}, false)];
    } in
    let pat_inr = Pat_Cons {
      head = pack_fv (explode_qn (`%Inr));
      univs = None;
      subpats = [(Pat_Var {v=v2; sort=Sealed.seal (`_)}, false)];
    } in
    let i, body1 = mk_right_body cfg l i (pack (Tv_Var v1)) in
    let br1 = pat_inl, body1 in
    let i, body2 = mk_right_body cfg r i (pack (Tv_Var v2)) in
    let br2 = pat_inr, body2 in
    let brs = [br1; br2] in
    i, pack (Tv_Match sc None brs)
  | _ ->
    (* Single case match. *)
    assume (i < List.Tot.length cfg.ctors);
    let branch = mk_right_case cfg i at in
    i+1, pack (Tv_Match sc None [branch])

let mk_right (cfg:cfg_t) : Tac decls =
  let b = fresh_binder (pack (Tv_FVar (pack_fv cfg.orig_tynm))) in
  let sv = Sg_Let {
    isrec = false;
    lbs = [
      {
        lb_fv = pack_fv (add_suffix "_right" cfg.pretty_tynm);
        lb_us = [];
        lb_typ = mk_tot_arr [b]
                            (pack (Tv_FVar (pack_fv cfg.pretty_tynm)));
        lb_def = mk_abs [b] (snd <| mk_right_body cfg cfg.at 0 (pack (Tv_Var b)));
      }
    ]
  }
  in
  [pack_sigelt sv]

let mk_left_case (cfg:cfg_t) (i : nat{i < List.Tot.length cfg.ctors}) (at : parsed_type) : Tac branch =
  let p, bs = parsed_type_pat at in
  let ctor_nm, _ = List.Tot.index cfg.ctors i in
  let body = pack (Tv_FVar (pack_fv ctor_nm)) in
  let body = mk_e_app body (Tactics.Util.map (fun (b:binder) -> pack (Tv_Var b)) bs) in
  p, body

let rec mk_left_branches (ff : term -> Tac term) (ctors : list ctor) (at : parsed_type) : Tac (list ctor & list (pattern & term))=
  match at with
  | Either l r ->
    let inl (t:term) : term = mk_e_app (Tv_FVar (pack_fv (explode_qn (`%Inl)))) [t] in
    let inr (t:term) : term = mk_e_app (Tv_FVar (pack_fv (explode_qn (`%Inr)))) [t] in
    let ctors, brs1 = mk_left_branches (fun t -> ff (inl t)) ctors l in
    let ctors, brs2 = mk_left_branches (fun t -> ff (inr t)) ctors r in
    ctors, brs1 @ brs2
  | _ ->
    guard (not (Nil? ctors));
    let (c_nm, c_ty)::ctors = ctors in

    let bs, _ = collect_arr c_ty in
    let bs = bs |> Tactics.Util.map (fun b -> fresh_binder b <: binder) in
    let p = Pat_Cons {
      head = pack_fv c_nm;
      univs = None;
      subpats = Tactics.Util.map (fun (b:binder) -> Pat_Var {v=b; sort=Sealed.seal (`_)}, false) bs;
    } in
    let body, rest_bs = parsed_type_expr at bs in
    let body = ff body in
    guard (Nil? rest_bs);
    (* Single case match. *)
    ctors, [(p ,body)]

let mk_left_body cfg (sc : term) : Tac term =
  let ctors, brs = mk_left_branches (fun t -> t) cfg.ctors cfg.at in
  guard (Nil? ctors);
  pack (Tv_Match sc None brs)

let mk_left (cfg : cfg_t) : Tac decls =
  let b = fresh_binder (pack (Tv_FVar (pack_fv cfg.pretty_tynm))) in
  let sv = Sg_Let {
    isrec = false;
    lbs = [
      {
        lb_fv = pack_fv (add_suffix "_left" cfg.pretty_tynm);
        lb_us = [];
        lb_typ = mk_tot_arr [fresh_binder (pack (Tv_FVar (pack_fv cfg.pretty_tynm)))]
                            (pack (Tv_FVar (pack_fv cfg.orig_tynm)));
        lb_def = mk_abs [b] (mk_left_body cfg (Tv_Var b));
      }
    ]
  }
  in
  [pack_sigelt sv]

(* In this case we are matching something of the flat type.
We must follow the structure of the type in order to match
deeply enough. *)
let rec prove_left_right_aux (at : parsed_type) (m : term) (k : unit -> Tac unit) : Tac unit =
  match at with
  | Atom _ -> k ()
  | Either l r ->
    let cases = t_destruct m in
    guard (List.length cases = 2);
    Util.zip cases [l;r] |> Util.iter #((_ & nat) & _) (fun ((c, n), at') ->
      focus fun () ->
        let bs : list binding = repeatn n intro in
        guard (List.length bs = 1);
        let [b] = bs in
        let b_eq = intro () in
        rewrite b_eq;
        prove_left_right_aux at' b k
    )

  | Tuple2 l r ->
    let cases = t_destruct m in
    guard (List.length cases = 1);
    let [(_, n)] = cases in
    guard (n = 2);
    let bs : list binding = repeatn n intro in
    let [b1;b2] = bs in
    let b_eq = intro () in
    rewrite b_eq;
    prove_left_right_aux l b1 (fun () ->
      prove_left_right_aux r b2 k);
    ()

  (* Nothing special *)
  | Named _ t -> prove_left_right_aux t m k

[@@plugin]
let prove_left_right at =
  let b = intro () in
  prove_left_right_aux at b trefl;
  ()

(* Just match on the pretty type and trefl. *)
[@@plugin]
let prove_right_left () : Tac unit =
  let b = intro () in
  let cases = t_destruct b in
  cases |> Util.iter #(_ & nat) (fun (c, n) ->
    focus fun () ->
      // dump "case";
      let bs = repeatn n intro in
      let b_eq = intro () in
      rewrite b_eq;
      trefl ();
      qed ()
  )

let rec quote_at (at : parsed_type) : Tac term =
  match at with
  | Atom t ->
    mk_e_app (`Atom) [(`fakeunit)]
    // hacky, but it doesn't matter since we only need the shape of this tree.
  | Tuple2 a b ->
    mk_e_app (`Tuple2) [quote_at a; quote_at b]
  | Named s t ->
    mk_e_app (`Named) [pack (Tv_Const (C_String s)); quote_at t]
  | Either a b ->
    mk_e_app (`Either) [quote_at a; quote_at b]

let mk_left_right cfg : Tac decls =
  let b = fresh_binder (pack (Tv_FVar (pack_fv cfg.orig_tynm))) in
  let tm_left  : term = Tv_FVar <| pack_fv (add_suffix "_left" cfg.pretty_tynm) in
  let tm_right : term = Tv_FVar <| pack_fv (add_suffix "_right" cfg.pretty_tynm) in
  let sv = Sg_Let {
    isrec = false;
    lbs = [
      {
        lb_fv = pack_fv (add_suffix "_left_right" cfg.pretty_tynm);
        lb_us = [];
        lb_typ =
          mk_tot_arr
            [b]
            (`(f_inverses (`#tm_left) (`#tm_right) (`#b)));
        lb_def = (`(_ by (prove_left_right (`#(quote_at cfg.at)))));
      }
    ]
  }
  in
  [pack_sigelt sv]

let mk_right_left cfg : Tac decls =
  let b = fresh_binder (pack (Tv_FVar (pack_fv cfg.pretty_tynm))) in
  let tm_left  : term = Tv_FVar <| pack_fv (add_suffix "_left" cfg.pretty_tynm) in
  let tm_right : term = Tv_FVar <| pack_fv (add_suffix "_right" cfg.pretty_tynm) in
  let bt : term = b in
  let sv = Sg_Let {
    isrec = false;
    lbs = [
      {
        lb_fv = pack_fv (add_suffix "_right_left" cfg.pretty_tynm);
        lb_us = [];
        lb_typ =
          mk_tot_arr
            [b]
            (`(f_inverses (`#tm_right) (`#tm_left) (`#bt)));
        lb_def = (`(_ by (prove_right_left ())));
      }
    ]
  }
  in
  [pack_sigelt sv]

let mk_bij cfg : Tac decls =
  let sv = Sg_Let {
    isrec = false;
    lbs = [
      {
        lb_fv = pack_fv (add_suffix "_bij" cfg.pretty_tynm);
        lb_us = [];
        lb_typ =
          (`(FStar.Bijection.bijection
              (`#(Tv_FVar (pack_fv cfg.orig_tynm)))
              (`#(Tv_FVar (pack_fv cfg.pretty_tynm)))
            ));
        lb_def =
          mk_e_app (`FStar.Bijection.mk_bijection)
            [
             pack <| Tv_FVar (pack_fv (add_suffix "_right" cfg.pretty_tynm));
             pack <| Tv_FVar (pack_fv (add_suffix "_left" cfg.pretty_tynm));
             pack <| Tv_FVar (pack_fv (add_suffix "_right_left" cfg.pretty_tynm));
             pack <| Tv_FVar (pack_fv (add_suffix "_left_right" cfg.pretty_tynm));
           ];
      }
    ]
  }
  in
  [pack_sigelt sv]

[@@plugin]
let entry (pretty_tynm nm : string) : Tac decls =
  // print ("ENTRY, n quals = " ^ string_of_int (List.length (splice_quals ())));
  // print ("ENTRY, n attrs = " ^ string_of_int (List.length (splice_attrs ())));
  let quals = splice_quals () in
  let attrs = splice_attrs () in

  let nm = explode_qn nm in
  let def = get_typ_def nm in
  // print ("def: " ^ term_to_string def);
  let at = parse_type def in
  // print ("at: " ^ parsed_type_to_string at);
  assume (List.length nm > 0);
  let qns, _ = unsnoc nm in
  let pretty_tynm = qns @ [pretty_tynm] in
  let _, fat = flatten_type pretty_tynm 0 at in
  // print ("fat: " ^ flat_type_to_string fat);

  let Sum cases = fat in
  let ctors = cases |> map (fun (s, p) -> mk_ctor pretty_tynm s p) in
  let cfg = {
    at = at;
    fat = fat;
    orig_tynm = nm;
    pretty_tynm = pretty_tynm;
    ctors = ctors;
  } in

  let tds = mk_fancy_type cfg in
  let ds = mk_right cfg in
  let ds = ds @ mk_left cfg in
  let ds = ds @ mk_left_right cfg in
  let ds = ds @ mk_right_left cfg in
  // let ds = ds @ mk_bij cfg in
  let post_type (se : sigelt) : Tac sigelt =
    let quals = filter (fun q -> not (Unfold_for_unification_and_vcgen? q)) quals in
    let se = set_sigelt_quals quals se in
    let se = set_sigelt_attrs attrs se in
    se
  in
  let post_other (se : sigelt) : Tac sigelt =
    let quals = filter (fun q -> not (Noeq? q || Unopteq? q)) quals in
    let se = set_sigelt_quals quals se in
    let attrs = attrs @ [`"KrmlPrivate"] in
    let se = set_sigelt_attrs attrs se in
    se
  in
  map post_type tds @ map post_other ds
