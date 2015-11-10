#light "off"
module FStar.Tests.Test

open FStar
open FStar.Util
open FStar.Absyn
open FStar.Syntax.Syntax
open FStar.Absyn.Syntax
open FStar.Absyn.Util
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module T = FStar.Syntax.Subst
let ident x = S.mk_ident(x.idText, x.idRange)
let lident (l:lident) = S.lid_of_ids ((l.ns@[l.ident]) |> List.map ident)

let aqual (a:aqual) : S.aqual = 
    match a with 
    | None -> None
    | Some a -> Some (match a with 
                      | Implicit -> S.Implicit
                      | Equality -> S.Equality)

let bv_of_bvar x = {ppname=ident x.v.ppname; 
                    index=x.v.realname.GetHashCode(); 
                    sort=S.tun}

let sconst = function
  | Const_unit           -> S.Const_unit
  | Const_uint8 x        -> S.Const_uint8 x
  | Const_bool  b        -> S.Const_bool b
  | Const_int32 i        -> S.Const_int32 i
  | Const_int64 i        -> S.Const_int64 i
  | Const_int i          -> S.Const_int i
  | Const_char c         -> S.Const_char c
  | Const_float f        -> S.Const_float f
  | Const_bytearray(a,r) -> S.Const_bytearray(a,r)
  | Const_string(a,r)    -> S.Const_string(a,r)

let rec trans_typ (t:typ) : term = 
    match (unmeta_typ t).n with
     | Typ_btvar x ->        S.bv_to_name (bv_of_bvar x)
     | Typ_const f ->        S.fvar None (lident f.v) t.pos
     | Typ_fun(bs, c) ->     U.arrow (trans_binders bs) (trans_comp c)
     | Typ_refine(x, t) ->   U.refine (trans_bvvar x) (trans_typ t)
     | Typ_app(t0, args) ->  S.mk (Tm_app(trans_typ t0, List.map trans_arg args)) None t.pos
     | Typ_lam(bs, t) ->     U.abs (trans_binders bs) (trans_typ t)
     | Typ_uvar (u, _) ->    S.fvar None (S.lid_of_path [Util.string_of_int (Unionfind.uvar_id u)] t.pos) t.pos
     | Typ_ascribed(t, k) -> S.mk (Tm_ascribed(trans_typ t, trans_kind k, None)) None t.pos
     | Typ_unknown _ ->      S.tun
     | Typ_meta    _
     | Typ_delayed _ ->      failwith "Impossbile"

and trans_bvvar x = {bv_of_bvar x with sort=trans_typ x.sort}

and trans_btvar x = {bv_of_bvar x with sort=trans_kind x.sort}

and trans_binders (bs:binders) = 
  bs |> List.map (fun (x, imp) -> match x with 
                                    | Inl x -> {bv_of_bvar x with sort=trans_kind x.sort}, aqual imp
                                    | Inr x -> trans_bvvar x, aqual imp)

and trans_arg = function 
 | Inl t, imp -> trans_typ t, aqual imp
 | Inr e, imp -> trans_exp e, aqual imp

and trans_comp (c:comp) : S.comp = 
 match c.n with 
 | Total t -> S.mk_Total <| trans_typ t
 | Comp c ->  S.mk_Comp {  
                 S.effect_name=lident c.effect_name;
                 S.effect_args=List.map trans_arg c.effect_args;
                 S.result_typ=trans_typ c.result_typ;
                 S.flags=[]
              } 

and trans_kind (k:knd) :term = 
    match (compress_kind k).n with 
     | Kind_type   ->       U.ktype0
     | Kind_effect ->       S.fvar None (S.lid_of_path ["Effect"] k.pos) k.pos
     | Kind_abbrev(_, k) -> trans_kind k
     | Kind_arrow(bs, k) -> U.arrow (trans_binders bs) (S.mk_Total (trans_kind k))
     | Kind_uvar(uv, _) ->  S.fvar None (S.lid_of_path [Util.string_of_int (Unionfind.uvar_id uv)] k.pos) k.pos
     | Kind_lam(bs, k) ->   U.abs (trans_binders bs) (trans_kind k)
     | Kind_unknown ->      S.tun
     | Kind_delayed _    -> failwith "Impossible"

and trans_pat (p:pat) : S.pat = 
    let wi q = S.withinfo q S.tun.n p.p in 
    match p.v with
      | Pat_disj ps -> wi (S.Pat_disj (List.map trans_pat ps))
      | Pat_constant c -> wi (S.Pat_constant (sconst c))
      | Pat_cons(x, q, pats) -> wi (S.Pat_cons(S.fv (lident x.v) None,  pats |> List.map (fun (p, b) -> trans_pat p, b)))
      | Pat_var x -> wi (S.Pat_var (bv_of_bvar x))
      | Pat_tvar a   -> wi (S.Pat_var (bv_of_bvar a))
      | Pat_wild x -> wi (S.Pat_wild (bv_of_bvar x))
      | Pat_twild x ->  wi (S.Pat_wild (bv_of_bvar x))
      | Pat_dot_term (x, e) -> wi (S.Pat_dot_term(bv_of_bvar x, trans_exp e))
      | Pat_dot_typ (a, t) ->  wi (S.Pat_dot_term(bv_of_bvar a, trans_typ t))

and trans_exp e = 
    match (unmeta_exp e).n with
     | Exp_bvar x ->      S.bv_to_name (bv_of_bvar x)
     | Exp_fvar (f, _) -> S.fvar None (lident f.v) e.pos
     | Exp_constant s ->  S.mk (Tm_constant (sconst s)) None e.pos
     | Exp_abs(bs, e) ->  U.abs (trans_binders bs) (trans_exp e)
     | Exp_app(e0, args) -> mk (Tm_app(trans_exp e0, List.map trans_arg args)) None e.pos
     | Exp_match(e0, pats) -> 
       let pats = pats |> List.map (fun (p, wopt, e) -> 
        let q = trans_pat p in 
        let xs = S.pat_bvs q |> List.map mk_binder in
        let wopt = 
            match wopt with 
            | None -> None
            | Some w -> FStar.Syntax.Subst.close xs (trans_exp w) |> Some in
        let e = FStar.Syntax.Subst.close xs (trans_exp e) in
        (q, wopt, e)) in 
       mk (Tm_match(trans_exp e0, pats)) None e.pos

     | Exp_ascribed(e0, t, _) -> 
       mk (Tm_ascribed(trans_exp e0, trans_typ t, None)) None e.pos
    
     | Exp_let((is_rec, lbs), body) -> 
       let lb_binders = lbs |> List.collect (fun lb -> 
            match lb.lbname with
                | Inr _ -> []
                | Inl x -> [mk_binder <| bv_of_bvar (FStar.Absyn.Util.bvd_to_bvar_s x lb.lbtyp)]) in
       let maybe_close t = if is_rec then FStar.Syntax.Subst.close lb_binders t else t in
       let lbs = lbs |> List.map (fun lb -> 
            let lbname = match lb.lbname with 
                            | Inr l -> Inr (lident l)
                            | Inl x -> Inl (bv_of_bvar (FStar.Absyn.Util.bvd_to_bvar_s x lb.lbtyp)) in
            let lbtyp = trans_typ lb.lbtyp in
            let lbdef = trans_exp lb.lbdef in
            let lbeff = lident lb.lbeff in
                  {
                    S.lbname=lbname;
                    S.lbdef=maybe_close lbdef;
                    S.lbeff=lbeff;
                    S.lbtyp=lbtyp;
                    S.lbunivs=[];
                  }) in
        let body = FStar.Syntax.Subst.close lb_binders (trans_exp body) in
        mk (Tm_let((is_rec, lbs), body)) None e.pos

     | Exp_uvar(u, _) -> S.fvar None (S.lid_of_path [Util.string_of_int (Unionfind.uvar_id u)] e.pos) e.pos
     | Exp_delayed _ 
     | Exp_meta _  -> failwith "Impossible"

let rec term_eq t1 t2 = 
    let t1 = T.compress t1 in 
    let t2 = T.compress t2 in 
    let binders_eq xs ys = 
        List.forall2 (fun ((x:bv, _)) (y:bv, _) -> term_eq x.sort y.sort) xs ys in
    let args_eq xs ys = 
        List.forall2 (fun (a, imp) (b, imp') -> term_eq a b && imp=imp') xs ys in
    let comp_eq (c:S.comp) (d:S.comp) =
        match c.n, d.n with 
            | S.Total t, S.Total s -> term_eq t s
            | S.Comp ct1, S.Comp ct2 ->     
              S.lid_equals ct1.effect_name ct2.effect_name 
              && term_eq ct1.result_typ ct2.result_typ
              && args_eq ct1.effect_args ct2.effect_args
            | _ -> false in
    match t1.n, t2.n with 
      | Tm_bvar x, Tm_bvar y -> x.index = y.index
      | Tm_name x, Tm_name y -> S.bv_eq x y
      | Tm_fvar f, Tm_fvar g -> S.fv_eq f g
      | Tm_uinst (t, _), Tm_uinst(s, _) -> term_eq t s
      | Tm_constant c1, Tm_constant c2 -> c1=c2
      | Tm_type u, Tm_type v -> u=v
      | Tm_abs(xs, t), Tm_abs(ys, u) -> binders_eq xs ys && term_eq t u
      | Tm_arrow(xs, c), Tm_arrow(ys, d) -> binders_eq xs ys && comp_eq c d
      | Tm_refine(x, t), Tm_refine(y, u) -> term_eq x.sort y.sort && term_eq t u
      | Tm_app(t, args), Tm_app(s, args') -> term_eq t s && args_eq args args'
      | Tm_match(t, pats), Tm_match(t', pats') -> 
        List.forall2 (fun (_, _, e) (_, _, e') -> term_eq e e') pats pats'
        && term_eq t t'
      | Tm_ascribed(t1, t2, _), Tm_ascribed(s1, s2, _) -> 
        term_eq t1 s1 && term_eq t2 s2
      | Tm_let((is_rec, lbs), t), Tm_let((is_rec',lbs'), s) when is_rec=is_rec' -> 
        lbs |> (lbs' |> List.forall2 (fun lb1 lb2 -> term_eq lb1.lbtyp lb2.lbtyp && term_eq lb1.lbdef lb2.lbdef)) 
        && term_eq t s
      | Tm_uvar(u, _), Tm_uvar(u', _) -> Unionfind.equivalent u u'
      | Tm_delayed _, _
      | Tm_meta _, _
      | _, Tm_delayed _
      | _, Tm_meta _ -> failwith "Impossible"
      | Tm_unknown, Tm_unknown -> true
      | _ -> false                                                

open FStar.Syntax.Util
open FStar.Syntax.Syntax
let x = gen_bv "x" None tun
let y = gen_bv "y" None tun
let f = gen_bv "f" None tun
let g = gen_bv "g" None tun
let n = gen_bv "n" None tun
let h = gen_bv "h" None tun
let m = gen_bv "m" None tun
let tm t = mk t None dummyRange
let nm x = bv_to_name x
let app x ts = tm <| Tm_app(x, List.map arg ts)
let b = mk_binder

let id    : term = abs [b x] (nm x)
let apply : term = abs [b f; b x] (app (nm f) [nm x])
let twice : term = abs [b f; b x] (app (nm f) [(app (nm f) [nm x])])
let tt    : term = abs [b x; b y] (nm x)
let ff    : term = abs [b x; b y] (nm y)



let z : term = abs [b f; b x] (nm x)
let one : term = abs [b f; b x] (app (nm f) [nm x])
let two : term = abs [b g; b y] (app (nm g) [app (nm g) [nm y]])
let succ n = abs [b f; b x] (app (nm f) [(app n [nm f; nm x])])
let rec encode n = 
    if n = 0 then z
    else succ (encode (n - 1))
let pred = abs [b n; b f; b x]
               (app (nm n)
                    [abs [b g; b h]
                         (app (nm h) [app (nm g) [nm f]]);
                     abs [b y] (nm x); 
                     abs [b y] (nm y)]) 
let minus m n = app n [pred; m]
let mul : term = abs [b m; b n; b f] (app (nm m) [app (nm n) [nm f]])
let let_ x e e' : term = app (abs [b x] e') [e]
let mk_let x e e' : term = 
    let e' = FStar.Syntax.Subst.subst [NM(x, 0)] e' in
    mk (Tm_let((false, [{lbname=Inl x; lbunivs=[]; lbtyp=tun; lbdef=e; lbeff=lid_of_path ["Pure"] dummyRange}]), e')) 
                           None dummyRange

let lid x = lid_of_path [x] dummyRange                           
let znat_l = S.fv (lid "Z") None
let snat_l = S.fv (lid "S") None
let tm_fv fv = mk (Tm_fvar fv) None dummyRange
let znat : term = tm_fv znat_l
let snat s      = mk (Tm_app(tm_fv snat_l, [arg s])) None dummyRange
let pat p = withinfo p tun.n dummyRange
open FStar.Syntax.Subst
module SS=FStar.Syntax.Subst
let mk_match h branches = 
    let branches = branches |> List.map (fun (p, wopt, b) -> 
        let binders = S.pat_bvs p |> List.map S.mk_binder in
        let b = SS.close binders b in
        let wopt = match wopt with
            | None -> None
            | Some w -> Some (SS.close binders w) in
        p, wopt, b) in
    mk (Tm_match(h, branches)) None dummyRange
let pred_nat s  = 
    let zbranch = pat (Pat_cons(znat_l, [])), 
                  None, 
                  znat in 
    let sbranch = pat (Pat_cons(snat_l, [pat (Pat_var x), false])), 
                  None, 
                  mk (Tm_bvar({x with index=0})) None dummyRange in
    mk_match s [zbranch;sbranch]
let minus_nat t1 t2 =
    let minus = m in 
    let zbranch = pat (Pat_cons(znat_l, [])), 
                  None, 
                  nm x in
    let sbranch = pat (Pat_cons(snat_l, [pat (Pat_var n), false])), 
                  None, 
                  app (nm minus) [pred_nat (nm x); nm n] in
    let lb = {lbname=Inl minus; lbeff=lid_of_path ["Pure"] dummyRange; lbunivs=[]; lbtyp=tun; 
              lbdef=subst [NM(minus, 0)] (abs [b x; b y] (mk_match (nm y) [zbranch; sbranch]))} in
    mk (Tm_let((true, [lb]), subst [NM(minus, 0)] (app (nm minus) [t1; t2]))) None dummyRange
let encode_nat n = 
    let rec aux out n = 
        if n=0 then out
        else aux (snat out) (n - 1) in 
    aux znat n

module P = FStar.Syntax.Print
let run r expected = 
//    Printf.printf "redex = %s\n" (P.term_to_string r);
    let x = FStar.TypeChecker.Normalize.norm FStar.TypeChecker.Normalize.empty_cfg [] [] r in
    Printf.printf "result = %s\n" (P.term_to_string x);
    Printf.printf "expected = %s\n\n" (P.term_to_string expected);
    assert (term_eq x expected);
    

[<EntryPoint>] 
let main argv =
    TypeChecker.Normalize.debug := argv.Length >= 1 && argv.[0] = "debug";
    run (app apply [one; id; nm n]) (nm n);
    run (app apply [tt; nm n; nm m]) (nm n);
    run (app apply [ff; nm n; nm m]) (nm m);
    run (app apply [apply; apply; apply; apply; apply; ff; nm n; nm m]) (nm m);
    run (app twice [apply; ff; nm n; nm m]) (nm m);
    run (minus one z) one;
    run (app pred [one]) z;
    run (minus one one) z;
    run (app mul [one; one]) one;
    run (app mul [two; one]) two;
    run (app mul [succ one; one]) two;
    run (minus (encode 10) (encode 10)) z;
    run (minus (encode 100) (encode 100)) z;
    run (let_ x (encode 1000) (minus (nm x) (nm x))) z;
    run (let_ x (succ one)
        (let_ y (app mul [nm x; nm x])
            (let_ h (app mul [nm y; nm y]) 
                    (minus (nm h) (nm h))))) z;
    run (mk_let x (succ one)
        (mk_let y (app mul [nm x; nm x])
            (mk_let h (app mul [nm y; nm y]) 
                      (minus (nm h) (nm h))))) z;
    run (pred_nat (snat (snat znat))) (snat znat);
    run (minus_nat (snat (snat znat)) (snat znat)) (snat znat);
    run (minus_nat (encode_nat 100) (encode_nat 100)) znat;
    run (minus_nat (encode_nat 10000) (encode_nat 10000)) znat;
    run (minus_nat (encode_nat 1000000) (encode_nat 1000000)) znat;
    0
