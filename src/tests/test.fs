//#light "off"
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
let id x = S.mk_ident(x.idText, x.idRange)
let lident (l:lident) = S.lid_of_ids ((l.ns@[l.ident]) |> List.map id)

let aqual (a:aqual) : S.aqual = 
    match a with 
    | None -> None
    | Some a -> Some (match a with 
                      | Implicit -> S.Implicit
                      | Equality -> S.Equality)

let bv_of_bvar x = {ppname=id x.v.ppname; 
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
     | Typ_const f ->        U.fvar None (lident f.v) t.pos
     | Typ_fun(bs, c) ->     U.arrow (trans_binders bs) (trans_comp c)
     | Typ_refine(x, t) ->   U.refine (trans_bvvar x) (trans_typ t)
     | Typ_app(t0, args) ->  S.mk (Tm_app(trans_typ t0, List.map trans_arg args)) None t.pos
     | Typ_lam(bs, t) ->     U.abs (trans_binders bs) (trans_typ t)
     | Typ_uvar (u, _) ->    U.fvar None (S.lid_of_path [Util.string_of_int (Unionfind.uvar_id u)] t.pos) t.pos
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
     | Kind_effect ->       U.fvar None (S.lid_of_path ["Effect"] k.pos) k.pos
     | Kind_abbrev(_, k) -> trans_kind k
     | Kind_arrow(bs, k) -> U.arrow (trans_binders bs) (S.mk_Total (trans_kind k))
     | Kind_uvar(uv, _) ->  U.fvar None (S.lid_of_path [Util.string_of_int (Unionfind.uvar_id uv)] k.pos) k.pos
     | Kind_lam(bs, k) ->   U.abs (trans_binders bs) (trans_kind k)
     | Kind_unknown ->      S.tun
     | Kind_delayed _    -> failwith "Impossible"

and trans_pat (p:pat) : S.pat = 
    let wi q = S.withinfo q S.tun.n p.p in 
    match p.v with
      | Pat_disj ps -> wi (S.Pat_disj (List.map trans_pat ps))
      | Pat_constant c -> wi (S.Pat_constant (sconst c))
      | Pat_cons(x, q, pats) -> wi (S.Pat_cons(U.fv (lident x.v) None,  pats |> List.map (fun (p, b) -> trans_pat p, b)))
      | Pat_var x -> wi (S.Pat_var (bv_of_bvar x))
      | Pat_tvar a   -> wi (S.Pat_var (bv_of_bvar a))
      | Pat_wild x -> wi (S.Pat_wild (bv_of_bvar x))
      | Pat_twild x ->  wi (S.Pat_wild (bv_of_bvar x))
      | Pat_dot_term (x, e) -> wi (S.Pat_dot_term(bv_of_bvar x, trans_exp e))
      | Pat_dot_typ (a, t) ->  wi (S.Pat_dot_term(bv_of_bvar a, trans_typ t))

and trans_exp e = 
    match (unmeta_exp e).n with
     | Exp_bvar x ->      S.bv_to_name (bv_of_bvar x)
     | Exp_fvar (f, _) -> U.fvar None (lident f.v) e.pos
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

     | Exp_uvar(u, _) -> U.fvar None (S.lid_of_path [Util.string_of_int (Unionfind.uvar_id u)] e.pos) e.pos
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
      | Tm_fvar f, Tm_fvar g -> U.fvar_eq (fst f) (fst g)
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


type Boxed<'a> (value:'a, cmp:'a -> 'a -> int, hash: 'a -> int) =
   member this.unbox = value
   override this.Equals (other:obj) = let y = other :?> Boxed<'a> in cmp value (y.unbox) = 0
   override this.GetHashCode() = hash value
   interface System.IComparable with
            member this.CompareTo(other:obj) =
                let x = other :?> Boxed<'a> in
                cmp value (x.unbox)


open System.Collections.Generic
type hset<'value>=HashSet<'value>
type EqCmp<'a> (eq:'a -> 'a -> bool, hash:'a -> int) =
    interface System.Collections.Generic.IEqualityComparer<'a> with
            member this.Equals(x:'a, y:'a) = eq x y
            member this.GetHashCode(x:'a) = hash x
let new_hset (eq:'a -> 'a -> bool) (hash:'a -> int) : hset<'a> =
    let cmp = new EqCmp<'a>(eq,hash) :> IEqualityComparer<'a> in
    new HashSet<'a>(cmp)
let hset_add a (s:hset<'a>) = ignore <| s.Add(a); s
let hset_remove a (s:hset<'a>) = ignore <| s.Remove(a); s
let hset_mem a (s:hset<'a>) = s.Contains(a)
let hset_copy (s:hset<'a>)  =
    let s' = new HashSet<'a>(s.Comparer) in
    s'.UnionWith(s);
    s'
let hset_union (s1:hset<'a>) (s2:hset<'a>) : hset<'a> = s1.UnionWith(s2); s1
let hset_intersect (s1:hset<'a>) (s2:hset<'a>) : hset<'a> = s1.IntersectWith(s2); s2
let hset_elements (s1:hset<'a>) : list<'a> =
    let mutable e = s1.GetEnumerator() in
    let mutable res =  [] in
        while e.MoveNext() do
          res <- e.Current :: res
        done;
        res
let hset_is_subset_of (s1:hset<'a>) (s2:hset<'a>) : bool = s1.IsSubsetOf(s2)
let hset_difference (s1:hset<'a>) (s2:hset<'a>) : hset<'a> = s1.ExceptWith(s2); s1
let hset_count (s1:hset<'a>) = s1.Count
let mk_ftv_hset<'a,'b> () : hset<bvar<'a,'b>> =
    new_hset (fun x y -> bvd_eq x.v y.v) (fun x -> Util.hashcode x.v.realname.idText)


type fset<'a> = Collections.Set<Boxed<'a>> * ('a -> Boxed<'a>)
let mk_ftv_fset<'a,'b> () : fset<bvar<'a,'b>> =
    let box v = new Boxed<bvar<'a,'b>>(v, (fun x y -> x.v.realname.idText.CompareTo(y.v.realname.idText)), (fun x -> Util.hashcode x.v.realname.idText)) in
    (new Collections.Set<Boxed<bvar<'a,'b>>>([]), box)

let fset_add a ((s, b):fset<'a>) = s.Add (b a), b
let fset_remove a ((s1, b):fset<'a>) = s1.Remove(b a), b
let fset_mem a ((s, b):fset<'a>) = s.Contains (b a)
let fset_copy (s:fset<'a>) = s
let fset_union ((s1, b):fset<'a>) ((s2, _):fset<'a>) = Set.union s1 s2, b
let fset_intersect ((s1, b):fset<'a>) ((s2, _):fset<'a>) = Set.intersect s1 s2, b
let fset_subset ((s1, _): fset<'a>) ((s2, _):fset<'a>) = s1.IsSubsetOf(s2)
let fset_count ((s1, _):fset<'a>) = s1.Count
let fset_difference ((s1, b):fset<'a>) ((s2, _):fset<'a>) : fset<'a> = Set.difference s1 s2, b
let fset_elements ((s1, b):fset<'a>) :list<'a> = Set.toList s1 |> List.map (fun x -> x.unbox)


type iset<'a,'b> = {
    name:string;
    add: 'a -> 'b -> 'b;
    mem: 'a -> 'b -> bool;
    union: 'b -> 'b -> 'b;
    copy: 'b -> 'b;
}

let hset_to_iset () : iset<'a, hset<'a>> = {
    name="HashSet";
    add=hset_add;
    mem=hset_mem;
    union=hset_union;
    copy=hset_copy
}

let fset_to_iset () : iset<'a, fset<'a>> = {
    name="F# set";
    add=fset_add;
    mem=fset_mem;
    union=fset_union;
    copy=fset_copy
}

let list_to_iset (eq:'a -> 'a -> bool) : iset<'a, list<'a>> = {
    name="F# list";
    add=fun x y -> x::y;
    mem=fun x xs -> List.exists (eq x) xs;
    union=fun xs ys -> xs@ys;
    copy=fun x -> x;
}

let bench_set (s1:'set, s2:'set, f:iset<bvvar, 'set>, vars:option<bvvar>[]) =
    let timer = System.Diagnostics.Stopwatch.StartNew()
    for i in 0..99999 do
        ignore <| f.add (vars.[i] |> Util.must) s1
    for i in 0..99999 do
        if (i % 2 = 0)
        then  ignore <| f.add (vars.[i] |> Util.must) s2

    printfn "%s: add in %fs" f.name timer.Elapsed.TotalSeconds

    timer.Restart()
    for i in 0..1000 do
        ignore <| f.union (f.copy s2) s1

    printfn "%s: copy/union in %fs" f.name timer.Elapsed.TotalSeconds

    timer.Restart()
    for _ in 1..10 do
        for i in 0..99999 do
        ignore <| f.mem (Util.must vars.[i]) s1

    printfn "%s: contains in %fs" f.name timer.Elapsed.TotalSeconds

let set_vs_fset_vs_list () =
    let s1 = mk_ftv_hset ()
    let s2 = mk_ftv_hset ()
    let vars = Array.create<bvvar option> 100000 None
    for i in 0..99999 do
        vars.[i] <- Some (Util.bvd_to_bvar_s (Util.new_bvd None) Syntax.tun)

    bench_set (s1, s2, hset_to_iset(), vars);
    let s1 = mk_ftv_fset () in
    let s2 = mk_ftv_fset () in
    bench_set (s1, s2, fset_to_iset(), vars)

    let eq x y = bvd_eq x.v y.v in
    bench_set ([], [], list_to_iset eq, vars)

let test_freevars () =
    Options.print_real_names := true
    let iset1 = Syntax.new_ftv_set ()
    let iset2 = Syntax.new_ftv_set ()
    printfn "Empty set subset? %A" (Util.set_is_subset_of iset1 iset2)
    for i in 1..10 do
        let x = Util.new_bvd None
        let y = {ppname=Syntax.mk_ident("junk", int64 i);
                 realname=Syntax.mk_ident(x.realname.idText, 1L)}
        ignore <| Util.set_add (Util.bvd_to_bvar_s x Syntax.tun) iset1
        ignore <| Util.set_add (Util.bvd_to_bvar_s y Syntax.tun) iset2
    done
    printfn "Set 1 is %A" (Util.set_elements iset1 |> List.map (fun x -> Print.strBvd x.v))
    printfn "Set 2 is %A" (Util.set_elements iset2 |> List.map (fun x -> Print.strBvd x.v))
    printfn "Subset? 1, 2= %A" (Util.set_is_subset_of iset1 iset2)
    printfn "Subset? 2, 1= %A" (Util.set_is_subset_of iset2 iset1)

[<EntryPoint>]
let main argv =
    set_vs_fset_vs_list()
    0 // return an integer exit code
