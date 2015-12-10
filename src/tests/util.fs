#light "off"
module FStar.Tests.Util

open FStar
open FStar.Util
open FStar.Absyn
open FStar.Syntax.Syntax
open FStar.Absyn.Syntax
open FStar.Absyn.Util
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module SS = FStar.Syntax.Subst
module I = FStar.Ident
open FStar.Ident

let rec force_term x =
  let x = SS.compress x in
  match x.n with
  | Tm_delayed _ -> failwith "impossible"
  | Tm_meta(t, _) -> force_term t
  | Tm_bvar _ 
  | Tm_name _ 
  | Tm_fvar _ 
  | Tm_constant _ -> ()
  | Tm_arrow(bs, c) -> force_binders bs; force_comp c
  | Tm_abs(bs, t2) ->  force_binders bs; force_term t2
  | Tm_refine(xt, f) -> force_term xt.sort; force_term f
  | Tm_app(_, []) -> failwith "Empty args!"
  | Tm_app(t, args) -> force_term t; args |> List.iter (fun (x, _) -> force_term x)
  | Tm_let(lbs, e) ->  snd lbs |> List.iter (fun lb -> force_term lb.lbdef; force_term lb.lbtyp); force_term e
  | Tm_match(head, branches) ->
    force_term head;
    branches |> List.iter (fun (_, _, e) -> force_term e)
  | _ -> ()

and force_binders bs = bs |> List.iter (fun (b, _) -> force_term b.sort)
and force_comp c = ()

let rec term_eq t1 t2 = 
    let t1 = SS.compress t1 in 
    let t2 = SS.compress t2 in 
    let binders_eq xs ys = 
        List.forall2 (fun ((x:bv, _)) (y:bv, _) -> term_eq x.sort y.sort) xs ys in
    let args_eq xs ys = 
        List.forall2 (fun (a, imp) (b, imp') -> term_eq a b && imp=imp') xs ys in
    let comp_eq (c:S.comp) (d:S.comp) =
        match c.n, d.n with 
            | S.Total t, S.Total s -> term_eq t s
            | S.Comp ct1, S.Comp ct2 ->     
              I.lid_equals ct1.effect_name ct2.effect_name 
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

