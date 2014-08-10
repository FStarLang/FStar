(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"
module Microsoft.FStar.Absyn.Test
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn.Syntax

let fail msg = failwith msg
  
type codes = 
  | Const
  | TConst
  | Var
  | TVar
  | Lam
  | TLam
  | App
  | TApp
  | Arr
  | TArr
  | TTApp
  | TEApp
  | KBase
  | KArr
  | KTArr

let codes = [Const; TConst; Var; TVar; Lam; TLam; App; TApp; Arr; TArr; KBase; KArr; KTArr; TTApp; TEApp]

let rng = System.Random(17)

let choose l = 
  if List.length l = 0
  then failwith "Choosing from an empty list!"
  else List.nth l (rng.Next(0, List.length l))
let flip () = rng.Next(2)=1
let randN n = rng.Next(n)
  
let minSize = function 
  | KBase
  | Const
  | TConst
  | Var
  | TVar -> 1
  | Lam  
  | TLam 
  | TTApp
  | TEApp
  | App 
  | TApp 
  | Arr
  | TArr 
  | KArr
  | KTArr -> 3

type sort = 
  | Exp 
  | Typ
  | Knd

let sortOfCode = function
  | Const
  | Var
  | Lam
  | App
  | TApp
  | TLam -> Exp
  
  | TVar
  | TConst
  | Arr
  | TArr 
  | TTApp
  | TEApp -> Typ
  | KBase
  | KArr
  | KTArr -> Knd

let chooseOp sort atmost ops = 
  let ops' = List.filter (fun o -> sortOfCode o = sort && atmost/2 <= minSize o && minSize o <= atmost) ops in 
  let ops' = 
    if ops'.Length=0 
    then List.filter (fun o -> sortOfCode o = sort && minSize o <= atmost) ops 
    else ops' in 
  choose ops' 

let chooseR vars = 
  let xvars = vars |> List.filter (fun v -> match v with Inr _ -> true | _ -> false) in
  let (Inr x) = choose xvars in
  x

let chooseL vars = 
  let xvars = vars |> List.filter (fun v -> match v with Inl _ -> true | _ -> false) in
  let (Inl x) = choose xvars in
  x

type fvs = list<either<btvar, bvvar>>

let bind (e1, vs, i) f =
  let e2, vs', j  = f e1 in 
  e2, vs@vs', i + j
let ret e = e, [], 1

let rec genExp vars ops size : exp * fvs * int = 
    assert (size > 0);
    let op = chooseOp Exp size ops in 
    let size = size - 1 in 
    match op with 
      | Var -> 
        if vars |> List.exists (function Inr _ -> true | _ -> false)
        then 
          let x = chooseR vars in
          Exp_bvar x, [Inr x], 1
        else ret <| Exp_constant Const_unit
      | Const -> ret <| Exp_constant Const_unit
      | App -> 
        bind (genExp vars ops (size / 2)) (fun e1 -> 
        bind (genExp vars ops (size / 2)) (fun e2 -> 
        ret (Exp_app(e1, e2, false))))
      | TApp ->
        bind (genExp vars ops (size / 2)) (fun e1 -> 
        bind (genTyp vars ops (size / 2)) (fun t1 -> 
        ret (Exp_tapp(e1, t1))))
      | Lam -> 
        let x = Util.new_bvd None in 
        bind (genTyp vars ops (size / 2)) (fun t -> 
        let xv = Util.bvd_to_bvar_s x t in 
        bind (genExp (Inr xv::vars) ops (size / 2)) (fun e -> 
        ret <| Exp_abs(x, t, e)))
      | TLam -> 
        let a = Util.new_bvd None in 
        bind (genKind vars ops (size / 2)) (fun k -> 
        let av = Util.bvd_to_bvar_s a k in 
        bind (genExp (Inl av::vars) ops (size / 2)) (fun e ->
        ret <| Exp_tabs(a, k, e)))
      | _ -> fail (Printf.sprintf "expected an expression; got %A" op)

and genTyp vars ops size : typ * fvs * int = 
  bind (genTyp' vars ops size) (fun t -> 
  withkind kun t, [], 0)

and genTyp' vars ops size : typ' * fvs * int = 
    assert (size > 0);
    let op = chooseOp Typ size ops in 
    let size = size - 1 in 
    match op with 
      | TVar -> 
        if vars |> List.exists (function Inl _ -> true | _ -> false)
        then let a = chooseL vars in Typ_btvar a, [Inl a], 1
        else ret <| (Util.ftv Const.unit_lid).t
      | TConst -> ret <| (Util.ftv Const.unit_lid).t
      | Arr -> 
        let x = Util.new_bvd None in 
        bind (genTyp vars ops (size / 2)) (fun t1 -> 
        let xv = Util.bvd_to_bvar_s x t1 in 
        bind (genTyp (Inr xv::vars) ops (size / 2)) (fun t2 ->
        ret <| Typ_fun(Some x, t1, Total t2 , false)))
      | TArr -> 
        let a = Util.new_bvd None in 
        bind (genKind vars ops (size / 2)) (fun k -> 
        let av = Util.bvd_to_bvar_s a k in 
        bind (genTyp (Inl av::vars) ops (size / 2)) (fun t ->
        ret <| Typ_univ(a, k, Total t)))
      | TTApp -> 
        bind (genTyp vars ops (size / 2)) (fun t1 ->
        bind (genTyp vars ops (size / 2)) (fun t2 -> 
        ret <| Typ_app(t1, t2 , false)))
      | TEApp -> 
        bind (genTyp vars ops (size / 2)) (fun t1 -> 
        bind (genExp vars ops (size / 2)) (fun e2 -> 
        ret <| Typ_dep(t1, e2, false)))
      | _ -> fail (Printf.sprintf "expected a type; got %A" op)

and genKind vars ops size : knd * fvs * int = 
    assert (size > 0);
    let op = chooseOp Knd size ops in 
    let size = size - 1 in 
    match op with 
      | KBase -> ret <| Kind_type
      | KArr -> 
        bind (genTyp vars ops (size / 2)) (fun t -> 
        bind (genKind vars ops (size / 2)) (fun k -> 
        ret <| Kind_dcon(None, t, k, false)))
      | KTArr -> 
        bind (genKind vars ops (size / 2)) (fun k1 -> 
        bind (genKind vars ops (size / 2)) (fun k2 -> 
        ret <| Kind_tcon(None, k1, k2, false)))
      | _ -> fail (Printf.sprintf "expected a kind; got %A" op)

let genMany genOne nvars size number = 
  let new_tvar () = Inl (Util.bvd_to_bvar_s (Util.new_bvd None) kun) in
  let new_xvar () = Inr (Util.bvd_to_bvar_s (Util.new_bvd None) tun) in
  let rec freevars out n = 
    if n = 0 then out
    else if flip () 
    then freevars (new_tvar ()::out) (n - 1)
    else freevars (new_xvar ()::out) (n - 1) in
  let vars = freevars [new_tvar(); new_xvar()] nvars in 
  let rec gen out n = 
    if n = 0 then out
    else gen (genOne vars codes size::out) (n - 1) in 
  vars, gen [] number

let testGen () = 
  let _, exps = genMany genTyp 3 20 10 in 
  exps |> List.iter (fun (e, _, _) -> 
    Printf.printf "%s\n" (Print.typ_to_string e))

let mk_subst vars : Syntax.subst = 
  match choose vars with 
    | Inl a -> [Inl (a.v, let x, _, _ = genTyp [] codes 10 in x)]
    | Inr x -> [Inr (x.v, let x, _, _ = genExp [] codes 10 in x)]

let rec equal_exps e1 e2 = 
  let e2 = Util.compress_exp e2 in 
  match e1, e2 with 
    | Exp_constant s1, Exp_constant s2 -> s1=s2
    | Exp_bvar x1, Exp_bvar x2 -> Util.bvar_eq x1 x2
    | Exp_abs(x1, t1, e1), Exp_abs(x2, t2, e2) -> 
      Util.bvd_eq x1 x2 && equal_typs t1 t2 && equal_exps e1 e2
    | Exp_tabs(a1, k1, e1), Exp_tabs(a2, k2, e2) -> 
      Util.bvd_eq a1 a2 && equal_kinds k1 k2 && equal_exps e1 e2
    | Exp_app(e1, e1', b1), Exp_app(e2, e2', b2) ->
      b1=b2 && equal_exps e1 e2 && equal_exps e1' e2'
    | Exp_tapp(e1, t1), Exp_tapp(e2, t2) ->
      equal_exps e1 e2 && equal_typs t1 t2
    | _ -> 
      Printf.printf "equal_exps failed: %s <> %s\n" (Print.exp_to_string e1) (Print.exp_to_string e2);
      false
 
and equal_typs t1 t2 = 
  //Printf.printf "equal_typs?: %s and  %s\n" (Print.typ_to_string t1) (Print.typ_to_string t2);
  let t20 = t2 in 
  let t2 = Util.compress_typ t2 in 
  match t1.t, t2.t with 
    | Typ_const fv1, Typ_const fv2 -> Util.fvar_eq fv1 fv2
    | Typ_btvar bv1, Typ_btvar bv2 -> Util.bvar_eq bv1 bv2
    | Typ_fun(Some x1, t1, Total t1', b1), Typ_fun(Some x2, t2, Total t2', b2) -> 
      b1=b2 && Util.bvd_eq x1 x2 && equal_typs t1 t2 && equal_typs t1' t2'
    | Typ_univ(a1, k1, Total t1), Typ_univ(a2, k2, Total t2) -> 
      Util.bvd_eq a1 a2 && equal_kinds k1 k2 && equal_typs t1 t2 
    | Typ_app(t1, t1', b1), Typ_app(t2, t2', b2) -> 
      b1=b2 && equal_typs t1 t2 && equal_typs t1' t2'
    | Typ_dep(t1, e1, b1), Typ_dep(t2, e2, b2) ->
      b1=b2 && equal_typs t1 t2 && equal_exps e1 e2
    | _ -> 
      Printf.printf "equal_typs failed: %s <> %s\n" (Print.typ_to_string t1) (Print.typ_to_string t2);
      false

and equal_kinds k1 k2 = 
  let k2 = Util.compress_kind k2 in 
  match k1, k2 with 
    | Kind_type, Kind_type -> true
    | Kind_tcon(None, k1, k1', b1), Kind_tcon(None, k2, k2', b2) -> 
      b1=b2 && equal_kinds k1 k2 && equal_kinds k1' k2'
    | Kind_dcon(None, t1, k1, b1), Kind_dcon(None, t2, k2, b2) -> 
      b1=b2 && equal_typs t1 t2 && equal_kinds k1 k2
    | _ -> 
      Printf.printf "equal_kids failed: %s <> %s\n" (Print.kind_to_string k1) (Print.kind_to_string k2);
      false
      
let testDelaySubst nvars size num = 
  let vars, typs = genMany genTyp nvars size num in 
  let contains vars ax = 
    vars |> List.exists (fun by -> match ax, by with 
      | Inl a, Inl b -> Util.bvar_eq a b
      | Inr x, Inr y -> Util.bvar_eq x y
      | _ -> false) in
  let subst_to_string s = 
    Printf.sprintf "[%s]" (s |> List.map (function 
      | Inl(a, t) -> Printf.sprintf "(%s \ '%s)" (Print.typ_to_string t) (Print.strBvd a)
      | Inr(x, e) -> Printf.sprintf "(%s \ %s)" (Print.exp_to_string e) (Print.strBvd x)) |> String.concat ", ") in   
  let count = ref 0 in
  typs |> List.iter (fun (t, fvs, sz) -> 
    let fvs = fvs |> List.filter (contains vars) in 
    if List.length fvs <> 0 //&& sz > 10
    then 
      (* let _ = printfn "Size = %d\n" sz in *) 
      let _ = incr count in
      let s = mk_subst fvs in 
      let t1 = Util.eager_subst_typ s t in
      let t2 = Util.subst_typ s t in
      printfn "\n\nSubsadat %s %s ... \n%s\n" (Print.typ_to_string t1) (subst_to_string s) (Print.typ_to_string t2);
//
//      if not (equal_exps e1 e2)
//      then (Printf.printf "Subst %s %s ... " (Print.exp_to_string e) (subst_to_string s);
//            Printf.printf "\nExpected:\n\t%s\nGot:\n\t%s\n" (Print.exp_to_string e1) (Print.exp_to_string e2); exit(0))
//      else ()//Printf.printf "ok\n"
    else ());
  Printf.printf "Tested %d cases\n" !count
 
#if TEST
let _ =
  let ios = Microsoft.FStar.Util.int_of_string in
  let nvars = ios <| Sys.argv.(1) in
  let size = ios <| Sys.argv.(2) in
  let num = ios <| Sys.argv.(3) in
  testDelaySubst nvars size num
#endif      
