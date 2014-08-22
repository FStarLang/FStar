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
module Microsoft.FStar.Tc.Rel

open Microsoft.FStar
open Microsoft.FStar.Tc
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Util
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Tc.Normalize


let unify_typ env ((uv,k):(uvar_t * knd)) t  = match Unionfind.find uv with 
  | Fixed _ -> failwith "impossible"
  | Uvar wf ->
    let rec aux retry t =
      let tk = t.tk in 
      let uvars_in_t = (uvars_in_typ t).uvars_t in
      let occurs () = Util.set_mem (uv,k) uvars_in_t in
      let doit t = match (compress_typ t).n with 
        | Typ_uvar (uv', _) -> Unionfind.union uv uv'; true
        | t' -> 
          let wfok =  wf t tk  in
          let occ_ok = not (occurs ()) in
          if wfok && occ_ok
          then (unchecked_unify uv t; true)
          else if !Options.debug <> []
          then (Util.print_string <| Util.format4 "%s occurs_ok? %s, wf? %s ... Uvars_in_t are {%s}\n"
                (string_of_int (Unionfind.uvar_id uv))
                (if occ_ok then "yes" else "no") 
                (if wfok then "yes" else "no")
                ((Util.set_elements uvars_in_t) |> List.map (fun (uv, _) -> Util.string_of_int <| Unionfind.uvar_id uv) |> String.concat ", "); false)
          else false in
     doit t || (retry && aux false (normalize env t)) in
   aux true t

let unify_kind (uv, ()) k = match Unionfind.find uv with 
  | Fixed _ -> failwith "impossible"
  | Uvar wf -> 
    let k = compress_kind k in
    match k.n with 
      | Kind_uvar (uv', _) -> Unionfind.union uv uv'; true
      | _ -> 
        let occurs = Util.set_mem uv ((uvars_in_kind k).uvars_k) in
        if not occurs && wf k ()
        then (unchecked_unify uv k; true)
        else false

let unify_exp (uv, t) e = match Unionfind.find uv with 
  | Fixed _ -> failwith "impossible"
  | Uvar wf -> 
    let e = compress_exp e in
    match e.n with 
      | Exp_uvar(uv', _) -> Unionfind.union uv uv'; true
      | _ -> 
        let occurs = Util.set_mem (uv,t) ((uvars_in_exp e).uvars_e) in
        if not occurs && wf e t 
        then (unchecked_unify uv e; true)
        else false


(**********************************************************************************************************************)
(* Relations (equality and subsumption) between kinds, types, expressions and computations *)
(**********************************************************************************************************************)
type rel = 
  | EQ 
  | SUB

type guard = 
  | Trivial
  | NonTrivial of formula

let rec is_trivial f : bool = 
    let bin_op f l = match l with 
        | [Inl t1; Inl t2] -> f t1 t2
        | _ -> failwith "Impossible" in
    let connectives = [(Const.and_lid, bin_op (fun t1 t2 -> is_trivial t1 && is_trivial t2));
                       (Const.or_lid,  bin_op (fun t1 t2 -> is_trivial t1 || is_trivial t2));
                       (Const.imp_lid, bin_op (fun t1 t2 -> is_trivial t2));
                       (Const.true_lid, (fun _ -> true));
                       (Const.false_lid, (fun _ -> false));
                       ] in

    let fallback phi = match phi.n with 
        | Typ_lam(_, _, phi) 
        | Typ_tlam(_, _, phi) -> is_trivial phi
        | _ -> false in

    match Util.destruct_typ_as_formula f with 
        | None -> fallback f
        | Some (BaseConn(op, arms)) -> 
           (match connectives |> List.tryFind (fun (l, _) -> lid_equals op l) with 
             | None -> false
             | Some (_, f) -> f arms)
        | Some (QAll(_, _, body)) 
        | Some (QEx(_, _, body)) -> is_trivial body
  

let mkGuard env f =
  let f = Tc.Normalize.normalize env f in 
  if is_trivial f 
  then Trivial
  else NonTrivial f

let guard_to_string (env:env) = function  
  | Trivial -> "trivial"
  | NonTrivial f -> Print.formula_to_string (Tc.Normalize.normalize env f)

let ret g = 
  if not !Options.verify
  then match g with 
    | None -> None
    | Some _ -> Some Trivial
  else g

let trivial t = match t with 
  | Trivial -> ()
  | NonTrivial _ -> failwith "impossible"

let map_guard g f = match g with 
  | Trivial -> Trivial
  | NonTrivial x -> NonTrivial <| f x

let conj_guard g1 g2 = match g1, g2 with 
  | Trivial, g
  | g, Trivial -> g
  | NonTrivial f1, NonTrivial f2 -> NonTrivial (Util.mk_conj f1 f2)

let mk_guard_lam t f = 
  let mk_lam t f =  mk_Typ_lam(Util.new_bvd None, t, f) (mk_Kind_dcon(None, t, mk_Kind_type, false) f.pos) f.pos in
  map_guard f (mk_lam t)

let bindf fopt g = match fopt with 
  | None -> None
  | Some f -> g f

let andf fopt g = match fopt with 
  | None -> None
  | Some f -> match g() with 
    | None -> None
    | Some f' -> Some (conj_guard f f')

let orf fopt g = match fopt with 
  | Some _ -> fopt
  | None -> g ()

let close b f = match b with 
  | Inl(a, k) -> Util.mk_forallT a k f
  | Inr(x, t) -> Util.mk_forall x t f
  
let close_guard b = function
  | Trivial -> Trivial
  | NonTrivial f -> NonTrivial <| close b f

let close_guard_lam yopt t f = 
  let close_lam yopt t f = 
    let y = match yopt with 
      | None -> Util.new_bvd None 
      | Some y -> y in
    close (Inr(y, t)) (syn f.pos mk_Kind_type <| mk_Typ_dep(f, Util.bvd_to_exp y t, false)) in
  map_guard f (close_lam yopt t)

let close_tlam aopt k f = 
  let a = match aopt with 
    | None -> Util.new_bvd None
    | Some a -> a in
  close (Inl(a, k)) (syn f.pos mk_Kind_type <| mk_Typ_app(f, Util.bvd_to_typ a k, false)) 
let close_guard_tlam aopt k f = map_guard f (close_tlam aopt k)

let rec forallf (l:list<'a>) (ff:'a -> option<guard>) : option<guard> = match l with 
  | [] -> Some Trivial
  | hd::tl -> bindf (ff hd) (fun f -> 
              bindf (forallf tl ff) (fun g -> Some <| conj_guard f g))
  
  
  
//////////////////////////////////////////////////////////////////////////
//Refinement subtyping with higher-order unification 
//with special treatment for higher-order patterns 
//////////////////////////////////////////////////////////////////////////
let new_kvar env vars =
  let wf k () = true in
  mk_Kind_uvar (Unionfind.fresh (Uvar wf), vars) (Env.get_range env)

let new_tvar env vars k =
  let wf t tk = true in
  let r = Tc.Env.get_range env in
  let rec mk_uv_app k vars = match vars with 
    | [] -> 
      let uv = Unionfind.fresh (Uvar wf) in
      mk_Typ_uvar'(uv,k) k r, (uv,k)
    
    | Inl a::rest -> 
      let k' = mk_Kind_tcon(Some a.v, a.sort, k, false) r in
      let app, uvk = mk_uv_app k' rest in 
      mk_Typ_app(app, Util.btvar_to_typ a, false) k r, uvk
    
    | Inr x::rest -> 
      let k' = mk_Kind_dcon(Some x.v, x.sort, k, false) r in
      let app, uvk = mk_uv_app k' rest in 
      mk_Typ_dep(app, Util.bvar_to_exp x, false) k r, uvk in
  
  let app,uvk = mk_uv_app k vars in 
  mk_Typ_meta'(Meta_uvar_t_app(app, uvk)) k r, uvk

let new_evar env vars t =
  let wf e t = true in 
  let r = Tc.Env.get_range env in
  let rec mk_uv_app t vars = match vars with 
    | [] -> 
        let uv = Unionfind.fresh (Uvar wf) in 
        mk_Exp_uvar (uv, t) r, (uv,t)
    | Inl a::rest -> 
        let t' = mk_Typ_univ(a.v, a.sort, mk_Total t) ktype r in
        let app, uvt = mk_uv_app t' rest in 
        mk_Exp_tapp(app, Util.btvar_to_typ a) t r, uvt
    | Inr x::rest -> 
        let t' = mk_Typ_fun(Some x.v, x.sort, mk_Total t, false) ktype r in
        let app, uvt = mk_uv_app t' rest in 
        mk_Exp_app(app, Util.bvar_to_exp x, false) t r, uvt in
  let app, uvt = mk_uv_app t vars in
  mk_Exp_meta'(Meta_uvar_e_app(app, uvt)) t r, uvt
 
let new_cvar env vars t = mk_Flex ((Unionfind.fresh Floating, vars), t)

type prob = 
  | KProb of int * rel * knd * knd 
  | TProb of int * rel * typ * typ
  | EProb of int * rel * exp * exp 
  | CProb of int * rel * comp * comp 

let prob_ctr = function 
  | KProb (i, _, _, _)
  | TProb (i, _, _, _)
  | EProb (i, _, _, _) 
  | CProb (i, _, _, _) -> i

type uvar_inst =  //never a uvar in the co-domain of this map
  | UK of uvar_k * knd 
  | UT of uvar_t * typ 
  | UE of uvar_e * exp
  | UC of uvar_c * comp

type worklist = {
    attempting: list<prob>;
    deferred: list<prob>;
    subst: list<uvar_inst>;
    guard: guard;
    ctr: int;
}
let extend_subst ui wl = {wl with subst=ui::wl.subst; ctr=wl.ctr + 1}
type solution = option<(list<uvar_inst> * guard)>
let find_uvar_k uv s = Util.find_map s (function UK(u, t) -> if Unionfind.equivalent uv u then Some t else None | _ -> None)
let find_uvar_t uv s = Util.find_map s (function UT(u, t) -> if Unionfind.equivalent uv u then Some t else None | _ -> None)
let find_uvar_e uv s = Util.find_map s (function UE(u, t) -> if Unionfind.equivalent uv u then Some t else None | _ -> None)
let find_uvar_c uv s = Util.find_map s (function UC(u, t) -> if Unionfind.equivalent uv u then Some t else None | _ -> None)

let rec compress env s t =
    let t = Util.compress_typ t in
    match t.n with 
        | Typ_uvar (uv, _) ->
           (match find_uvar_t uv s with 
                | None -> t
                | Some t -> compress env s t)    
        | Typ_meta(Meta_uvar_t_app(t', (uv, k)))  -> 
            (match find_uvar_t uv s with 
                | Some t -> 
                  let t = compress env s t in 
                  let _, args = Util.flatten_typ_apps t' in 
                  Tc.Normalize.normalize env <| Util.mk_typ_app_explicit t args
                | _ -> t)
        | _ -> t
     
let subst_xopt (xopt, t1) yopt = match xopt, yopt with 
    | None, None 
    | None, Some _
    | Some _, None -> mk_subst []
    | Some x, Some y -> 
      if Util.bvd_eq x y 
      then mk_subst []
      else mk_subst [Inr(y, Util.bvd_to_exp x t1)]

let subst_aopt (xopt, t1) yopt = match xopt, yopt with 
    | None, None 
    | None, Some _
    | Some _, None -> mk_subst []
    | Some x, Some y -> 
      if Util.bvd_eq x y 
      then mk_subst []
      else mk_subst [Inl(y, Util.bvd_to_typ x t1)]       

let rec solve (top:bool) (env:Tc.Env.env) probs : solution = 
    match probs.attempting with 
       | hd::tl -> 
        let probs = {probs with attempting=tl} in
         (match hd with 
            | KProb (_, rel, k1, k2) -> solve_k top env rel k1 k2 probs
            | TProb (_, rel, t1, t2) -> solve_t top env rel t1 t2 probs
            | EProb (_, rel, e1, e2) -> solve_e top env rel e1 e2 probs
            | CProb (_, rel, c1, c2) -> solve_c top env rel c1 c2 probs)
       | [] ->
         match probs.deferred with 
            | [] -> Some (probs.subst, probs.guard) //Yay ... done!
            | _ -> 
              let ctr = List.length probs.subst in 
              let attempt, rest = probs.deferred |> List.partition (fun t -> prob_ctr t < ctr) in
              match attempt with 
                 | [] -> None //no progress made to help with solving deferred problems; fail
                 | _ -> solve top env {probs with attempting=attempt; deferred=rest} 

and solve_k (top:bool) (env:Env.env) rel k1 k2 probs : solution = failwith "NYI"

and solve_t (top:bool) (env:Env.env) rel t1 t2 probs : solution = 
    let t1 = compress env probs.subst t1 in
    let t2 = compress env probs.subst t2 in 
    let ctr = probs.ctr in 
    let r = Env.get_range env in
    match t1.n, t2.n with
      | Typ_meta(Meta_uvar_t_app(_, (_, _))), Typ_meta(Meta_uvar_t_app(_, (_, _))) -> //flex-flex ... defer ... unless, there's no other way to proceed
        solve top env ({probs with deferred=TProb(ctr, rel, t1, t2)::probs.deferred})

      | Typ_btvar a, Typ_btvar b -> 
        if Util.bvd_eq a.v b.v 
        then solve top env probs
        else None

      | Typ_const f, Typ_const g -> 
        if Util.fvar_eq f g
        then solve top env probs
        else None
    
      | Typ_fun(xopt, t1, c1, _), Typ_fun(yopt, t2, c2, _) -> 
        let probs = {probs with attempting=TProb(ctr, rel, t2, t1)::CProb(ctr, rel, c1, Util.subst_comp (subst_xopt (xopt, t1) yopt) c2)::probs.attempting} in
        solve false env probs

      | Typ_univ(a, k1, c1), Typ_univ(b, k2, c2) -> 
        let probs = {probs with attempting=KProb(ctr, rel, k2, k1)::CProb(ctr, rel, c1, Util.subst_comp (subst_aopt (Some a, k1) (Some b)) c2)::probs.attempting} in
        solve false env probs

      | Typ_lam(x, t1, t2), Typ_lam(y, t1', t2') -> 
        let probs = {probs with attempting=TProb(ctr, rel, t1', t1)::TProb(ctr, rel, t2, Util.subst_typ (subst_xopt (Some x, t1) (Some y)) t2')::probs.attempting} in
        solve false env probs

      | Typ_tlam(a, k1, t2), Typ_tlam(b, k1', t2') -> 
        let probs = {probs with attempting=KProb(ctr, rel, k1', k1)::TProb(ctr, rel, t2, Util.subst_typ (subst_aopt (Some a, k1) (Some b)) t2')::probs.attempting} in
        solve false env probs

      | Typ_refine(x, t1, phi1), Typ_refine(y, t2, phi2) -> 
        let phi2 = Util.subst_typ (subst_xopt (Some x, t1) (Some y)) phi2 in
        let probs = match rel with
           | EQ -> {probs with attempting=TProb(ctr, rel, phi1, phi2)::probs.attempting}
           | SUB -> (* but if either phi1 or phi2 are patterns, why not solve it by equating? *)
           let g = mkGuard env <| Util.mk_imp phi1 phi2 in 
           let g = map_guard g (fun f -> 
            if top 
            then mk_Typ_lam(x, t1, f) (mk_Kind_dcon(None, t1, ktype, false) r) r
            else close (Inr(x, t1)) f) in
           {probs with guard=conj_guard probs.guard g} in
        solve_t top env rel t1 t2 probs

      | Typ_meta(Meta_uvar_t_app(t1, (uv,k))), _ -> //flex-rigid
        let _, args_lhs = Util.flatten_typ_apps t1 in
        let rec pat_vars seen = function 
            | [] -> Some (List.rev seen) 
            | Inl {n=Typ_btvar a}::rest ->
                if seen |> Util.for_some (function 
                   | Inl b -> bvd_eq a.v b.v
                   | _ -> false)
                then None //not a pattern
                else pat_vars (Inl a::seen) rest
            | Inr {n=Exp_bvar x}::rest ->
                if seen |> Util.for_some (function 
                    | Inr y -> bvd_eq x.v y.v
                    | _ -> false)
                then None //not a pattern
                else pat_vars (Inr x::seen) rest
            | _ -> None in //not a pattern 

        let subterms () = 
            let ps = args_lhs in
            let h, qs = flatten_typ_apps t2 in
            let xs = ps |> List.map (function 
                | Inl pi -> Inl <| Util.bvd_to_bvar_s (Util.new_bvd None) pi.tk
                | Inr pi -> Inr <| Util.bvd_to_bvar_s (Util.new_bvd None) pi.tk) in
            ps, h, qs, xs in 

        let imitate () = 
                //U p1..pn =?= h q1..qm
                //extend_subst: (U -> \x1..xn. h (G1(x1..xn), ..., Gm(x1..xm)))
                //sub-problems: Gi(p1..pn) =?= qi
            let ps, h, qs, xs = subterms () in
            let gs_xs, sub_probs = qs |> List.map (function 
                | Inl qi -> 
                  let gi_xs, gi = new_tvar env xs qi.tk in
                  let gi_ps = Util.mk_typ_app_explicit (mk_Typ_uvar(gi) r) ps in
                  Inl gi_xs, TProb(ctr + 1, EQ, gi_ps, qi)
                | Inr qi -> 
                  let gi_xs, gi = new_evar env xs qi.tk in
                  let gi_ps = Util.mk_exp_app_explicit (mk_Exp_uvar(gi) r) ps in
                  Inr gi_xs, EProb(ctr + 1, EQ, gi_ps, qi)) |> List.unzip in

            let im = mk_curried_tlam xs (mk_typ_app_explicit h gs_xs) in
            let probs = extend_subst (UT(uv, im)) probs in
            solve false env ({probs with attempting=sub_probs@probs.attempting}) in

        let project i = 
            //U p1..pn =?= h q1..qm
            //extend subst: U -> \x1..xn. xi(G1(x1...xn) ... Gk(x1..xm)) ... where k is the arity of ti
            //sub-problems: pi(G1(p1..pn)..Gk(p1..pn)) =?= h q1..qm
            let ps, h, qs, xs = subterms () in
            let pi = List.nth ps i in
            let rec gs k = match k.n with 
                | Kind_unknown
                | Kind_effect -> failwith "Impossible"
                | Kind_type -> [], []
                | Kind_abbrev(_, k) -> gs k
                | Kind_uvar((uv,_)) -> failwith "Impossible" //??? ...what to do here ... constrain it to Kind_type and proceed?
                | Kind_dcon(xopt, t, k, _) -> 
                  let gi_xs, gi = new_evar env xs t in
                  let gi_xs = Tc.Normalize.eta_expand_exp env gi_xs in
                  let gi_ps = Util.mk_exp_app_explicit (mk_Exp_uvar gi r) ps in
                  let k' = match xopt with 
                    | None -> k
                    | Some x -> Util.subst_kind (mk_subst [Inr(x, gi_xs)]) k in 
                  let g_xs, g_ps = gs k' in
                  Inr gi_xs::g_xs, Inr gi_ps::g_ps 
                | Kind_tcon(aopt, k1, k2, _) -> 
                  let gi_xs, gi = new_tvar env xs k1 in
                  let gi_xs = Tc.Normalize.eta_expand env gi_xs in
                  let gi_ps = Util.mk_typ_app_explicit (mk_Typ_uvar gi r) ps in
                  let k2' = match aopt with
                    | None -> k2
                    | Some a -> Util.subst_kind (mk_subst [Inl(a, gi_xs)]) k2 in
                  let g_xs, g_ps = gs k2' in
                  Inl gi_xs::g_xs, Inl gi_ps::g_ps in
            match pi, List.nth xs i with 
                | Inl pi, Inl xi -> 
                    let head_i, _ = Util.flatten_typ_apps pi in 
                    let matchable = match head_i.n, h.n with 
                        | Typ_btvar x, Typ_btvar y -> Util.bvar_eq x y
                        | Typ_const f, Typ_const g -> Util.fvar_eq f g
                        | Typ_uvar _, _ -> true
                        | _ -> false in
                    if not matchable then None
                    else let g_xs, g_ps = gs xi.sort in 
                         let proj = Util.mk_curried_tlam xs (Util.mk_typ_app_explicit (Util.btvar_to_typ xi) g_xs) in
                         let sub = TProb(ctr + 1, EQ, Util.mk_typ_app_explicit (Util.btvar_to_typ xi) g_ps, t2) in
                         let probs = extend_subst (UT(uv, proj)) probs in
                         solve false env {probs with attempting=sub::probs.attempting}
                | _ -> None in
        let n = List.length args_lhs in
        let rec imitate_or_project i = 
            if i >= n then None
            else if i = -1 
            then match imitate () with 
                   | None -> imitate_or_project (i + 1) //backtracking point
                   | sol -> sol
            else match project i with 
                   | None -> imitate_or_project (i + 1) //backtracking point
                   | sol -> sol in
                     
        begin match pat_vars [] args_lhs with 
            | Some vars -> 
              let fvs1 = Util.freevars_typ t1 in
              let fvs2 = Util.freevars_typ t2 in
              let uvs = Util.uvars_in_typ t2 in 
              if Util.set_is_subset_of fvs2.ftvs fvs1.ftvs
                && Util.set_is_subset_of fvs2.fxvs fvs1.fxvs
                && not (Util.set_mem (uv,k) uvs.uvars_t)
              then //fast solution for flex-pattern/rigid case
                   let sol = mk_curried_tlam vars t2 in
                   solve top env (extend_subst (UT(uv, sol)) probs)
              else imitate_or_project -1
            | None -> imitate_or_project -1
        end

      | _, Typ_meta(Meta_uvar_t_app _) -> //rigid-flex
        solve_t top env EQ t2 t1 probs //re-orient


      | Typ_app _, _
      | Typ_dep _, _
      | _, Typ_app _
      | _, Typ_dep _ -> failwith "NYI"

and solve_e (top:bool) (env:Env.env) rel e1 e2 probs : solution = failwith "NYI"

and solve_c (top:bool) (env:Env.env) rel c1 c2 probs : solution = failwith "NYI"
                  
let rec krel rel env k k' : option<guard(* Type *)> =
  let k, k' = compress_kind k, compress_kind k' in
  if Util.physical_equality k k' then Some Trivial else
  //printfn "krel: %s and %s" (Print.kind_to_string k) (Print.kind_to_string k');
  match k.n, k'.n with 
    | Kind_type, Kind_type
    | Kind_effect, Kind_effect -> ret <| Some Trivial
    
    | Kind_tcon(aopt, k1, k2, _), Kind_tcon(bopt, k1', k2', _) -> 
      andf (krel rel env k1' k1)
          (fun () -> match aopt, bopt with 
            | None, _
            | _, None -> krel rel env k2 k2'
            | Some a, Some b -> 
              //printfn "Sub'ing %s for %s\n" b.realname.idText a.realname.idText;
              let k2' = Util.subst_kind (mk_subst [Inl(b, Util.bvd_to_typ a k1')]) k2' in
              krel rel env k2 k2')

    | Kind_dcon(xopt, t1, k1, _), Kind_dcon(yopt, t1', k1', _) -> 
      bindf (trel false rel env t1' t1) (fun f -> 
        let g = match xopt, yopt with 
          | None, _
          | _, None -> krel rel env k1 k1'
          | Some x, Some y -> 
            let k1' = Util.subst_kind (mk_subst [Inr(y, Util.bvd_to_exp x t1')]) k1' in
            krel rel env k1 k1' in
          bindf g (fun g ->
          ret <| (Some <| conj_guard (close_guard_lam None t1' f) g)))
    
    | Kind_uvar uv, _ -> 
      if unify_kind (uv, ()) k'
      then Some Trivial 
      else if !Options.debug <> [] 
      then (Util.print_string (Util.format2 "Incompatible kinds: %s and %s\n" (Print.kind_to_string k) (Print.kind_to_string k')); None)
      else None
    
    | _, Kind_uvar uv -> 
      if unify_kind (uv, ()) k
      then Some Trivial 
      else if !Options.debug <> [] 
      then (Util.print_string (Util.format2 "Incompatible kinds: %s and %s\n" (Print.kind_to_string k) (Print.kind_to_string k')); None)
      else None
    
    | Kind_abbrev(_, k), _ -> krel rel env k k'
    | _, Kind_abbrev(_, k') -> krel rel env k k'
    
    | _ -> 
      if !Options.debug <> []
      then (Util.print_string <| Util.format2 "incompatible kinds: %s and %s\n" (Print.kind_to_string k) (Print.kind_to_string k'); None)
      else None

and trel top rel env t t' : option<guard (* has kind t => Type when top and t:Type, otherwise Type *)> = 
  let rec reduce t =
    let t = compress_typ t in 
    match t.n with 
    | Typ_app(t1, t2, _) -> 
      (match (compress_typ t1).n with 
        | Typ_tlam(a, k, t) -> reduce (subst_typ' [Inl(a, t2)] t)
        | _ -> t)
    | Typ_dep(t1, v, _) -> 
      (match (compress_typ t1).n with 
        | Typ_lam(x, _, t) -> reduce (subst_typ' [Inr(x, v)] t)
        | _ -> t)
    | _ -> t in
  let mk_guard_lam top t f = 
    if not top then f 
    else match t.tk.n with 
           | Kind_type -> mk_guard_lam t f
           | _ -> f in
  let rec aux top norm t t' = 
    let t = Util.compress_typ t in
    let t' = Util.compress_typ t' in
    if Microsoft.FStar.Util.physical_equality t t' 
    then (Some Trivial)
    else (//if Tc.Env.debug env then Util.print_string <| format2 "trel: %s \t\t %s\n" (Print.typ_to_string t) (Print.typ_to_string t');
          let r = aux' top norm t t' in r
//          match !Options.debug, r with
//              | _::_, None -> Util.print_string <| Util.format2 "Incompatible types %s and %s\n" (Print.typ_to_string t) (Print.typ_to_string t'); None
//              | _ -> r 
         )
  and aux' top norm t t' =
    let t, t' = reduce t, reduce t' in
      match t.n, t'.n with 
       | Typ_btvar a1, Typ_btvar a1' -> 
         if Util.bvd_eq a1.v a1'.v 
         then Some <| Trivial
         else None

       | Typ_const c1, Typ_const c1' -> 
         if Util.fvar_eq c1 c1' then Some Trivial
         else if not norm
         then aux top true (normalize env t) (normalize env t') 
         else None

       | Typ_fun(Some x, t1, c, _), Typ_fun(Some x', t1', c', _)  -> 
         let sc' = if Util.bvd_eq x x' then c' else Util.subst_comp' [Inr(x', Util.bvd_to_exp x t1')] c' in
         bindf (aux false norm t1' t1) (fun f -> 
         bindf (crel rel env c sc') (fun g -> 
         let g = conj_guard f <| close_guard (Inl(x, t1')) g in
         ret <| Some (mk_guard_lam top t g)))

       | Typ_fun(xopt, t1, c, _), Typ_fun(yopt, t1', c', _)  -> 
         bindf (aux false norm t1' t1) (fun f -> 
         bindf (crel rel env c c') (fun g -> 
          let g = match xopt, yopt with 
            | Some x, None 
            | None, Some x -> close_guard (Inl(x, t1')) g 
            | _ -> g in
          let g = conj_guard f g in
          ret <| Some (mk_guard_lam top t g)))

       | Typ_univ(a1, k1, c), Typ_univ(a1', k1', c') -> 
         let sc' = if Util.bvd_eq a1 a1' then c' else Util.subst_comp' [Inl(a1', Util.bvd_to_typ a1 k1')] c' in
         bindf (krel rel env k1' k1) (fun f -> 
         bindf (crel rel env c sc') (fun g -> 
         let g = close_guard (Inr(a1, k1')) g in
         ret <| Some (mk_guard_lam top t <| conj_guard f g)))
      
       | Typ_lam(x, t1, t2), Typ_lam(x', t1', t2') ->
         bindf (aux false norm t1' t1) (fun f -> 
         bindf (aux false norm t2 (Util.subst_typ' [Inr(x', Util.bvd_to_exp x t1')] t2')) (fun g -> 
         let g = close_guard (Inl(x, t1')) g in
         ret <| Some (mk_guard_lam top t <| conj_guard f g)))
     
       | Typ_tlam(a1, k1, t1), Typ_tlam(a1', k1', t1') ->
         bindf (krel rel env k1' k1) (fun f -> 
         bindf (aux false norm t1 (Util.subst_typ' [Inl(a1', Util.bvd_to_typ a1 k1')] t1')) (fun g -> 
         let g = close_guard (Inr(a1, k1')) g in
         ret <| Some (mk_guard_lam top t <| conj_guard f g))) 
     
       | Typ_uvar(uv, _), Typ_uvar(uv', _) when Unionfind.equivalent uv uv' -> 
         Some Trivial
           
       | Typ_uvar(uv, k), _ -> 
         if unify_typ env (uv, k) t' 
         then Some Trivial
         else None

       | _, Typ_uvar(uv, k) -> 
         if unify_typ env (uv, k) t 
         then Some Trivial
         else None
     
       | Typ_app _, _
       | Typ_dep _, _
       | _, Typ_app _
       | _, Typ_dep _  -> 
         let tc, args = Util.flatten_typ_apps t in
         let tc', args' = Util.flatten_typ_apps t' in
         let matches = 
          if List.length args = List.length args' 
          then bindf (andf (aux false norm tc tc') (fun () -> 
                      forallf (List.zip args args') (function 
                         | Inl t1, Inl t1' -> aux false true t1 t1'
                         | Inr e1, Inr e1' -> exp_equiv env e1 e1'
                         | _ -> None))) (fun f ->
               Some (mk_guard_lam top t f)) 
          else None in
         orf matches (fun () -> 
          if not norm 
          then aux top true (Normalize.norm_typ [Normalize.DeltaHard;Normalize.Beta] env t)
                            (Normalize.norm_typ [Normalize.DeltaHard;Normalize.Beta] env t')
          else None)

       | Typ_refine(x, t1, phi1), Typ_refine(x', t1', phi2) -> 
         let xexp = Util.bvd_to_exp x t1 in
         let finish f g = 
            if top 
            then let f = map_guard f (fun f -> syn f.pos mk_Kind_type <| mk_Typ_dep(f, xexp, false)) in
                 let gf = conj_guard g f in
                 ret (Some <| map_guard gf (fun gf -> syn t.pos (mk_Kind_dcon(None, t, mk_Kind_type, false) t.pos) <| mk_Typ_lam(x, t, gf)))
            else let g = close_guard (Inl(x, t1)) g in 
                 ret <| (Some <| conj_guard f g) in
         bindf (aux top norm t1 t1') (fun f -> 
         match rel with
          | EQ -> 
            bindf (aux false norm phi1 (Util.subst_typ' [Inr(x', xexp)] phi2)) (finish f)

          | SUB -> 
            let g = mkGuard env <| Util.mk_imp phi1 (Util.subst_typ' [Inr(x', xexp)] phi2) in
            finish f g)

       | Typ_refine(x, t1, phi), _  when (rel=SUB) -> 
         bindf (aux top norm t1 t') (fun f ->
         if top 
         then let xexp = Util.bvd_to_exp x t1 in
              let f = map_guard f (fun f ->
                syn t.pos (mk_Kind_dcon(None, t, mk_Kind_type, false) t.pos) <| 
                    mk_Typ_lam(x, t, Util.mk_imp phi (syn f.pos mk_Kind_type <| mk_Typ_dep(f, xexp, false)))) in
              ret <| Some f
         else ret <| Some (map_guard f (fun f -> close (Inl(x, t1)) (Util.mk_imp phi f))))
                   
       | _, Typ_refine(x, t', phi) when (rel=SUB) -> 
         bindf (aux top norm t t') (fun f -> 
         if top 
         then let xexp = Util.bvd_to_exp x t in
              let f = map_guard f (fun f -> syn f.pos mk_Kind_type <| mk_Typ_dep(f, xexp, false)) in
              let phi_f = conj_guard (mkGuard env phi) f in
              ret <| (Some <| map_guard phi_f (fun phi_f -> 
                syn phi_f.pos (mk_Kind_dcon(None, t, mk_Kind_type, false) t.pos) <| mk_Typ_lam(x, t, phi_f)))
         else let f = conj_guard (mkGuard env phi) f in
              ret <| (Some <| map_guard f (close (Inl(x, t)))))

       | Typ_unknown, _ 
       | _, Typ_unknown -> failwith "Impossible"

       | _ -> None in

  aux top false t t'

and exp_equiv env e e' : option<guard (* has kind Type *)> = 
  if Util.physical_equality e e' then Some Trivial
  else let r = exp_equiv' env e e' in 
       match !Options.debug, r with 
        | _::_, None -> Util.print_string <| Util.format2 "Incompaible expressions: %s and %s\n" (Print.exp_to_string e) (Print.exp_to_string e'); None
        | _ -> r

and exp_equiv' env e e' : option<guard (* has kind Type *)> = 
  let e, e' = compress_exp e, compress_exp e' in 
  match e.n, e'.n with 
    | Exp_uvar(uv, t), _ -> 
      if unify_exp (uv, t) e'
      then Some Trivial
      else None

    | _, Exp_uvar(uv, t) -> 
      if unify_exp (uv, t) e
      then Some Trivial
      else None

    | Exp_bvar x1, Exp_bvar x1' -> 
      if Util.bvd_eq x1.v x1'.v
      then Some Trivial
      else ret <| Some (NonTrivial <| Util.mk_eq e e')

    | Exp_fvar (fv1, _), Exp_fvar (fv1', _) -> 
      if lid_equals fv1.v fv1'.v
      then Some Trivial
      else ret <| Some (NonTrivial <| Util.mk_eq e e')

    | Exp_constant s1, Exp_constant s1' -> 
      if const_eq s1 s1'
      then Some Trivial
      else None

    | Exp_ascribed(e1, _), Exp_ascribed(e1', _) -> 
      exp_equiv env e1 e1'

    | _ ->
      ret <| Some (NonTrivial <| Util.mk_eq e e')

and const_eq s1 s2 = match s1, s2 with 
  | Const_bytearray(b1, _), Const_bytearray(b2, _) -> b1=b2
  | Const_string(b1, _), Const_string(b2, _) -> b1=b2
  | _ -> s1=s2 

and crel rel env c1 c2 : option<guard> = 
  let rec aux norm (c1:comp) (c2:comp) = 
    if Util.physical_equality c1 c2 then Some Trivial
    else let c1 = compress_comp c1 in
         let c2 = compress_comp c2 in
         //check_sharing (Util.comp_result c1) (Util.comp_result c2) "crel0";
         match rel with 
           | EQ -> 
             begin match c1.n, c2.n with
               | Total t1, Total t2 -> trel false rel env t1 t2
               | Total _,  _ -> crel rel env (mk_Comp <| force_comp c1) c2
               | _, Total _ -> crel rel env c1 (mk_Comp <| force_comp c2)
               | Comp ct1, Comp ct2 ->
                 if lid_equals ct1.effect_name ct2.effect_name
                 then either_rel rel env (Inl ct1.result_typ::ct1.effect_args) (Inl ct2.result_typ::ct2.effect_args) 
                 else if not norm 
                 then aux true (mk_Comp <| Normalize.norm_comp [Normalize.DeltaComp] env c1)
                               (mk_Comp <| Normalize.norm_comp [Normalize.DeltaComp] env c2)
                 else None
               | Flex (u, t1), Comp ct2
               | Comp ct2, Flex (u, t1) -> 
                 bindf (trel false EQ env t1 ct2.result_typ) (fun f -> 
                   Unionfind.change u (Resolved c1);
                   Some f)
               | Flex (u1, t1), Flex (u2, t2) -> 
                 bindf (trel false EQ env t1 t2) (fun f -> 
                   if (Unionfind.equivalent u1 u2) 
                   then Some f
                   else (Unionfind.union u1 u2; Some f))
             end
               
           | SUB -> 
             match c1.n, c2.n with 
               | Total t1, Total t2 -> trel false SUB env t1 t2
               | Total t1, Flex (u, t2) -> 
                 bindf (trel false SUB env t1 t2) (fun f -> 
                   Unionfind.change u (Resolved (mk_Total t2));
                   Some f)
               | Flex(u, t1), Total t2 -> 
                 bindf (trel false SUB env t1 t2) (fun f -> 
                   Unionfind.change u (Resolved c2);
                   Some f)
               | Total _,  _ -> crel SUB env (mk_Comp <| force_comp c1) c2
               | _, Total _ -> crel SUB env c1 (mk_Comp <| force_comp c2)
               | Comp _, Comp _ -> 
                 let c1 = Normalize.weak_norm_comp env c1 in
                 let c2 = Normalize.weak_norm_comp env c2 in
                 //check_sharing (c1.result_typ) (c2.result_typ) "crel1";
                 begin match Tc.Env.monad_leq env c1.effect_name c2.effect_name with
                   | None -> None
                   | Some edge ->
                     let wpc1, wpc2 = match c1.effect_args, c2.effect_args with 
                       | Inl wp1::_, Inl wp2::_ -> wp1, wp2 
                       | _ -> failwith (Util.format2 "Got effects %s and %s, expected normalized effects" (Print.sli c1.effect_name) (Print.sli c2.effect_name)) in
                     andf (trel false SUB env c1.result_typ c2.result_typ) (fun f -> 
                       let c2_decl : monad_decl = Tc.Env.get_monad_decl env c2.effect_name in
                       let is_wpc2_null () = 
                         if not !Options.verify then false
                         else match trel true EQ env wpc2 (Util.mk_typ_app_explicit c2_decl.null_wp [Inl c2.result_typ]) with 
                           | Some Trivial -> true
                           | _ -> false in
                       if Util.physical_equality wpc1 wpc2
                       then ret <| Some Trivial
                       else if is_wpc2_null() 
                       then let _ = if debug env then Util.print_string "Using trivial wp ... \n" in
                            let t = Util.mk_typ_app_explicit c2_decl.trivial [Inl c1.result_typ; Inl <| edge.mlift c1.result_typ wpc1] in
                            ret <| Some (mkGuard env <| {t with tk=mk_Kind_type})
                       else let t = Util.mk_typ_app_explicit c2_decl.wp_binop [Inl c2.result_typ; Inl wpc2; Inl <| Util.ftv Const.imp_lid (Const.kbin ktype ktype ktype); 
                                                                               Inl <| edge.mlift c1.result_typ wpc1] in
                            let t = {t with tk=wpc2.tk} in
                            let t = Util.mk_typ_app_explicit c2_decl.wp_as_type [Inl c2.result_typ; Inl t] in
                            ret <| Some (NonTrivial <| {t with tk=mk_Kind_type})) 
                 end
                   
               | Flex(u, t), Comp ct2 -> 
                 bindf (trel false SUB env t ct2.result_typ) (fun f -> 
                   Unionfind.change u (Resolved c2);
                   Some f)
               | Comp ct2, Flex(u, t) -> 
                 bindf (trel false SUB env ct2.result_typ t) (fun f -> 
                   Unionfind.change u (Resolved c1);
                   Some f)

               | Flex(u1, t1), Flex(u2, t2) -> 
                 bindf (trel false SUB env t1 t2) (fun f -> 
                   (if not (Unionfind.equivalent u1 u2)
                    then Unionfind.union u1 u2); (* TODO: Fix precedence of the ';' *)
                   Some f) in
  aux false c1 c2

and either_rel rel env l1 l2 = 
  forallf (List.zip l1 l2) (function 
    | Inl t1, Inl t2 -> trel false rel env t1 t2
    | Inr e1, Inr e2 -> exp_equiv env e1 e2
    | _ -> None)

let keq env t k1 k2 : guard = 
  match krel EQ env (norm_kind [Beta] env k1) (norm_kind [Beta] env k2) with 
    | Some f -> f
    | None -> 
      let r = match t with 
        | None -> Tc.Env.get_range env
        | Some t -> t.pos in
      match t with 
        | None -> raise (Error(Tc.Errors.incompatible_kinds k2 k1, r))
        | Some t -> raise (Error(Tc.Errors.expected_typ_of_kind k2 t k1, r))

let teq env t1 t2 : guard = 
  match trel true EQ env (norm_typ [Beta] env t1) (norm_typ [Beta] env t2) with
    | Some f -> f
    | None -> raise (Error(Tc.Errors.basic_type_error None t2 t1, Tc.Env.get_range env))

let try_subtype env t1 t2 = trel true SUB env t1 t2 

let subtype env t1 t2 : guard = 
  match try_subtype env t1 t2 with
    | Some f -> f
    | None -> 
     Util.fprint2 "Incompatible types %s\nand %s\n" (Print.typ_to_string t1) (Print.typ_to_string t2);
     raise (Error(Tc.Errors.basic_type_error None t2 t1, Tc.Env.get_range env))

let trivial_subtype env eopt t1 t2 = 
  let f = try_subtype env t1 t2 in 
  match f with 
    | Some Trivial -> ()
    | None 
    | Some (NonTrivial _) ->  
      let r = match eopt with 
        | None -> Tc.Env.get_range env
        | Some e -> e.pos in
      raise (Error(Tc.Errors.basic_type_error eopt t2 t1, r))

let sub_comp env c1 c2 = crel SUB env c1 c2
