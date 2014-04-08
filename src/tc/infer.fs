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
module Microsoft.FStar.Tc.Infer

open Microsoft.FStar
open Microsoft.FStar.Tc
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util

let check_expected_typ env e = 
  match Env.expected_typ env with 
  | None -> e, e.sort
  | Some t -> 
     Tc.Util.subtype env e.sort t;
     withinfo (Exp_ascribed(e, t)) t e.p, t

let rec tc_kind env k : kind = 
  let k = Util.compress_kind k in 
  match k with
  | Kind_uvar _
  | Kind_star -> k

  | Kind_tcon (aopt, k1, k2) -> 
    let k1' = tc_kind env k1 in 
    let env' = match aopt with 
      | None -> env 
      | Some a -> Env.push_local_binding env (Env.Binding_typ(a, k1')) in
    let k2' = tc_kind env k2 in
    Kind_tcon(aopt, k1', k2')

  | Kind_dcon (xopt, t1, k2) ->
    let t1', _ = tc_typ env t1 in
    let env' = match xopt with 
      | None -> env
      | Some x -> Env.push_local_binding env (Env.Binding_var(x, t1')) in
    let k2' = tc_kind env' k2 in
    Kind_dcon(xopt, t1', k2')

  | Kind_unknown -> 
    Tc.Util.new_kvar env

and tc_typ env t : typ * kind = 
  let t = Util.compress_typ t in
  match t with 
  | Typ_btvar a -> 
    let k = Env.lookup_btvar env a in
    t, k

  | Typ_const i -> 
    let k = Env.lookup_typ_lid env i.v in 
    t, k

  | Typ_fun(xopt, t1, t2, imp) -> 
    let t1' = tc_typ_check env t1 Kind_star in
    let env' = match xopt with 
      | None -> env
      | Some x -> Env.push_local_binding env (Env.Binding_var(x, t1')) in
    let t2' = tc_typ_check env' t2 Kind_star in
    Typ_fun(xopt, t1', t2', imp), Kind_star

  | Typ_univ(a, k1, t1) -> 
    let k1' = tc_kind env k1 in 
    let env' = Env.push_local_binding env (Env.Binding_typ(a, k1')) in
    let t1' = tc_typ_check env' t1 Kind_star in 
    Typ_univ(a, k1', t1'), Kind_star

  | Typ_refine(x, t1, t2) -> 
    let t1' = tc_typ_check env t1 Kind_star in
    let env' = Env.push_local_binding env (Env.Binding_var(x, t1')) in
    let t2' = tc_typ_check env' t2 Kind_star in
    Typ_refine(x, t1', t2'), Kind_star

  | Typ_app(t1, t2) -> 
    let t1', k1' = tc_typ env t1 in 
    let aopt, karg, kres = match Util.compress_kind k1' with 
      | Kind_tcon(aopt, karg, kres) -> aopt, karg, kres
      | Kind_uvar uv ->  (* inference never introduces a dependent function *)
        let karg, kres = Tc.Util.new_kvar env, Tc.Util.new_kvar env in 
        Tc.Util.kind_equiv env (Kind_uvar uv) (Kind_tcon(None, karg, kres));
        None, karg, kres
      | _ -> raise (Error(Tc.Errors.expected_arrow_kind k1', Env.get_range env)) in
    let t2' = tc_typ_check env t2 karg in
    let k2 = match aopt with 
      | None -> kres
      | Some a -> Util.subst_kind [Inl(a, t1')] kres in
    t2', k2
    
  | Typ_dep(t1, e1) -> 
    let t1', k1' = tc_typ env t1 in
    let xopt, targ, kres = match Util.compress_kind k1' with 
      | Kind_dcon(xopt, targ, kres) -> xopt, targ, kres
      | Kind_uvar uv -> (* inference never introduces a dependent function *)
        let targ, kres = Tc.Util.new_tvar env Kind_star, Tc.Util.new_kvar env in 
        Tc.Util.kind_equiv env (Kind_uvar uv) (Kind_dcon(None, targ, kres));
        None, targ, kres
      | _ -> raise (Error(Tc.Errors.expected_arrow_kind k1', Env.get_range env)) in
    let env' = Env.set_expected_typ env targ in
    let e1', _ = tc_exp env' e1 in
    let k2 = match xopt with 
      | None -> kres
      | Some x -> Util.subst_kind [Inr(x, e1')] kres in
    Typ_dep(t1', e1'), k2
  
  | Typ_lam(x, t1, t2) -> 
    let t1', k1 = tc_typ env t1 in 
    let env' = Env.push_local_binding env (Env.Binding_var(x, t1')) in
    let t2', k2 = tc_typ env' t2 in
    Typ_lam(x, t1', t2'), Kind_dcon(Some x, t1', k2)

  | Typ_tlam(a, k1, t1) -> 
    let k1' = tc_kind env k1 in 
    let env' = Env.push_local_binding env (Env.Binding_typ(a, k1')) in 
    let t1', k2 = tc_typ env t1 in 
    Typ_tlam(a, k1', t1'), Kind_tcon(Some a, k1', k2)

  | Typ_ascribed(t1, k1) -> 
    let k1' = tc_kind env k1 in 
    let t1' = tc_typ_check env t1 k1' in
    Typ_ascribed(t1', k1'), k1'

  | Typ_uvar(u, k1) -> 
    t, k1

  | Typ_meta (Meta_pos(t, r)) -> 
    let env' = Env.set_range env r in
    let t', k = tc_typ env' t in 
    Typ_meta(Meta_pos(t', r)), k

  | Typ_unknown -> 
    let k = Tc.Util.new_kvar env in 
    let t = Tc.Util.new_tvar env k in 
    t, k   

and tc_typ_check env t k : typ = 
  let t', k' = tc_typ env t in
  Tc.Util.kind_equiv env k k';
  t'       

and tc_exp env e : exp * typ = match e.v with 
  | Exp_bvar x -> 
    let t = Env.lookup_bvar env x in 
    check_expected_typ env ({e with sort=t})

  | Exp_fvar(v, dc) -> 
    let t = Env.lookup_lid env v.v in
    if dc &&  not (Env.is_datacon env v.v)
    then failwith "Expected a data constructor"
    else check_expected_typ env ({e with sort=t})

  | Exp_constant c -> 
    let t = Tc.Util.typing_const env c in
    check_expected_typ env ({e with sort=t})

  | Exp_abs(x, t1, e1) -> 
    let t1', k1 = tc_typ env t1 in
    let env, topt = Env.clear_expected_typ env in
    let targ, env', implicit = match topt with 
      | Some t -> 
        (match Util.compress_typ t with 
          | Typ_fun(xopt, targ, tres, implicit) -> 
            Tc.Util.typ_equiv env targ t1';
            let tres = match xopt with 
              | None -> tres
              | Some y -> Util.subst_typ [Inr(y, Util.bvd_to_exp x targ)] tres in
            targ, Env.set_expected_typ env tres, implicit
          | _ -> t1', env, false)
      | None -> 
        t1', env, false in
    let e1', tres = tc_exp (Env.push_local_binding env' (Env.Binding_var(x, targ))) e1 in 
    let t = Typ_fun(Some x, targ, tres, implicit) in
    withinfo (Exp_abs(x, targ, e1')) t e.p, t

  | Exp_tabs(a, k1, e1) -> 
    let k1' = tc_kind env k1 in 
    let env, topt = Env.clear_expected_typ env in 
    let karg, env' = match topt with 
      | Some t -> 
        (match Util.compress_typ t with 
          | Typ_univ(b, karg, tres) -> 
            Tc.Util.kind_equiv env karg k1';
            let tres = Util.subst_typ [Inl(b, Util.bvd_to_typ a karg)] tres in
            karg, Env.set_expected_typ env tres
          | _ -> k1', env)
      | None -> 
        k1', env in
    let e1', tres = tc_exp (Env.push_local_binding env' (Env.Binding_typ(a, karg))) e1 in 
    let t = Typ_univ(a, karg, tres) in
    withinfo (Exp_tabs(a, karg, e1')) t e.p, t

  | Exp_app(e1, e2, imp) -> 
    let env1, _ = Env.clear_expected_typ env in
    let e1', t1 = tc_exp env1 e1 in
    let xopt, env2, tres = match Tc.Util.destruct_function_typ env t1 with 
      | Some (Typ_fun(xopt, targ, tres, implicit)) -> 
        let env2 = Env.set_expected_typ env targ in
        xopt, env2, tres
      | _ -> 
        raise (Error(Tc.Errors.expected_function_typ t1, e1.p)) in
    let e2', t2 = tc_exp env2 e2 in 
    let t = match xopt with 
      | None -> tres
      | Some y -> Util.subst_typ [Inr(y, e2')] tres in
    check_expected_typ env (withinfo (Exp_app(e1', e2', imp)) t e.p)
       
  | Exp_tapp(e1, t1) -> failwith "NYI"
  | Exp_match(e1, eqns) -> failwith "NYI"
  | Exp_ascribed(e1, t1) -> failwith "NYI"
  | Exp_let(is_rec, lbs, e1) -> failwith "NYI"
  | Exp_primop(op, es) -> failwith "NYI"
  | Exp_uvar(u, t1) -> failwith "NYI"

and tc_pat env p : pat * typ = match p with 
  | Pat_cons(l, pats) -> failwith "NYI"
  | Pat_var(x) -> failwith "NYI"
  | Pat_tvar(a) -> failwith "NYI"
  | Pat_constant c -> failwith "NYI"
  | Pat_disj pats -> failwith "NYI"
  | Pat_wild  -> failwith "NYI"
  | Pat_twild  -> failwith "NYI"

