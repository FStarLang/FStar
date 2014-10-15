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
 module Microsoft.FStar.MonadicUtils

 open Util
 open Absyn
 open AbsynUtils
 open MonadicPretty
 open Profiling
 open KindAbbrevs

#if MONO
 module Z3Enc = Z3Exe.Query
#else
 module Z3Enc = Z3Encoding.Query
#endif

 (*****************************************************************************)
 (*                              Sanity checking                              *)
 (*****************************************************************************)
 let check_bvar_identity msg t = 
   if not (AbsynUtils.check_bvar_identity t)
   then (pr "<%s>Bvar identity broken for type %s\n" msg (t.ToString()); raise Impos)
   else ()
 let check_bvar_identity_opt msg = function None -> () | Some t -> check_bvar_identity msg t

 let unrefine_kte red (tcenv:Tcenv.env) (t:'a) : 'a =  
   let res, _ = red
     (fun v _ _ -> v)
     (fun _ v _ env binders t -> 
        match t.sort(* .u *), (compress t).v with 
          | Kind_prop, Typ_const _
          | Kind_affine, Typ_const _
          | Kind_star, Typ_const _ -> 
              v env binders (Tcutil.reduce_typ_delta_beta tcenv t)
          | _, Typ_refine(_, t1, _, _) -> v env binders t1 
          | _ -> v env binders t )
     (fun _ _ v -> v)
     combine_kind
     (fun t (kl, tl, el) env -> 
         match t.v with 
          | Typ_refine(x, t1, phi, ghost) -> let [t1';t2'] = tl in t1', env
          | _ -> combine_typ t (kl, tl, el) env)
     combine_exp
     () [] t in 
     res
 let unrefine_typ = unrefine_kte AbsynUtils.reduce_typ
 let unrefine_kind = unrefine_kte AbsynUtils.reduce_kind 
 let unrefine_exp = unrefine_kte AbsynUtils.reduce_exp 

 (* Check for Typ_unknown or Kind_unknown anywhere in the AST. *)
 let contains_unknown red e : bool =
   let _, res = red 
     (fun v _ _ b binders k -> match k(* .u *) with 
        | Kind_unknown -> v true binders k
        | _ -> v b binders k)
     (fun _ v _ b binders t -> match t.v with 
        | Typ_unknown -> v true binders t
        | _ -> v b binders t)
     (fun _ _ v -> v)
     (fun _ _ b -> (), b)
     (fun _ _ b -> (), b)
     (fun _ _ b -> (), b)
     false [] e in 
     res
 let kind_contains_unknown = contains_unknown AbsynUtils.reduce_kind
 let typ_contains_unknown = contains_unknown AbsynUtils.reduce_typ
 let exp_contains_unknown = contains_unknown AbsynUtils.reduce_exp

 let contains_refinement tcenv red t : bool =
   let _, res = red 
     (fun v _ _ -> v)
     (fun _ v _ b binders t -> match t.v with 
        | Typ_refine _ -> (), true
        | _ -> v b binders t)
     (fun _ _ v -> v)
     (fun _ _ b -> (), b)
     (fun _ _ b -> (), b)
     (fun _ _ b -> (), b)
     false [] t in 
     res
 let kind_contains_refinement env =
   contains_refinement env AbsynUtils.reduce_kind
 let typ_contains_refinement env =
   contains_refinement env AbsynUtils.reduce_typ 
 let exp_contains_refinement env =
   contains_refinement env AbsynUtils.reduce_exp

 (*****************************************************************************)
 (*                      Alpha conversion and label freshening                *)
 (*****************************************************************************)
 type benv = list<Disj<btvdef*btvar, bvvdef*bvvar>>
 let alpha_fresh_labels' range t =
   let rstr = Range.string_of_range range in
   let red rk rt vz binders (env:benv) (l,z) f = match l with 
     | Inl(aopt, k) -> 
         let k, env = rk env binders k in 
         let binders', bopt, env' = match aopt with 
           | None -> binders, None, env
           | Some a -> 
               let binders' = Inl a::binders in
               let b = gen_bvar_p (range_of_bvd a) k in
               let env' = Inl(a,b)::env in 
                 binders', Some b.v, env' in 
         let z, _ = vz env' binders' z in 
           f (Inl(bopt, k), z), env

     | Inr(xopt, t1) -> 
         let t1, env = rt env binders t1 in 
         let binders', yopt, env' = match xopt with 
           | None -> binders, None, env
           | Some x -> 
               let y = gen_bvar_p t1.p t1 in 
                 (Inr x)::binders, Some (y.v), (Inr (x, y))::env in 
         let z, _ = vz env' binders' z in 
           f (Inr(yopt,t1), z), env in 

     fst <| AbsynUtils.reduce_typ 
         (fun vk rt _ env binders k -> 
            let red = red vk rt vk binders env in 
              match k with 
                | Kind_tcon(aopt, k1, k2) -> 
                    red (Inl(aopt, k1), k2) (fun (Inl(bopt, k1), k2) -> Kind_tcon(bopt, k1, k2))
                | Kind_dcon(xopt, t, k) -> 
                    red (Inr(xopt, t), k) (fun (Inr(yopt, t), k) -> Kind_dcon(yopt, t, k))
                | _ -> vk env binders k)
         (fun rk vt re env binders t ->
            let red x f = red rk vt vt binders env x (fun y -> twithinfo (f y) t.sort t.p) in 
              match t.v with 
                | Typ_btvar btv -> 
                    (match env |> Util.findOpt (function Inr _ -> false | Inl(btvd, _) -> bvd_eq btvd btv.v) with 
                       | None -> t,env
                       | Some (Inl (_, x)) -> 
                           twithinfo (Typ_btvar x) t.sort t.p, env
                       | _ -> raise Impos)

                | Typ_dep(({v=Typ_const(v, _)} as lbl), 
                          ({v=Exp_constant(Sugar.Const_string(bytes, p))} as str))
                    when Sugar.lid_equals Const.lbl_lid v.v -> 
                    let bytes =  Util.unicodeEncoding.GetBytes(Util.unicodeEncoding.GetString(bytes) ^ " : " ^ rstr) in 
                    let t = twithinfo (Typ_dep(lbl, ewithinfo (Exp_constant(Sugar.Const_string(bytes, p))) str.sort str.p)) t.sort t.p in 
                      t, env

                | Typ_fun(xopt, t1, t2) -> 
                    red (Inr (xopt, t1), t2) (fun (Inr(xopt, t1), t2) -> Typ_fun(xopt, t1, t2))
                | Typ_dtuple([(xopt, t1); (None, t2)]) -> 
                    red (Inr (xopt, t1), t2) (fun (Inr(xopt, t1), t2) -> Typ_dtuple([(xopt, t1); (None, t2)]))

                | Typ_lam(x, t1, t2) -> 
                    red (Inr (Some x, t1), t2) (fun (Inr(Some x, t1), t2) -> Typ_lam(x, t1, t2))
                | Typ_refine(x, t1, t2, b) -> 
                    red (Inr (Some x, t1), t2) (fun (Inr(Some x, t1), t2) -> Typ_refine(x, t1, t2, b))

                | Typ_univ(a, k, [], t) -> 
                    red (Inl (Some a, k), t) (fun (Inl(Some a,k), t) -> Typ_univ(a,k,[],t))
                | Typ_tlam(a, k, t) -> 
                    red (Inl (Some a, k), t) (fun (Inl(Some a,k), t) -> Typ_tlam(a,k,t))

                | _ -> vt env binders t) 
         (fun rk rt ve env binders e -> 
            match e.v with 
              | Exp_bvar bv -> 
                  (match env |> Util.findOpt (function Inl _ -> false | Inr(bvd, _) -> bvd_eq bvd bv.v) with 
                     | None -> e, env
                     | Some (Inr (_, x)) -> 
                         ewithinfo (Exp_bvar x) e.sort e.p, env
                     | _ -> raise Impos)

              | _ -> ve env binders e)
         combine_kind
         combine_typ
         combine_exp
         [] [] t

 let fresh_labels range t = 
   let rstr = Range.string_of_range range in
     fst <| AbsynUtils.reduce_typ 
         (fun vk _ _ -> vk)
         (fun rk vt re env binders t ->
            match t.v with 
              | Typ_dep(({v=Typ_const(v, _)} as lbl), str) 
                  when Sugar.lid_equals Const.lbl_lid v.v -> 
                  (match unascribe str with
                     | {v=Exp_constant(Sugar.Const_string(bytes, p))} -> 
                         let bytes =  Util.unicodeEncoding.GetBytes(Util.unicodeEncoding.GetString(bytes) ^ " : " ^ rstr) in 
                         let t = twithinfo (Typ_dep(lbl, ewithinfo (Exp_constant(Sugar.Const_string(bytes, p))) str.sort str.p)) t.sort t.p in 
                           t, env
                     | _ -> raise Impos)
              | _ -> vt env binders t)
         (fun _ _ ve -> ve)
         combine_kind
         combine_typ
         combine_exp
         [] [] t

 (* let alpha_fresh_labels range t =  *)
 (*   fresh_labels range <| alpha_convert t *)

 (*****************************************************************************)
 (*                             Type builders                                 *)
 (*****************************************************************************)
 type prop = typ (* types of kind E *)
 type pred = typ (* types of kind t => E or t => heap => E *)
                 (* all other typ :: * *) 
 type preds = list<pred>
 let is_Typ_unknown (t:typ) : bool =
   match t.v with
     | Typ_unknown -> true
     | _ -> false

 let mono_type env t = 
   let t' = compress t in
     match t'.v with 
       | Typ_univ _ -> false
       | _ -> true

 let is_heap_typ = function 
   | {v=Typ_const(l, _)} -> Sugar.lid_equals l.v Const.heap_lid
   | _ -> false 

 let isTrueTyp (t:typ) : bool =
   match t.v with
     | Typ_const (v,_)
       when Sugar.lid_equals v.v Const.true_lid -> true
     | _ -> false

 let mkTapp t1 t2 = 
   match t1.sort(* .u *) with 
     | Kind_tcon _ -> 
         let k = open_kind t1.sort t2 in 
           twithsort (Typ_app(t1,t2)) k 
     | _ -> pr "Unexpected type application: (%s :: %s) applied to  (%s)\n" 
         (Pretty.strTyp t1) (Pretty.strKind t1.sort) (Pretty.strTyp t2); raise Impos

 let mkDep t v = 
   let k = match t.sort(* .u *) with 
     | Kind_dcon(None, _, k) -> k
     | Kind_dcon(Some x, _, k) -> substitute_kind_exp k x v
     | _ -> raise Impos in 
     twithsort (Typ_dep(t,v)) k 

 let mkDep_l t vl =
   vl |> List.fold_left mkDep t

 let mkLam x t t' = 
   twithinfo (Typ_lam(x, t, t')) (Kind_dcon(Some x, t, t'.sort)) t'.p

 let mkTyp_tlam a k t =
   twithinfo (Typ_tlam(a,k, t)) (Kind_tcon(Some a, k, t.sort)) t.p

 let mkAnd (p1:prop) (p2:prop) = 
   (* A little optimization *)
   if isTrueTyp p1 then p2
   else if isTrueTyp p2 then p1
   else let partial = 
     twithinfo 
       (Typ_app(Const.and_typ, p1)) 
       (Kind_tcon(None, Kind_erasable, Kind_prop))
       p1.p in 
     twithinfo
       (Typ_app(partial, p2))
       Kind_prop
       p2.p

 let mkAnd_l pl = List.fold_left mkAnd Const.true_typ pl

 let mkHeapDep p hexp = match p.sort(* .u *) with 
   | Kind_dcon(_, t, _) when is_heap_typ t -> mkDep p hexp
   | _ -> p

 let mkHeapAnd_l predl = 
   let h = new_bvd None in 
   let hexp = bvd_to_exp h Const.heap_typ in
     mkLam h Const.heap_typ       
       (mkAnd_l (predl |> List.map (fun p -> mkHeapDep p hexp)))

 let mkHeapCases predl = 
   let h = new_bvd None in
   let hexp = bvd_to_exp h Const.heap_typ in
     mkLam h Const.heap_typ
       (twithsort (Typ_meta (Meta_cases (predl |> List.map (fun p -> mkHeapDep p hexp)))) Kind_erasable)

 let mkImplies (p1:prop) (p2:prop) =
   if isTrueTyp p1 then p2 
   else
     let partial = 
       twithinfo 
         (Typ_app(Const.implies_typ, p1)) 
         (Kind_tcon(None, Kind_erasable, Kind_prop))
         p1.p in 
       twithinfo
         (Typ_app(partial, p2))
         Kind_prop
         p2.p

 let mkHeapImplies p1 p2 = 
   let h = new_bvd None in 
   let hexp = bvd_to_exp h Const.heap_typ in
     mkLam h Const.heap_typ 
       (mkImplies (mkHeapDep p1 hexp) (mkHeapDep p2 hexp))

 let mkTypeOf env v t = 
   let tof = 
     let k = Tcenv.lookup_typ_lid env Const.typeof_lid in  
     let typeOf = twithsort (Typ_const(fvwithsort Const.typeof_lid k, None)) k in 
     let k1 = open_kind k v.sort  in 
     let t1 = twithsort (Typ_app(typeOf, v.sort)) k1 in 
     let k2 = open_kind_with_exp k1 v in 
       twithsort (Typ_dep(t1, v)) k2 in 
   let eqtyp = 
     let k = Tcenv.lookup_typ_lid env Const.eqTyp_lid in 
     let eqtyp = twithsort (Typ_const(fvwithsort Const.eqTyp_lid k, None)) k in 
     let k1 = Kind_tcon(None, Kind_erasable, Kind_erasable) in 
     let t1 = twithsort (Typ_app(eqtyp, tof)) k1 in 
       twithsort (Typ_app(t1, t)) Kind_erasable in 
     eqtyp

 let mkPred t p = 
   let h = new_bvd None in 
   let hexp = bvd_to_exp h t in 
     mkLam h t p

 let forall_kind = AbsynUtils.forall_kind
 let mkForall x t p = 
   if isTrueTyp p then p
   else AbsynUtils.mkForall x t p

 let mkForall_l binders body : typ = 
   List.fold_right (fun (x,t) body -> mkForall x t body) binders body 

 let mkForallT_l binders body = 
   List.fold_right (fun (a,k) body -> twithsort (Typ_univ(a, k, [], body)) Kind_prop) binders body

 let mkEq (env:Tcenv.env) (t:typ) (e1:exp) (e2:exp) : prop =
   let eq_k = alpha_convert_kind (Tcenv.lookup_typ_lid env Const.eq_lid) in
   let eq_typ = twithsort (Typ_const((fvwithsort Const.eq_lid eq_k), None)) eq_k in
   let eq_app1_k = open_kind eq_k t in
   let eq_app1 = twithinfo (Typ_app(eq_typ, t)) eq_app1_k eq_typ.p in
   let eq_app2_k = open_kind_with_exp eq_app1.sort e1 in
   let eq_app2 = twithinfo (Typ_dep(eq_app1, e1)) eq_app2_k e1.p in
   let eq_app3_k = open_kind_with_exp eq_app2.sort e2 in
   let eq_app3 = twithinfo (Typ_dep(eq_app2, e2)) eq_app3_k e2.p in
     eq_app3

 (* ******************************************************************************** *)
 (* Operations on generic monad constructions *)
 (* ******************************************************************************** *)
 type monadsig = 
     {mtyp:typ;
      mrettx:typ;
      mcomposetx:typ;
      solver:option<Tcenv.solver>}

 let tx_kind msig t = 
   match msig.mtyp.sort(* .u *) with 
     | Kind_tcon(Some alpha, k, (Kind_tcon(_, txkind, Kind_star))) -> 
         substitute_kind_l txkind [(alpha, t)]
     | _ -> pr "Got kind %s\n" (Pretty.strKind msig.mtyp.sort); raise Impos

 let post_kind msig t = 
   match tx_kind msig t with 
     | Kind_tcon(_, post_kind, pre_kind) -> post_kind
     | _ -> raise Impos

 let pre_kind msig t = 
   match tx_kind msig t with 
     | Kind_tcon(_, post_kind, pre_kind) -> pre_kind
     | _ -> raise Impos

 let prop_at_kind t k = 
   let rec aux binders k = match k with 
     | Kind_prop 
     | Kind_erasable -> 
         List.fold_left (fun out b -> match b with 
                           | Inl (a, k) -> mkTyp_tlam a k out
                           | Inr (x, t) -> mkTlam (Some x) t out) t binders

     | Kind_tcon(a, k1, k2) -> 
         let b = new_bvd (match a with None -> None | Some a -> Some (range_of_bvd a)) in 
         let btyp = bvd_to_typ b k1 in 
           aux (Inl(b,k1)::binders) k2

     | Kind_dcon(x, t1, k2) -> 
         let y = new_bvd (match x with None -> None | Some x -> Some (range_of_bvd x)) in 
         let yval = bvd_to_exp y t1 in 
           aux (Inr(y, t1)::binders) k2
     | _ -> raise Impos in 
     aux [] k

 let prop_as_pre msig t = 
   match tx_kind msig t with 
     | Kind_tcon(_, post_kind, pre_kind) -> prop_at_kind t pre_kind
     | _ -> raise Impos

 let fresh_postcondition msig env p = 
   let u = TypeRelations.new_uvar env Kind_star p in 
   let pk = post_kind msig u in 
   let postvar = new_bvd (Some p) in 
     postvar, bvd_to_typ postvar pk

 let fresh_postcondition_at_type msig env u p = 
   let pk = post_kind msig u in 
   let postvar = new_bvd (Some p) in 
     postvar, bvd_to_typ postvar pk

 let rec fix_post_kind p env k1 k2 = 
   match TypeRelations.force_kind_convertible_ev env k1 k2 with 
     | None -> raise (Error(spr "Incompatible kinds when composing transformers: \nExpected kind %s\n Got kind %s\n" (Pretty.strKind k2) (Pretty.strKind k1), p))
     | Some _ -> ()

 let get_monadsig (env:Tcenv.env) (m:modul) = 
   match findOpt (function PRAGMA_MONADIC _ -> true | _ -> false) m.pragmas with 
     | Some (PRAGMA_MONADIC(t1,t2,t3)) -> 
         let t1, _ = Tc.kinding env t1 in 
         let t2, _ = Tc.kinding env t2 in
         let t3, _ = Tc.kinding env t3 in
         {mtyp=t1;
          mrettx=t2;
          mcomposetx=t3;
          solver=None}
     | _ -> failwith "Monadic mode requires a #monadic pragma"

 let mk_monad msig t tx = mkTapp (mkTapp msig.mtyp t) tx

 let destruct_monad env msig torig : option<typ * typ> = 
   let mlid = match msig.mtyp with 
     | {v=Typ_const(m, _)} -> m.v
     | _ -> raise Impos in 
     match Tcenv.expand_typ_until env torig mlid with 
       | None -> None
       | Some t ->    
           match AbsynUtils.flattenTypAppsAndDeps t with 
             | ({v=Typ_const(tc,_)}, [Inl res_t; Inl tx]) -> 
                 Some (res_t, tx)
             | _ -> None

 let mk_return_pre msig v post = 
   mkTapp (mkDep (mkTapp msig.mrettx v.sort) v) post 

 let compose_tx (msig:monadsig) env (x:bvvdef) (t1:typ) (tx1:typ) (t2:typ) (tx2:typ) (post:typ) = 
   match TypeRelations.force_kind_convertible_ev env tx1.sort (tx_kind msig t1) with 
     | None -> raise (Error(spr "Incompatible kinds when composing transformers: \nExpected kind %s\n Got kind %s\n" (Pretty.strKind (tx_kind  msig t1)) (Pretty.strKind tx1.sort),  t1.p))
     | _ ->  
         let k2 = Kind_dcon(Some x, t1, (tx_kind msig t2)) in 
           (match TypeRelations.force_kind_convertible_ev env tx2.sort k2 with 
              | None -> 
                  raise (Error(spr "Incompatible kinds when composing transformers: \nExpected kind %s\n Got kind %s\n" (Pretty.strKind k2) (Pretty.strKind tx2.sort),  t2.p))
              | _ -> List.fold_left mkTapp msig.mcomposetx [t1; t2; tx1; tx2; post])

 let adjust_preds_with_binders f preds : typ = 
   let p, k = match preds with 
     | [] -> raise Impos 
     | hd::tl -> hd.p, hd.sort in 
   let rec aux binders preds k = match k(* .u *) with 
     | Kind_prop
     | Kind_erasable -> 
         let pred = f (List.rev binders) preds in 
           List.fold_left (fun out b -> match b with 
                             | Inl (a, k) -> mkTyp_tlam a k out
                             | Inr (x, t) -> mkTlam (Some x) t out) pred binders

     | Kind_tcon(a, k1, k2) -> 
         let b = new_bvd (match a with None -> None | Some a -> Some (range_of_bvd a)) in 
         let btyp = bvd_to_typ b k1 in 
         let preds = preds |> List.map (fun t -> mkTapp t btyp) in 
           aux (Inl(b,k1)::binders) preds k2

     | Kind_dcon(x, t1, k2) -> 
         let y = new_bvd (match x with None -> None | Some x -> Some (range_of_bvd x)) in 
         let yval = bvd_to_exp y t1 in 
         let preds = preds |> List.map (fun t -> mkDep t yval) in 
           aux (Inr(y, t1)::binders) preds k2

     | _ -> raise (Error(spr "Internal error: Unexpected kind %s\n" (Pretty.strKind k), p)) in 

     aux [] preds k

 let adjust_preds f preds = adjust_preds_with_binders (fun _ x -> f x) preds

 let close_precondition msig env pre xts : typ = 
   adjust_preds (fun [t] -> mkForall_l xts t) [pre]

 let close_precondition_with_types msig env pre vars : typ = 
   adjust_preds (fun [t] -> 
                   List.fold_right (fun v body -> match v with
                                      | Inl(a,k) -> twithsort (Typ_univ(a,k,[],body)) body.sort
                                      | Inr(x,t) -> mkForall x t body)
                     vars t)
     [pre]

 let guard_precondition' double msig env pre guard = 
   if isTrueTyp guard then pre
   else
     match guard.sort(* .u *) with 
       | Kind_erasable
       | Kind_prop ->
           if double
           then adjust_preds (fun [t] -> mkImplies (mkTapp Const.doublesided_typ guard) t) [pre]
           else adjust_preds (fun [t] -> mkImplies guard t) [pre]
       | _ ->   
           (pr "Guarding pre-condition with %s :: %s\n" (Pretty.strTyp guard) (Pretty.strKind guard.sort);
            raise Impos)

 let guard_precondition msig env pre guard = 
   guard_precondition' (!Options.relational) msig env pre guard

 let guard_singlesided_precondition msig env pre guard = 
   guard_precondition' false msig env pre guard

 let strengthen_precondition pre preds = 
   let preds = mkAnd_l preds in 
   if isTrueTyp preds 
   then pre
   else adjust_preds (fun [t] -> mkAnd t preds) [pre]
     
 let augment_postcondition msig env post obligation = 
   adjust_preds (fun [t] -> mkAnd obligation t) [post]

 let mk_cases msig env pres = 
   adjust_preds (fun pres -> twithsort (Typ_meta (Meta_cases pres)) Kind_erasable) pres

 let trivial_pre msig t = 
   let k = pre_kind msig t in 
   let dummy = twithsort Typ_unknown k in 
     adjust_preds (fun _ -> Const.true_typ) [dummy]

 (*****************************************************************************)
 (*         Predicates on types and type normalization                        *)
 (*****************************************************************************)
 let rec small_type env t = 
   let t' = compress t in
     match t'.sort(* .u *) with 
       | Kind_star -> 
           (match (unascribe_typ t').v with 
              | Typ_uvar _
              | Typ_btvar _
              | Typ_const _ -> true
              | Typ_record(fn_t_l, _) -> 
                  fn_t_l |> List.forall (fun (_,t) -> small_type env t)
              | Typ_dtuple(xtl) -> 
                  xtl |> List.forall (fun (_,t) -> small_type env t)
              | Typ_refine(_, t, _, _) -> 
                  small_type env t
              | Typ_app _ 
              | Typ_dep _ -> true
              | Typ_ascribed _
              | Typ_unknown -> raise Impos
              | Typ_affine _ 
              | Typ_lam _
              | Typ_tlam _ 
              | Typ_fun _ 
              | Typ_univ _ -> false
              | Typ_meta _ -> failwith "Meta escaped!")
       | _ -> false


 let canonicalizePST msig env t = 
   let rec aux binders t = 
     if small_type env t then t
     else match t.v with 
       | Typ_univ(a, k, fl, t) -> {t with v=Typ_univ(a, k, fl, aux binders t)}
       | Typ_fun(Some x, t1, t2) when small_type env t1 -> 
           let binders = (x,t1)::binders in 
             begin match destruct_monad env msig t2 with 
               | None -> {t with v=Typ_fun(Some x, t1, aux binders t2)}

               | Some (tret, tx) -> 
                   let trans = whnf tx in 
                   let trans = (List.fold_right (fun (y, ty) trans -> mkLam y ty trans)
                                  binders trans) in 
                   let trans = (List.fold_left (fun trans (y, t) -> mkDep trans (bvd_to_exp y t))
                                  trans binders) in 
                     {t with v=(Typ_fun(Some x, t1, mk_monad msig tret trans))}
             end
       | _ -> t in
   let t = aux [] t in 
     (* check_bvar_identity "canonicalize" t; *)
     t

 let close_typ msig env t xts : typ = 
   if small_type env t 
   then t
   else failwith "NYI: Closing non-small types not yet implemented"

 let try_unify_kinds (env:Tcenv.env) (k1:kind) (k2:kind) : bool = 
   match TypeRelations.force_kind_convertible_ev env k1 k2  with
     | None -> false
     | _ -> true

 let unify_kinds (env:Tcenv.env) (k1:kind) (k2:kind) p msg : unit = 
   if try_unify_kinds env k1 k2 
   then ()
   else raise (Err(spr "(%s) Expected kind %s\n Got kind %s\n" msg (Pretty.strKind k2) (Pretty.strKind k1)))

 type mfun = {formals:list<bvvdef*typ>;
              typ:typ;
              transformer:formula}

 type purefun = {formals:list<bvvdef*typ>;
                 refname:bvvdef;
                 typ:typ;
                 refinement:formula;
                 preconditions:list<formula>;}

 let mkPureFun pf = 
   let res = twithsort (Typ_refine(pf.refname, pf.typ, pf.refinement, true)) Kind_star in 
     List.fold_right (fun (x,t) out -> twithsort (Typ_fun(Some x, t, out)) Kind_star) pf.formals res

 let mkMFun msig (mfun:mfun) = 
   let res = mk_monad msig mfun.typ mfun.transformer in 
     List.fold_right (fun (x,t) out -> twithsort (Typ_fun(Some x, t, out)) Kind_star) mfun.formals res

 let unFunType env msig (t:typ) : Disj<mfun, purefun> = 
   let rec aux binders_rev t = 
     let t = compress t in
       match (unascribe_typ t).v with 
         | Typ_fun(xopt, t1, t2) -> 
             let x = match xopt with 
               | None -> new_bvd (Some t.p)
               | Some x -> x in 
               aux ((x, t1)::binders_rev) t2 
         | _ -> 
             match destruct_monad env msig t with 
               | None -> 
                   let binders = (List.rev binders_rev) in
                   let binders, preconditions = List.unzip <| List.map 
                       (fun (x,t) -> match AbsynUtils.normalizeRefinement (Tcutil.reduce_typ_delta_beta env t) with
                          | {v=Typ_refine(y, t, phi, _)} -> 
                              let phi = substitute_exp_l phi [y, bvd_to_exp x t] in 
                                (x,t), [phi]
                          | t -> (x,t), []) 
                       binders in 
                     (match (normalizeRefinement t).v with 
                        | Typ_refine(x, t, phi, b) -> 
                            Inr {formals=binders;
                                 refname=x;
                                 typ=t;
                                 refinement=phi;
                                 preconditions=List.flatten preconditions}
                        | _ -> 
                            let x = new_bvd (Some t.p) in
                              Inr {formals=binders;
                                   refname=x;
                                   typ=t;
                                   refinement=Const.true_typ;
                                   preconditions=List.flatten preconditions})
               | Some (t', tx) -> 
                   let binders = List.rev binders_rev in
                     Inl {formals=binders;
                          typ=t';
                          transformer=tx} in
     aux [] (Tcenv.expand_typ env t)


 let guard_mfun msig env p (mfun:mfun) (fl:list<formula>) =
   let post_var, post = fresh_postcondition_at_type msig env mfun.typ p in 
   let pre = mkTapp mfun.transformer post in 
   let pre = guard_precondition msig env pre (mkAnd_l fl) in 
   let tx = mkTyp_tlam post_var post.sort pre in 
     {mfun with transformer=tx}

 let guard_purefun purefun (fl:list<formula>) =
   {purefun with refinement=(mkAnd_l (purefun.refinement::fl))}


 let rec unify (env:Tcenv.env) msig (t1:typ) (t2:typ) =
   let just_do_it () = match TypeRelations.convertible_ev env t1 t2 with
      | Some (subst, _) -> 
          let _ = Tcutil.unify_subst_vars subst in  (* this has a side effect; changes uvar pointers in Unionfind *) 
            true
      | _ -> false in 
    if not !Options.delay_monadic_unification
    then just_do_it ()
    else
      if small_type env t2 
      then just_do_it ()
      else 
        match unFunType env msig t1, unFunType env msig t2 with
          | Inl mfun1, Inl mfun2 when List.length mfun1.formals = List.length mfun2.formals ->
              if ((List.forall2 (fun (x,t) (y,s) -> unify env msig t s) mfun1.formals mfun2.formals)
                  && unify env msig mfun1.typ mfun2.typ)
              then 
                let tx1, _ = AbsynUtils.flattenTypAppsAndDeps mfun1.transformer in
                let tx2, _ = AbsynUtils.flattenTypAppsAndDeps mfun2.transformer in
                  (match (unname_typ (compress tx2)).v with
                     | Typ_uvar(uv,k) when try_unify_kinds env tx1.sort tx2.sort ->  
                         Unionfind.change uv (Delayed tx1); true
                           (* true *)
                           (* (match Tcutil.check_unify (uv,k) tx1 with None -> true | Some msg -> print_string msg; false) *)
                     | _ -> just_do_it ())
              else false
          | _ -> just_do_it ()


 let join_types msig env tl p : typ = 
   if List.for_all (small_type env) tl 
   then 
     match tl with 
       | [] -> raise Impos
       | t::rest -> 
           if List.for_all (unify env msig t) rest
           then t 
           else raise (Error(spr "Incompatible branch types {%s}\n" (String.concat ", " (List.map Pretty.strTyp tl)), t.p))
   else failwith "NYI: Joining non-small types not yet implemented"

 (**********************************************************************************)
 (* Normalizing refinement types *)
 (**********************************************************************************)
 let isRefinedType (t:typ) : bool =
   match t.v with
     | Typ_refine _ -> true
     | _ -> false

 let normalize_refinements lid msig (env:Tcenv.env) (t:typ) : typ =
   let rec aux t refs : typ =
     match (Tcenv.expand_typ env t).v with
       | Typ_ascribed (t, k) -> aux t refs
       | Typ_lam (x, t1, t2) ->
           let t1 = Tcenv.expand_typ env t1 in
             if isRefinedType t1 then 
               raise (Error(spr "Monadic mode: Type-level functions cannot have refined domains (%s)" (Sugar.text_of_lid lid), t.p))
             else
               let t1 = aux t1 [] in
               let t2' = aux t2 refs in
                 twithinfo (Typ_lam(x, t1, t2')) t.sort t.p
       | Typ_tlam (x, k, t2) ->
           let t2' = aux t2 refs in
             if kind_contains_refinement env k 
             then raise (Error(spr "Monadic mode: Type-level functions cannot have refined domains (%s)" (Sugar.text_of_lid lid), t.p))
             else twithinfo (Typ_tlam(x, k, t2')) t.sort t.p
       | Typ_univ (x, k, [], t2) ->
           let t2' = aux t2 refs in
             if kind_contains_refinement env k 
             then raise (Error(spr "Monadic mode: Type-level functions cannot have refined domains (%s)" (Sugar.text_of_lid lid), t.p))
             else twithinfo (Typ_univ(x, k, [], t2')) t.sort t.p
       | Typ_fun(xopt, t1, t2) ->
           let t1 = Tcenv.expand_typ env t1 in
           let xopt, t1', t2' = match (AbsynUtils.normalizeRefinement t1).v with
             | Typ_refine (x, t1', re, _) -> 
                 (* Make sure x is the same x as in xopt.  It must be in scope
                  * in the return type. *)
                 let xopt, re = match xopt with
                   | Some x' -> 
                       if bvd_eq x x' 
                       then Some x', re 
                       else
                         let re' = substitute_exp re x (bvd_to_exp x' t1') in
                           Some x', re'
                   | None -> Some x, re in
                 let t2' = aux t2 (re::refs) in
                   xopt, t1', t2'
             | _ -> xopt, t1, (aux t2 refs) in
           let t1' = if small_type env t1' then t1' else aux t1' [] in
             twithinfo (Typ_fun(xopt, t1', t2')) t.sort t.p
       | _ ->
           let t, tx = match destruct_monad env msig t with 
             | Some (t, tx) -> (Tcenv.expand_typ env t), tx 
             | _ -> 
                 (* TODO: can we allow pure signatures and automatically lift them? *)
                 raise (Error(spr "Monadic mode: User-defined functions must have a monadic result type; (%s) \nexpected %s\n got %s" 
                                       (Sugar.text_of_lid lid) (Pretty.strTyp msig.mtyp) (Pretty.strTyp t), t.p))  in
             if typ_contains_refinement env tx
             then raise (Error(spr "Monadic mode: Predicate transformers cannot use refined types (%s)" (Sugar.text_of_lid lid), tx.p))
             else
               let post_var, post = fresh_postcondition msig env t.p in 

               let post = match (AbsynUtils.normalizeRefinement t).v with
                 | Typ_refine (x, t, re, _) ->
                     let ob = twithinfo (Typ_lam(x,t,re)) (Kind_dcon(Some x, t, re.sort)) t.p in 
                       augment_postcondition msig env post ob

                 | _ -> post in

               let pre = mkTapp tx post  in 
               let pre = match refs with 
                 | [] -> pre
                 | _ -> guard_precondition msig env pre (mkAnd_l refs) in 

               let tx = mkTyp_tlam post_var post.sort pre in 
                 mk_monad msig t tx in 
     aux t []

 let mkproj env lid e =
   let proj_t = Tcenv.lookup_lid env lid in
   ewithsort (Exp_constr_app(ewithsort lid proj_t, [e.sort], [], [e])) e.sort 
 let mk_lproj env e = mkproj env Const.lproj_lid e
 let mk_rproj env e = mkproj env Const.rproj_lid e

 let patternBindings p env pat : (exp * list<Disj<(btvdef*kind), (bvvdef*typ)>> * Tcenv.env) = 
   match pat with 
     | Pat_variant(cname, tvs, [], xs, false) ->
       let tc = alpha_fresh_labels p (Tcenv.lookup_lid env cname) in 
       let vars = (List.map Inl tvs) @ (List.map Inr xs) in 
       let rec mk_bindings (tvs, ts, bindings) vars t = match vars, t.v with 
         | (Inl ({v=(Typ_btvar btv)} as tv))::rest, Typ_univ(a, k, _, t') -> 
           let tvar = bvd_to_typ btv.v k in 
           let t' = substitute_l t' [a, tvar] in
           let b = Tcenv.Binding_typ(btv.v.realname,k) in
           mk_bindings (tv::tvs, Inl(btv.v, k)::ts, b::bindings) rest t'

         | (Inl ({v=Typ_unknown}))::rest, Typ_univ(a, k, _, t') -> 
           let tuv = TypeRelations.new_uvar env k (range_of_bvd a) in
           let t' = substitute_l t' [a, tuv] in
           mk_bindings (tuv::tvs, ts, bindings) rest t'

         | ((Inr _)::_, Typ_univ(a, k, _, t')) -> 
           let tuv = TypeRelations.new_uvar env k (range_of_bvd a) in
           let t' = substitute_l t' [a, tuv] in
           mk_bindings (tuv::tvs, ts, bindings) vars t'

         | (Inr xv)::rest, Typ_fun(Some x, tx, t2) -> 
           let t2 = substitute_exp_l t2 [x, bvd_to_exp xv.v tx] in 
           let b = Tcenv.Binding_var(bvar_real_name xv, tx) in
           mk_bindings (tvs, Inr(xv.v, tx)::ts, b::bindings) rest t2

         | (Inr xv)::rest, Typ_fun(None, tx, t2) -> 
           let b = Tcenv.Binding_var(bvar_real_name xv, tx) in
           mk_bindings (tvs, Inr(xv.v, tx)::ts, b::bindings) rest t2

         | [], _ -> 
           let env = List.fold_left Tcenv.push_local_binding_fast env (List.rev bindings) in
           List.rev tvs, List.rev ts, env

         | Inl t::_, _ -> raise (Error(spr "Unexpected pattern type-variable: %s\n" (Pretty.strTyp t), t.p))
         | Inr x::_, _ -> raise (Error(spr "Unexpected pattern variable: %s\n" (Pretty.strBvar x), x.p)) in
       let tvs, binders, env = mk_bindings ([],[],[]) vars tc  in 
       let vpat = ewithpos (Exp_constr_app(fvwithpos cname p, tvs, [], List.map AbsynUtils.bvar_to_exp xs)) p in
       vpat, binders, env

     | _ -> raise Impos


 let composeClassic env t wp0 wp1 = 
   let k = Tcenv.lookup_typ_lid env Const.composeClassic_lid in 
   let cc = twithsort (Typ_const(fvwithsort Const.composeClassic_lid k, None)) k in 
     mkTapp (mkTapp (mkTapp cc t) wp0) wp1

 let enableSolver msig env = match msig.solver with
   | None -> env
   | Some s -> Tcenv.set_solver env s 

 (********************************************************************************)
 let close preds1 binders preds2 = Some (preds1 @ preds2 |> List.map (mkForall_l binders)) 
 let close_t preds1 binders preds2 = Some (preds1 @ preds2 |> List.map (mkForallT_l binders)) 
 let rec convertible msig env t1 t2 : option<preds> =
   (* d_convertible is covariant on both; callers re-order args as appropriate *)
   let d_convertible msig env (x1Opt, t1_1, t1_2) (x2Opt, t2_1, t2_2) =
     let env = Tcenv.clear_current_value env in 
     bind_opt (convertible msig env t1_1 t2_1) (fun preds1 ->
       match x1Opt, x2Opt with
         | None, None -> 
           bind_opt (convertible msig env t1_2 t2_2) (fun preds2 -> Some (preds1@preds2))
             
         | Some x1, Some x2 ->
           let t2_2 = substitute_exp t2_2 x2 (bvd_to_exp x1 t1_1) in
           bind_opt (convertible msig env t1_2 t2_2) (close preds1 [(x1,t1_1)])
             
         | Some x1, None ->
           bind_opt (convertible msig env t1_2 t2_2) (close preds1 [(x1,t1_1)])
             
         | None, Some x2 ->
           bind_opt (convertible msig env t1_2 t2_2) (close preds1 [(x2,t1_1)])) in
   
   let refinement_subtyping env t1 t2 : option<preds> =
     let t1 = unascribe_typ (unname_typ t1) in
     let t2 = unascribe_typ (unname_typ t2) in
     match t1.v, t2.v with
       | Typ_refine(bvd1, t1, phi1, _), Typ_refine(bvd2, t2, phi2, _) ->
         bind_opt (convertible msig env t1 t2)
           (fun preds ->
             match Tcenv.current_value env with
               | None ->
                 let phi2 = substitute_exp phi2 bvd1 (bvd_to_exp bvd1 t2) in
                 Some (mkForall bvd1 t2 (mkImplies phi1 phi2)::preds)
                   
               | Some v ->
                 let phi1 = substitute_exp phi1 bvd1 v in 
                 let phi2 = substitute_exp phi2 bvd2 v in 
                 Some (mkImplies phi1 phi2::preds))
           
       | Typ_refine(_, t1, _, _), _  -> convertible msig env t1 t2
         
       | _, Typ_refine _ ->
         let t1 = twithsort (Typ_refine(new_bvd None, t1, Const.true_typ, true)) t1.sort in
         convertible msig env t1 t2

       | Typ_fun(x1Opt, t1_1, t1_2), Typ_fun(x2Opt, t2_1, t2_2) ->
         d_convertible msig env (x1Opt, t2_1, t1_2) (x2Opt, t1_1, t2_2) (* note contravariance in arg *)
           
       | Typ_dtuple([(x1Opt, t1_1); (_, t1_2)]), Typ_dtuple([(x2Opt, t2_1); (_, t2_2)]) ->
         d_convertible msig env (x1Opt, t1_1, t1_2) (x2Opt, t2_1, t2_2) (* note covariance in both *)

       | Typ_lam(x1, t1_1, t1_2), Typ_lam(x2, t2_1, t2_2) ->
         d_convertible msig env (Some x1, t2_1, t1_2) (Some x2, t1_1, t2_2) (* note contravariance in arg *)
           
       | Typ_univ(a1, k1, [], t1), Typ_univ(a2, k2, [], t2) 
       | Typ_tlam(a1, k1, t1), Typ_tlam(a2, k2, t2) ->
         let env = Tcenv.clear_current_value env in 
         bind_opt (kind_convertible msig env k2 k1) (fun preds1 ->
           let t2 = substitute t2 a2 (bvd_to_typ a1 k2) in
           bind_opt (convertible msig env t1 t2) (close_t preds1 [(a1,k2)]))
             
       | Typ_affine t1, Typ_affine t2 ->
         convertible msig env t1 t2
           
       | _ -> None in
   
   match TypeRelations.equiv env t1 t2 with
     | Some subst -> Tcutil.unify_subst_vars subst; Some []
     | _ -> refinement_subtyping env t1 t2
                 
 and kind_convertible msig env k1 k2 : option<preds> =
   let aux env k1 k2 = match k1, k2 with
     | Kind_affine, Kind_erasable
     | Kind_star, Kind_erasable
     | Kind_prop, Kind_erasable -> Some []
     | Kind_dcon(xopt, t1, k1), Kind_dcon(yopt, t2, k2) ->
       bind_opt (convertible msig env t2 t1) (fun preds1 ->
         match xopt, yopt with
           | None, None -> 
             bind_opt (kind_convertible msig env k1 k2) (fun preds2 -> Some (preds1@preds2))
           | Some x, Some y ->
             let k2 = substitute_kind_exp k2 y (bvd_to_exp x t2) in
             bind_opt (kind_convertible msig env k1 k2) (close preds1 [(x,t2)])
           | Some x, None ->
             bind_opt (kind_convertible msig env k1 k2) (close preds1 [(x,t2)])
           | None, Some y ->
             bind_opt (kind_convertible msig env k1 k2) (close preds1 [(y,t2)]))
         
     | Kind_tcon(aopt, k1, k2), Kind_tcon(bopt, k1', k2') ->
       bind_opt (kind_convertible msig env k1' k1) (fun preds1 ->
         match aopt, bopt with
           | None, None -> bind_opt (kind_convertible msig env k2 k2') (fun preds2 -> Some (preds1@preds2))
           | Some a, Some b ->
             let ta = bvd_to_typ a k1' in 
             let k2' = substitute_kind k2' b ta in
             bind_opt (kind_convertible msig env k2 k2') (close_t preds1 [(a,k1')])
           | Some a, None ->
             bind_opt (kind_convertible msig env k2 k2') (close_t preds1 [(a,k1')])
           | None, Some b ->
             bind_opt (kind_convertible msig env k2 k2') (close_t preds1 [(b,k1')]))
     | _ -> None in
   if k1 === k2 then Some []
   else aux env k1 k2

 type result = 
   | NonMonadic
   | Failure
   | Success

 let rec monadic_conv msig env subst t s = 
   match t.v, s.v with 
     | Typ_fun(Some x, t1, t2), Typ_fun(Some y, s1, s2) -> 
         (match TypeRelations.equiv env (substitute_l_typ_or_exp t1 subst) (substitute_l_typ_or_exp s1 subst) with 
            | Some [] -> 
                let env = Tcenv.push_local_binding env (Tcenv.Binding_var(x.realname, t1)) in 
                let subst = Inr(y, bvd_to_exp x s1)::subst in 
                  monadic_conv msig env subst t2 s2
            | _ -> NonMonadic)
           

     | Typ_univ(a, Kind_star, _, t), Typ_univ(b, Kind_star, _, s) -> 
         let env = Tcenv.push_local_binding env (Tcenv.Binding_typ(a.realname, Kind_star)) in 
         let subst = Inl(b, bvd_to_typ a Kind_star)::subst in 
           monadic_conv msig env subst t s

     | Typ_fun _,  _ ->
         (match Tcenv.expand_typ_until_pred env s (function {v=Typ_fun _} -> true | _ -> false) with
            | Some s ->  monadic_conv msig env subst t s
            | _ -> NonMonadic)

     | Typ_univ _, _ ->
         (match Tcenv.expand_typ_until_pred env s (function {v=Typ_univ _} -> true | _ -> false) with
            | Some s ->  monadic_conv msig env subst t s
            | _ -> NonMonadic)

     | _, Typ_fun _ ->
         (match Tcenv.expand_typ_until_pred env t (function {v=Typ_fun _} -> true | _ -> false) with
            | Some t ->  monadic_conv msig env subst t s
            | _ -> NonMonadic)

     | _, Typ_univ _ ->
         (match Tcenv.expand_typ_until_pred env t (function {v=Typ_univ _} -> true | _ -> false) with
            | Some t ->  monadic_conv msig env subst t s
            | _ -> NonMonadic)

     | _, _ -> 
         match destruct_monad env msig t, destruct_monad env msig s with
           | None, _ 
           | _, None -> NonMonadic
           | Some(res_t1,tx1), Some(res_t2,tx2) -> 
               let res_t1 = substitute_l_typ_or_exp res_t1 subst in
               let res_t2 = substitute_l_typ_or_exp res_t2 subst in
               let tx1 = substitute_l_typ_or_exp tx1 subst in
               let tx2 = substitute_l_typ_or_exp tx2 subst in
               match TypeRelations.equiv env res_t1 res_t2 with 
                 | Some [] -> 
                     let postvar, post = fresh_postcondition msig env tx1.p in 
                     let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_typ(postvar.realname, post.sort)) in 
                     let pre1 = mkTapp tx1 post in 
                     let pre2 = mkTapp tx2 post in 
                     let pre_k = pre_kind msig res_t2 in 
                     let rec check env k pre1 pre2 = match k with 
                       | Kind_dcon(x, t1, k2) -> 
                           let y = new_bvd (match x with None -> None | Some x -> Some (range_of_bvd x)) in 
                           let yval = bvd_to_exp y t1 in 
                           let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_var(y.realname, t1)) in 
                             check env k2 (mkDep pre1 yval) (mkDep pre2 yval)
                       | Kind_tcon(a, k1, k2) -> 
                           let b = new_bvd (match a with None -> None | Some a -> Some (range_of_bvd a)) in 
                           let btyp = bvd_to_typ b k1 in 
                           let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_typ(b.realname, k1)) in 
                             check env k2 (mkTapp pre1 btyp) (mkTapp pre2 btyp)
                       | _ -> 
                           (* Note, contravariance *)
                           let t,x = AbsynUtils.mkRefinedUnit pre2 in 
                           let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_var(x, t)) in 
                           let pre1 = Krivine.strong_normalize env pre1 in
                           (* let _ = pr "Annotated pre is %s\n" (Pretty.strTyp pre2) in *)
                           (* let _ = pr "Inferred pre is %s\n" (pre1.ToString()) in *)
                             match msig.solver with 
                               | None -> raise Impos
                               | Some s -> 
                                   let env = Tcenv.set_solver env s in 
                                     Z3Enc.query env pre1 in 
                       if check env pre_k pre1 pre2 then Success else Failure
                 | _ -> NonMonadic
   

 let is_convertible msig err_e p env t1 t2 : pred =
   let fail () = 
     raise (Error(spr "\nInferred type for %s : %s not compatible with annotated type %s\n"
                    (Pretty.strExp err_e) 
                    (Pretty.strTyp t1) 
                    (Pretty.strTyp t2),
                  p)) in 
     match TypeRelations.equiv env t1 t2 with 
       | Some subst -> Tcutil.unify_subst_vars subst; Const.true_typ
       | _ -> 
           match monadic_conv msig env [] t1 t2 with 
             | Success -> Const.true_typ
             | Failure -> fail ()
             | _ -> match convertible msig env (Krivine.strong_normalize env t1) (Krivine.strong_normalize env t2) with
                 | None -> fail ()
                 | Some preds -> mkAnd_l preds
                     
     
