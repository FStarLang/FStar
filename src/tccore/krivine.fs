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
module Microsoft.FStar.Krivine
open Util
open Absyn 
open Profiling 

(* Reduction of types via the Krivine Abstract Machine (KN), with lazy
   reduction and strong reduction (under binders), as described in:

   Strongly reducing variants of the Krivine abstract machine
   Pierre Crégut
   Higher-Order Symb Comput (2007) 20: 209–230
*)
exception Impos1
exception Impos2
exception Impos3
type config<'a> = {code:'a;
                   environment:environment;
                   stack:stack}
and environment = list<env_entry>    
and stack = list<stack_entry>
and env_entry = 
  | T of (btvdef * tclos * memo<typ>)
  | V of (bvvdef * vclos * memo<exp>)
  | TDummy of btvdef
  | VDummy of bvvdef
and stack_entry = 
  | TT of tclos * kind * Range.range
  | VV of vclos * kind * Range.range
and tclos = (typ * environment)
and vclos = (exp * environment)
and memo<'a> = ref<option<'a>>

type stats = {maxstack:int ref;
              nlazy:int ref;
              beta:int ref;
              delta:int ref;
              alpha:int ref}
let stats = {maxstack = ref 0;
             nlazy = ref 0;
             beta = ref 0;
             delta = ref 0;
             alpha = ref 0}
let reset_stats () = 
  stats.maxstack := 0;
  stats.nlazy := 0;
  stats.beta := 0;
  stats.delta := 0;
  stats.alpha := 0

let print_stats () =
  pr "KN Stats: maxstack = %d, nlazy=%d, betas=%d, deltas=%d, alphas=%d\n" 
    (!stats.maxstack)
    (!stats.nlazy)
    (!stats.beta)
    (!stats.delta)
    (!stats.alpha)
let npush = ref 0
let push se config = {config with stack=se::config.stack}
  (* npush := !npush + 1; *)
  (* (\* if !npush mod 1000 = 0 then print_stats(); *\) *)
  (* let sz = config.stacksz+1 in *)
  (*   if sz > !stats.maxstack then stats.maxstack := sz; *)
  (*   {config with stack=se::config.stack; stacksz=sz} *)
let pop config = match config.stack with 
  | [] -> None, config
  | hd::tl -> Some hd, {config with stack=tl}
let beta () = stats.beta := !stats.beta + 1    
let delta () = stats.delta := !stats.delta + 1    
let alpha () = stats.alpha := !stats.alpha + 1
let nlazy () = stats.nlazy := !stats.nlazy + 1    
let check_stack_empty c = ()
(* let check_stack_empty c = match c.stack with  *)
(*   | [] -> () *)
(*   | _ -> pr "Unexpected arguments on the stack!\n"; raise Impos *)
let lookup_typ_abbrev = 
  (* let cache = new System.Collections.Generic.Dictionary<string, option<typ>> () in (\* Hashtbl.create 1000 in *\) *)
    fun env (ftv:var<kind>) ->
  (*     let key = ftv.v.str in *)
  (*     let (hit, res) = cache.TryGetValue(key) in  *)
  (*       if hit then res *)
  (*       else  *)
          let res = Tcenv.lookup_typ_abbrev env ftv in 
            (* cache.Add(key,res); *)
            res

(* let rec sn tcenv (config:config<typ>) (cont:config<typ> -> 'a) : 'a =  *)
(*   let W t = (twithinfo t config.code.sort config.code.p) in *)
    
(*   (\* let W t (cont:typ -> 'a) : 'a = *\) *)
(*   (\*   cont (twithinfo t config.code.sort config.code.p) in *\) *)
    
(*   (\* let W t (cont:typ -> 'a) : 'a = *\) *)
(*   (\*   snk tcenv {code=config.code.sort; *\) *)
(*   (\*              environment=config.environment; *\) *)
(*   (\*              stack=[]; *\) *)
(*   (\*              stacksz=0} *\) *)
(*   (\*     (fun ck -> cont (twithinfo t ck.code config.code.p)) in *\) *)
(*   let rebuild config cont =  *)
(*     let rec aux stack (kk: list<Disj<typ,exp> * kind * Range.range> -> 'a) : 'a = match stack with *)
(*       | [] -> kk [] *)
(*       | TT((t,e),s,p)::rest ->  *)
(*           sn tcenv {code=t; environment=e; stack=[]} *)
(*             (fun c -> aux rest (fun l -> kk ((Inl c.code,s,p)::l))) *)
(*       | VV((v,e),s,p)::rest ->  *)
(*           wne tcenv {code=v; environment=e; stack=[]} *)
(*             (fun c -> aux rest (fun l -> kk ((Inr c.code,s,p)::l))) in *)
(*       aux config.stack  *)
(*         (fun tvl ->  *)
(*            let t = List.fold_left  *)
(*              (fun out (tv,s,p) -> match tv with  *)
(*                 | Inl t -> twithinfo (Typ_app(out, t)) s p *)
(*                 | Inr v -> twithinfo (Typ_dep(out, v)) s p) *)
(*              config.code *)
(*              tvl in  *)
(*              cont {config with code=t; stack=[]}) in *)
    
(*   let sn_prod xopt t1 t2 mk cont =  *)
(*     sn tcenv  *)
(*       {config with code=t1; stack=[]} *)
(*       (fun c1 ->  *)
(*          let c2 = match xopt with  *)
(*            | None -> {config with code=t2; stack=[]} *)
(*            | Some x -> {config with code=t2; environment=VDummy x::config.environment; stack=[]} in *)
(*            sn tcenv c2 (fun c2 -> cont {config with code=W (mk c1.code c2.code)})) in *)
    
(*     match config.code.v with  *)
(*       | Typ_const(fv, eref) ->   *)
(*            (match lookup_typ_abbrev tcenv fv with *)
(*               | None -> rebuild config cont *)
(*               | Some t -> (\* delta(); alpha ();  *\)sn tcenv {config with code=alpha_convert t} cont) *)

(*       | Typ_btvar(btv) ->  *)
(*           (match config.environment |> Util.findOpt (function TDummy x | T (x, _, _) -> bvd_eq btv.v x | _ -> false) with  *)
(*              | None -> rebuild config cont (\* possible for an open term *\) *)
(*              | Some (TDummy x) -> rebuild config cont  *)
(*              | Some (T(x, (t,e), m)) ->  *)
(*                  (match !m with  *)
(*                     | Some t ->  *)
(*                         (\* nlazy();  *\) *)
(*                         sn tcenv {config with code=t; environment=e}  *)
(*                           cont *)
(*                     | None ->  *)
(*                         let config' = {code=t; environment=e; stack=[]} in *)
(*                           (\* let config = push (MemoT (fun t -> m:=Some t)) config in  *\) *)
(*                           sn tcenv config' (fun c ->  *)
(*                                               m:=Some c.code; *)
(*                                               sn tcenv {c with stack=config.stack} cont)) *)
(*              | _ -> raise Impos) *)

(*       | Typ_app(t1, t2) ->  *)
(*           let se = TT((t2, config.environment), config.code.sort, config.code.p) in  *)
(*           let config = push se {config with code=t1} in  *)
(*             sn tcenv config cont *)
              
(*       | Typ_dep(t, v) ->  *)
(*           let se = VV((v, config.environment),config.code.sort,config.code.p) in  *)
(*           let config = push se {config with code=t} in  *)
(*             sn tcenv config cont *)

(*       | Typ_lam(x, t1, t2) ->  *)
(*           sn tcenv {config with code=t1; stack=[]} *)
(*             (fun c1 -> match pop config with  *)
(*                | None, config ->  *)
(*                    sn tcenv {config with  *)
(*                                code=t2; *)
(*                                environment=VDummy x::config.environment} *)
(*                      (fun c2 ->  *)
(*                         cont {config with code=W (Typ_lam(x, c1.code, c2.code))}) (\* stack is empty *\) *)
                     
(*                | Some (VV(vclos, _, _)), config ->  *)
(*                    (\* beta(); *\) *)
(*                    sn tcenv {config with  *)
(*                                code=t2; *)
(*                                environment=V(x,vclos,ref None)::config.environment} *)
(*                      cont *)
                     
(*                | _ -> raise Impos) *)
               
          
(*       | Typ_tlam(a, k, t) ->  *)
(*           snk tcenv {code=k; environment=config.environment; stack=[]} *)
(*             (fun ck -> match pop config with  *)
(*                | None, config  ->  *)
(*                    sn tcenv {config with  *)
(*                                code=t; *)
(*                                environment=TDummy a::config.environment} *)
(*                      (fun c ->  *)
(*                         cont {config with code=W (Typ_tlam(a, ck.code, c.code))}) *)
(*                      (\* stack is empty *\) *)
                     
(*                | Some (TT(tclos, _, _)), config ->  *)
(*                    (\* beta(); *\) *)
(*                    sn tcenv {config with  *)
(*                                code=t; *)
(*                                environment=T(a,tclos,ref None)::config.environment} *)
(*                      cont *)
                     
(*                | Some(VV _), config ->  *)
(*                    let _ = pr "Unexpected value argument on the stack\nExpected a type (or nothing)\n" in *)
(*                      raise Impos) *)

(*       | Typ_fun(xopt, t1, t2) ->  *)
(*           sn_prod xopt t1 t2 (fun t1 t2 -> Typ_fun(xopt, t1, t2)) cont *)

(*       | Typ_dtuple([(xopt, t1); (_, t2)]) ->  *)
(*           sn_prod xopt t1 t2 (fun t1 t2 -> Typ_dtuple([(xopt, t1); (None, t2)])) cont *)

(*       | Typ_refine(x, t1, t2, b) ->  *)
(*           sn_prod (Some x) t1 t2 (fun t1 t2 -> Typ_refine(x, t1, t2, b)) cont *)
            
(*       | Typ_affine t ->  *)
(*           sn tcenv {config with code=t; stack=[]} *)
(*             (fun c -> rebuild {config with code=W (Typ_affine c.code)} cont) *)
            
(*       | Typ_ascribed(t, _) ->  *)
(*           sn tcenv {config with code=t} cont *)

(*       | Typ_univ(a, k, [], t) ->  *)
(*           snk tcenv {code=k; environment=config.environment; stack=[]} *)
(*             (fun ck -> sn tcenv {config with  *)
(*                                    code=t;  *)
(*                                    stack=[]; *)
(*                                    environment=TDummy a::config.environment}  *)
(*                (fun ct ->  *)
(*                   (\* check_stack_empty config; *\) *)
(*                   cont {config with code=W (Typ_univ(a, ck.code, [], ct.code))})) *)
            
(*       | Typ_unknown -> rebuild config cont *)
          
(*       | Typ_uvar(uv, k) -> *)
(*           let t = compress config.code in  *)
(*             if t === config.code  *)
(*             then rebuild config cont  *)
(*             else sn tcenv {config with code=t} cont *)

(*       | Typ_record(fnt_l, topt) ->  *)
(*           let configs = fnt_l |> List.map (fun (_, t) -> {config with code=t; stack=[]}) in  *)
(*             snl tcenv configs (fun configs ->  *)
(*                                  let fnt_l = List.map2 (fun (fn, _) c -> (fn, c.code)) fnt_l configs in  *)
(*                                    match topt with  *)
(*                                      | None -> (\* check_stack_empty config;  *\) *)
(*                                          cont {config with code=W (Typ_record(fnt_l, None))} *)
(*                                      | Some t ->  *)
(*                                          sn tcenv {config with code=t}  *)
(*                                            (fun c ->  *)
(*                                               (\* check_stack_empty config;  *\) *)
(*                                               cont {config with code=W (Typ_record(fnt_l, Some c.code))})) *)
(*       | Typ_meta (Meta_PrePost(f1, t, f2)) ->  *)
(*           (\* check_stack_empty config; *\) *)
(*           snl tcenv ([{config with code=f1}; *)
(*                       {config with code=t}; *)
(*                       {config with code=f2}]) *)
(*             (fun [c1;c2;c3] ->  *)
(*                cont {config with code=W (Typ_meta(Meta_PrePost(c1.code, c2.code, c3.code)))}) *)
            
(*       | Typ_meta (Meta_cases tl) -> *)
(*           (\* snpar tcenv config tl (fun tl -> rebuild {config with code=W(Typ_meta (Meta_cases tl))} cont) *\) *)
            
(*           (\* check_stack_empty config; *\) *)
(*           snl tcenv (tl |> List.map (fun t -> {config with code=t})) *)
(*             (fun cl -> rebuild {config with code=W (Typ_meta (Meta_cases(cl |> List.map (fun c -> c.code))))} cont) *)
            
(*       | Typ_meta (Meta_named(s,t)) ->  *)
(*           (match config.stack with  *)
(*              | [] -> sn tcenv {config with code=t} (fun c -> cont {config with code=W (Typ_meta(Meta_named(s, c.code)))}) *)
(*              | _ -> sn tcenv {config with code=t} cont) *)

(*       | Typ_meta (Meta_tid i) -> rebuild config cont *)
          
(*       | Typ_meta (Meta_alpha t) ->   *)
(*           sn tcenv {config with code=t; stack=[]}  *)
(*             (fun c ->  *)
(*                (\* alpha (); *\) *)
(*                rebuild {config with code=alpha_convert c.code} cont) *)

(* (\* and snpar<'a> tcenv config tl (cont:typ list -> 'a) : 'a =  *\) *)
(* (\*   (Seq.ofList tl *\) *)
(* (\*   |> Seq.map (fun t ->  *\) *)
(* (\*                 async { *\) *)
(* (\*                   return (sn<typ> tcenv {config with code=t} (fun c -> c.code)) *\) *)
(* (\*                 }) *\) *)
(* (\*   |> Async.Parallel *\) *)
(* (\*   |> Async.RunSynchronously *\) *)
(* (\*   |> List.ofArray *\) *)
(* (\*   |> cont) *\) *)


(* and snl tcenv configs (cont:list<config<typ>> -> 'a) : 'a = match configs with  *)
(*   | [] -> cont [] *)
(*   | c::rest -> sn tcenv c (fun c -> snl tcenv rest (fun rest -> cont (c::rest))) *)

(* and snk tcenv (config:config<kind>) (cont:config<kind> -> 'a) : 'a =  *)
(*   match config.code with  *)
(*     | Kind_unknown *)
(*     | Kind_star *)
(*     | Kind_affine *)
(*     | Kind_prop *)
(*     | Kind_erasable -> cont config *)
(*     | Kind_tcon(aopt, k1, k2) ->  *)
(*         snk tcenv {config with code=k1}  *)
(*           (fun c1 ->  *)
(*              snk tcenv {config with  *)
(*                           code=k2; *)
(*                           environment=(match aopt with  *)
(*                                          | None -> config.environment *)
(*                                          | Some a -> TDummy a::config.environment)} *)
(*                (fun c2 -> cont {config with code=Kind_tcon(aopt, c1.code, c2.code)})) *)
                          
(*     | Kind_dcon(xopt, t1, k2) ->  *)
(*         sn tcenv {code=t1;environment=config.environment;stack=[]} *)
(*           (fun c1 ->  *)
(*              snk tcenv {config with  *)
(*                           code=k2; *)
(*                           environment=(match xopt with  *)
(*                                          | None -> config.environment *)
(*                                          | Some x -> VDummy x::config.environment)} *)
(*                (fun c2 -> cont {config with code=Kind_dcon(xopt, c1.code, c2.code)})) *)
          
(*     | Kind_boxed k ->  *)
(*         snk tcenv {config with code=k} *)
(*           (fun c -> cont {config with code=Kind_boxed c.code}) *)

(* and wne tcenv (config:config<exp>) (cont:config<exp> -> 'a) : 'a =  *)
(*   let W e = (ewithinfo e config.code.sort config.code.p) in *)
(*     (\* let W e (cont:exp -> 'a) : 'a =  *\) *)
(*   (\*   cont (ewithinfo e config.code.sort config.code.p) in *\) *)
(*   (\* let W e (cont:exp -> 'a) : 'a =  *\) *)
(*   (\*   sn tcenv {code=config.code.sort; *\) *)
(*   (\*             environment=config.environment; *\) *)
(*   (\*             stack=[]; *\) *)
(*   (\*             stacksz=0} *\) *)
(*   (\*     (fun ct -> cont (ewithinfo e ct.code config.code.p)) in *\) *)
(*     match config.code.v with  *)
(*       | Exp_fvar _  *)
(*       | Exp_constant _  *)
(*       | Exp_bot -> cont config *)

(*       | Exp_bvar x ->  *)
(*           (match config.environment |> Util.findOpt (function VDummy y | V (y, _, _) -> bvd_eq x.v y | _ -> false) with  *)
(*              | None -> cont config *)
(*              | Some (VDummy x) -> cont config *)
(*              | Some (V(x, vclos, m)) ->  *)
(*                  match !m with  *)
(*                    | Some v ->  *)
(*                        (\* nlazy(); *\) *)
(*                        wne tcenv {config with code=v; environment=snd vclos} cont *)
(*                    | None ->  *)
(*                        let config = {config with code=fst vclos; environment=snd vclos} in  *)
(*                          wne tcenv config (fun c -> m:=Some c.code; cont c)) *)
                           
(*       | Exp_constr_app(v, tl, [], el) ->  *)
(*           snl tcenv (tl |> List.map (fun t -> {code=t; environment=config.environment; stack=[]}))  *)
(*             (fun cl1 ->  *)
(*                wnel tcenv (el |> List.map (fun e -> {code=e; environment=config.environment; stack=[]})) *)
(*                  (fun cl2 ->  *)
(*                     cont {config with code=W (Exp_constr_app(v, cl1 |> List.map (fun c -> c.code), [], cl2 |> List.map (fun c -> c.code)))})) *)

(*       | Exp_ascribed(e, _, _) ->  *)
(*           wne tcenv {config with code=e} cont *)

(*       | Exp_primop(id, el) ->  *)
(*           wnel tcenv (el |> List.map (fun e -> {config with code=e})) *)
(*             (fun cl -> cont {config with code=W (Exp_primop(id, cl |> List.map (fun c -> c.code)))}) *)
            
(*       | _ -> failwith "NYI" *)
          
(*       (\* | Exp_recd       of option<lident> * list<typ> * list<exp> * list<fieldname * exp>  (\\* let r' = {r with f=1} *\\) *\) *)
(*       (\* | Exp_proj       of exp * fieldname  *\) *)
          
(*       (\* | Exp_abs _ ->  *\) *)
(*       (\* | Exp_tabs _ ->  *\) *)
(*       (\* | Exp_app        of exp * exp *\) *)
(*       (\* | Exp_tapp       of exp * typ                                     (\\* produced during type checking *\\) *\) *)
(*       (\* | Exp_match      of exp * list<pat * exp> * exp                   (\\* always includes a default case *\\) *\) *)
(*       (\* | Exp_cond       of exp * exp * exp        *\) *)
(*       (\* | Exp_let        of bool * list<bvvdef * typ * exp> * exp (\\* let (rec?) x1 = e1 AND ... AND xn = en in e *\\) *\) *)
(*       (\* | Exp_gvar       of int (\\* only for internal use by proof extraction. unbound variable deBruijn index *\\)  *\) *)
(*       (\* | Exp_extern_call of Sugar.externref * ident * typ * list<typ> * list<exp> *\) *)


(* and wnel tcenv configs (cont:list<config<exp>> -> 'a) : 'a = match configs with  *)
(*   | [] -> cont [] *)
(*   | c::rest -> wne tcenv c (fun c -> wnel tcenv rest (fun rest -> cont (c::rest))) *)



let rec sn tcenv (config:config<typ>) : config<typ> =
  let W t = (twithinfo t config.code.sort config.code.p) in
    
  (* let W t (cont:typ -> 'a) : 'a = *)
  (*   cont (twithinfo t config.code.sort config.code.p) in *)
    
  (* let W t (cont:typ -> 'a) : 'a = *)
  (*   snk tcenv {code=config.code.sort; *)
  (*              environment=config.environment; *)
  (*              stack=[]; *)
  (*              stacksz=0} *)
  (*     (fun ck -> cont (twithinfo t ck.code config.code.p)) in *)
  let rebuild config  = 
    let rec aux out stack : list<Disj<typ,exp> * kind * Range.range> = match stack with
      | [] -> List.rev out
      | TT((t,e),s,p)::rest -> 
          let c = sn tcenv {code=t; environment=e; stack=[]} in 
            aux ((Inl c.code,s,p)::out) rest 
      | VV((v,e),s,p)::rest -> 
          let c = wne tcenv {code=v; environment=e; stack=[]} in 
            aux ((Inr c.code,s,p)::out) rest in
    let tvl = aux [] config.stack  in
    let t = List.fold_left 
      (fun out (tv,s,p) -> match tv with 
         | Inl t -> twithinfo (Typ_app(out, t)) s p
         | Inr v -> twithinfo (Typ_dep(out, v)) s p)
      config.code
      tvl in 
      {config with code=t; stack=[]} in
    
  let sn_prod xopt t1 t2 mk = 
    let c1 = sn tcenv {config with code=t1; stack=[]} in
    let c2 = match xopt with 
      | None -> {config with code=t2; stack=[]}
      | Some x -> {config with code=t2; environment=VDummy x::config.environment; stack=[]} in
    let c2 = sn tcenv c2 in 
      {config with code=W (mk c1.code c2.code)} in
    
    match config.code.v with 
      | Typ_const(fv, eref) ->  
           (match lookup_typ_abbrev tcenv fv with
              | None -> rebuild config 
              | Some t -> (* delta(); alpha ();  *)sn tcenv {config with code=Absyn.alpha_convert t} )  (* code=AbsynUtils.alpha_fast t *)

      | Typ_btvar(btv) -> 
          (match config.environment |> Util.findOpt (function TDummy x | T (x, _, _) -> bvd_eq btv.v x | _ -> false) with 
             | None -> rebuild config (* possible for an open term *)
             | Some (TDummy x) -> rebuild config 
             | Some (T(x, (t,e), m)) -> 
                 (match !m with 
                    | Some t -> 
                        (* nlazy();  *)
                        sn tcenv {config with code=t; environment=e} 
                    | None -> 
                        let config' = {code=t; environment=e; stack=[]} in
                          (* let config = push (MemoT (fun t -> m:=Some t)) config in  *)
                        let c= sn tcenv config' in
                          m:=Some c.code;
                          sn tcenv {c with stack=config.stack})
             | _ -> raise Impos1)

      | Typ_app(t1, t2) -> 
          let se = TT((t2, config.environment), config.code.sort, config.code.p) in 
          let config = push se {config with code=t1} in 
            sn tcenv config 
              
      | Typ_dep(t, v) -> 
          let se = VV((v, config.environment),config.code.sort,config.code.p) in 
          let config = push se {config with code=t} in 
            sn tcenv config 

      | Typ_lam(x, t1, t2) -> 
          let c1 = sn tcenv {config with code=t1; stack=[]} in
            (match pop config with 
               | None, config -> 
                   let c2 = sn tcenv {config with 
                                        code=t2;
                                        environment=VDummy x::config.environment} in
                     {config with code=W (Typ_lam(x, c1.code, c2.code))} (* stack is empty *)
                       
               | Some (VV(vclos, _, _)), config -> 
                   (* beta(); *)
                   sn tcenv {config with 
                               code=t2;
                               environment=V(x,vclos,ref None)::config.environment}
                     
               | _ -> raise Impos2)
               
          
      | Typ_tlam(a, k, t) -> 
          let ck = snk tcenv {code=k; environment=config.environment; stack=[]} in
            (match pop config with 
               | None, config  -> 
                   let c = sn tcenv {config with 
                                       code=t;
                                       environment=TDummy a::config.environment} in 
                     {config with code=W (Typ_tlam(a, ck.code, c.code))}
                       (* stack is empty *)
                       
               | Some (TT(tclos, _, _)), config -> 
                   (* beta(); *)
                   sn tcenv {config with 
                               code=t;
                               environment=T(a,tclos,ref None)::config.environment}
                     
               | Some(VV _), config -> 
                   let _ = pr "Unexpected value argument on the stack\nExpected a type (or nothing)\n" in
                     raise Impos3)

      | Typ_fun(xopt, t1, t2) -> 
          sn_prod xopt t1 t2 (fun t1 t2 -> Typ_fun(xopt, t1, t2)) 

      | Typ_dtuple([(xopt, t1); (_, t2)]) -> 
          sn_prod xopt t1 t2 (fun t1 t2 -> Typ_dtuple([(xopt, t1); (None, t2)])) 
            
      | Typ_refine(x, t1, t2, b) -> 
          sn_prod (Some x) t1 t2 (fun t1 t2 -> Typ_refine(x, t1, t2, b)) 

      | Typ_affine t -> 
          let c = sn tcenv {config with code=t; stack=[]} in 
            rebuild {config with code=W (Typ_affine c.code)}
              
      | Typ_ascribed(t, _) -> 
          sn tcenv {config with code=t} 

      | Typ_univ(a, k, [], t) -> 
          let ck = snk tcenv {code=k; environment=config.environment; stack=[]} in 
          let ct = sn tcenv {config with 
                               code=t; 
                               stack=[];
                               environment=TDummy a::config.environment}  in 
            (* check_stack_empty config; *)
            {config with code=W (Typ_univ(a, ck.code, [], ct.code))}
              
      | Typ_unknown -> rebuild config 
          
      | Typ_uvar(uv, k) ->
          let t = compress_hard config.code in 
            if t === config.code 
            then rebuild config 
            else sn tcenv {config with code=t} 

      | Typ_record(fnt_l, topt) -> 
          let configs = fnt_l |> List.map (fun (_, t) -> {config with code=t; stack=[]}) in 
          let configs = snl tcenv configs in
          let fnt_l = List.map2 (fun (fn, _) c -> (fn, c.code)) fnt_l configs in 
            (match topt with 
               | None -> (* check_stack_empty config;  *)
                   {config with code=W (Typ_record(fnt_l, None))}
               | Some t -> 
                   let c = sn tcenv {config with code=t} in 
                     (* check_stack_empty config;  *)
                     {config with code=W (Typ_record(fnt_l, Some c.code))})

      | Typ_meta(Meta_pattern(t, ps)) -> 
        (* check_stack_empty config; *)
        let ts, vs = ps |> List.partition (function Inl _ -> true | _ -> false) in
        let cts = {config with code=t}::(ts |> List.map (fun (Inl t) -> {config with code=t})) in 
        let c::ts = snl tcenv cts in 
        let vs = wnel tcenv (vs |> List.map (fun (Inr v) -> {code=v; environment=config.environment; stack=[]})) in 
        {config with code=W (Typ_meta(Meta_pattern(c.code, (ts |> List.map (fun t -> Inl t.code)) @ (vs |> List.map (fun t -> Inr t.code)))))}
        
      | Typ_meta (Meta_PrePost(f1, t, f2)) -> 
          (* check_stack_empty config; *)
          let [c1;c2;c3] = snl tcenv [{config with code=f1};
                                      {config with code=t};
                                      {config with code=f2}] in 
            {config with code=W (Typ_meta(Meta_PrePost(c1.code, c2.code, c3.code)))}

      | Typ_meta (Meta_cases tl) ->
          (* snpar tcenv config tl (fun tl -> rebuild {config with code=W(Typ_meta (Meta_cases tl))} cont) *)
          let configs = tl |> List.map (fun t -> {config with code=t}) in 
          let cl = snl(* par *) tcenv configs in
          (* check_stack_empty config; *)
            (* let cl = snlpar tcenv config tl in  (\* (tl |> List.map (fun t -> {config with code=t})) in  *\) *)
            rebuild {config with code=W (Typ_meta (Meta_cases(cl |> List.map (fun c -> c.code))))}
              
      | Typ_meta (Meta_named(s,t)) -> 
          (match config.stack with 
             | [] ->  config
                 (* let c = sn tcenv {config with code=t} in  *)
                 (*   {config with code=W (Typ_meta(Meta_named(s, c.code)))} *)
             | _ -> sn tcenv {config with code=t})

      | Typ_meta (Meta_tid i) -> rebuild config 
          
      | Typ_meta (Meta_alpha t) ->  
          let c = sn tcenv {config with code=t; stack=[]} in
            rebuild {config with code=(* alpha_convert  *)c.code}
              
and snl tcenv configs : list<config<typ>> =

    List.map (sn tcenv) configs

and snlpar tcenv configs =
  (Seq.ofList configs
  |> Seq.map (fun c ->
                async {
                  return (sn tcenv c)
                })
  |> Async.Parallel
  |> Async.RunSynchronously
  |> List.ofArray)

        
and snk tcenv (config:config<kind>) : config<kind> =
    match config.code with 
      | Kind_unknown
      | Kind_star
      | Kind_affine
      | Kind_prop
      | Kind_erasable -> config
      | Kind_tcon(aopt, k1, k2) -> 
          let c1 = snk tcenv {config with code=k1} in
          let c2 = snk tcenv {config with 
                                code=k2;
                                environment=(match aopt with 
                                               | None -> config.environment
                                               | Some a -> TDummy a::config.environment)} in 
            {config with code=Kind_tcon(aopt, c1.code, c2.code)}
              
      | Kind_dcon(xopt, t1, k2) -> 
          let c1 = sn tcenv {code=t1;environment=config.environment;stack=[]} in
          let c2 = snk tcenv {config with 
                                code=k2;
                                environment=(match xopt with 
                                               | None -> config.environment
                                               | Some x -> VDummy x::config.environment)} in 
            {config with code=Kind_dcon(xopt, c1.code, c2.code)}
              
      | Kind_boxed k -> 
          let c = snk tcenv {config with code=k} in 
            {config with code=Kind_boxed c.code}

and wne tcenv (config:config<exp>) : config<exp> =
  let W e = (ewithinfo e config.code.sort config.code.p) in
    (* let W e (cont:exp -> 'a) : 'a =  *)
  (*   cont (ewithinfo e config.code.sort config.code.p) in *)
  (* let W e (cont:exp -> 'a) : 'a =  *)
  (*   sn tcenv {code=config.code.sort; *)
  (*             environment=config.environment; *)
  (*             stack=[]; *)
  (*             stacksz=0} *)
  (*     (fun ct -> cont (ewithinfo e ct.code config.code.p)) in *)
    match config.code.v with 
      | Exp_fvar _ 
      | Exp_constant _ 
      | Exp_bot -> config

      | Exp_bvar x -> 
          (match config.environment |> Util.findOpt (function VDummy y | V (y, _, _) -> bvd_eq x.v y | _ -> false) with 
             | None -> config
             | Some (VDummy x) -> config
             | Some (V(x, vclos, m)) -> 
                 match !m with 
                   | Some v -> 
                       (* nlazy(); *)
                       wne tcenv {config with code=v; environment=snd vclos} 
                   | None -> 
                       let config = {config with code=fst vclos; environment=snd vclos} in 
                       let c = wne tcenv config in 
                         m:=Some c.code; 
                         c)
                           
      | Exp_constr_app(v, tl, [], el) -> 
          let cl1 = snl tcenv (tl |> List.map (fun t -> {code=t; environment=config.environment; stack=[]})) in 
          let cl2 = wnel tcenv (el |> List.map (fun e -> {code=e; environment=config.environment; stack=[]})) in 
          let W = 
            if Tcenv.is_logic_function tcenv v
            then 
              let t = sn tcenv {code=config.code.sort ; environment=config.environment; stack=[]} in 
                fun e -> ewithinfo e t.code config.code.p
            else 
              W in 
            {config with code=W (Exp_constr_app(v, cl1 |> List.map (fun c -> c.code), [], cl2 |> List.map (fun c -> c.code)))}

      | Exp_ascribed(e, _, _) -> 
          wne tcenv {config with code=e} 

      | Exp_primop(id, el) -> 
          let cl = wnel tcenv (el |> List.map (fun e -> {config with code=e})) in 
            {config with code=W (Exp_primop(id, cl |> List.map (fun c -> c.code)))}

      | Exp_recd(lid_opt, tl, vl, fne_l) -> 
        let fl, el = List.unzip fne_l in
        let fne_l = List.zip fl (List.map (fun c -> c.code) (wnel tcenv (el |> List.map (fun e -> {config with code=e})))) in
        let tl = snl tcenv (tl |> List.map (fun t -> {code=t; environment=config.environment; stack=[]})) in 
        let vl = wnel tcenv (vl |> List.map (fun v -> {config with code=v})) in
        {config with code=W (Exp_recd(lid_opt, tl |> List.map (fun c -> c.code), vl |> List.map (fun v -> v.code), fne_l))}

      | Exp_proj(e, f) -> 
        let {code=e} = wne tcenv {config with code=e} in 
        {config with code=W(Exp_proj(e, f))}

      | _ -> failwith (spr "NYI: %s" (Pretty.strExp config.code))
          
      (* | Exp_recd       of option<lident> * list<typ> * list<exp> * list<fieldname * exp>  (\* let r' = {r with f=1} *\) *)
      (* | Exp_proj       of exp * fieldname  *)
          
      (* | Exp_abs _ ->  *)
      (* | Exp_tabs _ ->  *)
      (* | Exp_app        of exp * exp *)
      (* | Exp_tapp       of exp * typ                                     (\* produced during type checking *\) *)
      (* | Exp_match      of exp * list<pat * exp> * exp                   (\* always includes a default case *\) *)
      (* | Exp_cond       of exp * exp * exp        *)
      (* | Exp_let        of bool * list<bvvdef * typ * exp> * exp (\* let (rec?) x1 = e1 AND ... AND xn = en in e *\) *)
      (* | Exp_gvar       of int (\* only for internal use by proof extraction. unbound variable deBruijn index *\)  *)
      (* | Exp_extern_call of Sugar.externref * ident * typ * list<typ> * list<exp> *)


and wnel tcenv configs : list<config<exp>> = 
    List.map (wne tcenv) configs 

      
let strong_normalize tcenv t = 
  reset_stats ();
  let c = "strong_normalize" ^^ lazy sn tcenv {code=t; environment=[]; stack=[]} in
    (* print_stats(); *)
    c.code
