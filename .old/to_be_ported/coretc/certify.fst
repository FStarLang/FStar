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
module Certify
open Terms
open Env
open Typing

type cert_t = option (i:icompartment * f:environment * b:bindings * 
                        a:acontext * e:expr * t:typ * expression_ty i f b a Term_level e t)
type result = {bindings:bindings;
               cert:cert_t}
      
 let eqName (n1:string) (n2:string) = n1 = n2
 let eqBvar = eqName
 let eqTyname = eqName
 let eqVlname = eqName
 let eqCname = eqName
 let eqIname = eqName
 let eqBoxname = eqName
 
 val eqGvar: gvar 'a -> gvar 'a -> bool
 let eqGvar gv1 gv2 =
   match gv1, gv2 with
     | GV_Bound bv1, GV_Bound bv2 -> eqBvar bv1 bv2
	 | GV_Free a1, GV_Free a2 -> a1 = a2
	 | _, _ -> false

val list_exists: ('a -> bool) -> list 'a -> bool
let rec list_exists f ls =
  match ls with
    | [] -> false
	| hd::tl -> if (f hd) then true else (list_exists f tl)

let addToList x ls =
  if list_exists (fun y -> x = y) ls then ls else x::ls

type bds = bindings
let emptyBds: bds = []
val addToBds: bindings -> bds -> bds
let rec addToBds (b:bindings) bs =
  match b with
    | [] -> bs
	| hd::tl -> addToBds tl (addToList hd bs)

val strcat3: string -> string -> string -> string
let strcat3 s1 s2 s3 = strcat (strcat s1 s2) s3

val strcat4: string -> string -> string -> string -> string
let strcat4 s1 s2 s3 s4 = (* Definition s1 := s2 s3 s4. *)
  strcat "Definition " (strcat s1 (strcat " := " (strcat s2 (strcat s3 (strcat " " (strcat s4 "."))))))

val writeBindings: string -> bds -> unit
let rec writeBindings fs bs =
  (* LB_BvarTy bvar t ==> Definition bvar := LB_BvarTy bvar t *)
  (* LB_BvarKind bvar k ==> Definition bvar := LB_BvarKind bvar k *)
  let writeOne b =
    let getName bvar =
	  let name = strcat bvar (freshname true) in
	  addBindings (boxToObject b) name; name in
    match b with
      | LB_BvarTy bvar t ->
	    printfile fs (strcat4 (getName bvar) "LB_BvarTy " (string_of_any_for_coq bvar) (string_of_any_for_coq t))
      | LB_BvarKind bvar k -> 
	    printfile fs (strcat4 (getName bvar) "LB_BvarKind " (string_of_any_for_coq bvar) (string_of_any_for_coq k)) 
      | _ -> true in
  match bs with
    | [] -> ()
    | b::rest -> writeOne b; writeBindings fs rest


val dowfE: bds -> i:icompartment -> e:environment -> b:bindings -> a:acontext -> m:mode -> exp:expr -> t:typ -> expression_ty i e b a m exp t -> bds
val dowfV: bds -> i:icompartment -> e:environment -> b:bindings -> a:acontext -> m:mode 
           -> v:value -> t:typ -> value_ty i e b a m v t -> bds
val dowfT: bds -> i:icompartment -> e:environment -> b:bindings -> t:typ -> k:kind -> wfT i e b t k -> bds
val dowfK: bds -> i:icompartment -> e: environment -> b:bindings -> k: kind -> bk: basekind -> wfK i e b k bk -> bds
val dowfEnv: bds -> i:icompartment -> e:environment -> b:bindings -> wfEnv i e b -> bds

let rec dowfEnv (bs: bds) i e b0 (wfenv: wfEnv i e b0) = addToBds b0 bs

and dowfK bs i e b0 k bk (wfk: wfK i e b0 k bk) =
    match wfk with
      | WFK_Base _ _ _ _ wfenv -> dowfEnv bs i e b0 wfenv
      | WFK_ProdK _ _ _ a k1 b1 k2 b2 _ wfk1 wfk2 ->
	    let bs = dowfK bs i e b0 k1 b1 wfk1 in
		dowfK bs i e ((LB_BvarKind a k1)::b0) k2 b2 wfk2
      | WFK_ProdT _ _ _ x t tb k b _ wft wfk2 ->
	    let bs = dowfT bs i e b0 t (K_Base tb) wft in
		dowfK bs i e ((LB_BvarTy x t)::b0) k b wfk2

and dowfT bs i e b0 t k wft =
  match wft with
    | WFT_Var _ _ _ a k wfenv _ -> dowfEnv bs i e b0 wfenv
    | WFT_FVar _ _ _ a k wfenv _ -> dowfEnv bs i e b0 wfenv
    | WFT_Ind _ _ _ _ _ wfenv _ -> dowfEnv bs i e b0 wfenv
    | WFT_VApp _ _ _ u v x t k kres wft wfv _ ->
      let bs = dowfT bs i e b0 u (K_ProdT x t k) wft in
      dowfV bs i e b0 [] Type_level v t wfv
    | WFT_App _ _ _ t u a k k' kres wft wft' _ ->
      let bs = dowfT bs i e b0 t (K_ProdK a k k') wft in
      dowfT bs i e b0 u k wft'
    | WFT_Prod _ _ _ x t bt u bu _ _ wft wft' ->
      let bs = dowfT bs i e b0 t (K_Base bt) wft in
      dowfT bs i e ((LB_BvarTy x t)::b0) u (K_Base bu) wft'
    | WFT_ProdK _ _ _ a k b u bu _ wfk wft' ->
      let bs = dowfK bs i e b0 k b wfk in
      dowfT bs i e ((LB_BvarKind a k)::b0) u (K_Base bu) wft'
    | WFT_Ref _ _ _ x t phi bt _ wft wft' ->
      let bs = dowfT bs i e b0 t (K_Base bt) wft in
      dowfT bs i e ((LB_BvarTy x t)::b0) phi (K_Base BK_Erase) wft'
    | WFT_Lam _ _ _ x t bt u ku _ wft wft' ->
      let bs = dowfT bs i e b0 t (K_Base bt) wft in
      dowfT bs i e ((LB_BvarTy x t)::b0) u ku wft'
    | WFT_Afn _ _ _ t wft' -> dowfT bs i e b0 t (K_Base BK_Comp) wft'
    | WFT_Ascribe _ _ _ t k wft' ->dowfT bs i e b0 t k wft'
    | WFT_Sub _ _ _ t k k' b wft' _ wfk ->
      let bs = dowfT bs i e b0 t k wft' in
      dowfK bs i e b0 k' b wfk

and dowfV bs i e b0 a m v t0 wfv = 
  match wfv with
    | WFV_Var _ _ _ m x t wfenv _ wft ->
      let bs = dowfEnv bs i e b0 wfenv in
      dowfT bs i e b0 t (K_Base BK_Comp) wft
    | WFV_VarT _ _ _  x t wfenv _ -> dowfEnv bs i e b0 wfenv
    | WFV_VarA _ _ _ m x t wfenv _ -> dowfEnv bs i e b0 wfenv
    | WFV_FVar _ _ _ m x t wfenv _ -> dowfEnv bs i e b0 wfenv
    | WFV_Const _ _ _ _ m c ts vs tc u k x cmon ex _ _ _ wft wfe ->
      let bs = dowfT bs i e b0 u k wft in
      dowfE bs i e ((LB_BvarTy x tc)::b0) a m ex u wfe
    | WFV_Fun _ _ _ _ m t bt u x body _ _ _ wft wfe ->
      let bs = dowfT bs i e b0 t (K_Base bt) wft in
      dowfE bs i e ((LB_BvarTy x t)::b0) (x::a) m body u wfe
    | WFV_FunT _ _ _ _ m k bk u al body _ _ wfk wfe ->
      let bs = dowfK bs i e b0 k bk wfk in
      dowfE bs i e ((LB_BvarKind al k)::b0) a m body u wfe
    | WFV_Ref _ _ _ _ m v x tt phi _ wfv ->
      let bs = addToBds ((LB_VlEq v (V_Var (GV_Bound x)))::(LB_BvarTy x tt)::b0) bs in
      dowfV bs i e b0 a m v tt wfv
    | WFV_WeakenX _ _ _ _ x1 x2 m v tt _ wfv ->
      dowfV bs i e b0 x1 m v tt wfv
    | WFV_Ascribe _ _ _ _ m v t wfv ->dowfV bs i e b0 a m v t wfv
    | WFV_Sub _ _ _ _ m v t u k wfv _ wft' ->
      let bs = dowfV bs i e b0 a m v t wfv in
      dowfT bs i e b0 u k wft'

and dowfE bs i e b0 a m ex t wfe = 
  match wfe with
    | WFE_Val _ _ _ _ _ v _ wfv -> dowfV bs i e b0 a m v t wfv
    | WFE_App _ _ _ _ x1 x2 m ex v x t u tv tres _ _ _ wfe wfv ->
      let bs = dowfE bs i e b0 x1 m ex tv wfe in
      dowfV bs i e b0 x2 m v t wfv
    | WFE_TApp _ _ _ _ m al k tt ex te u tres _ _ wfe wft ->
      let bs = dowfE bs i e b0 a m ex te wfe in
      dowfT bs i e b0 tt k wft
    | WFE_LetIn _ _ _ _ x1 x2 m x ex body t bt u bu _ wft1 wft2 _ wfe1 wfe2 ->
      let bs = dowfT bs i e b0 t (K_Base bt) wft1 in
      let bs = dowfT bs i e b0 u (K_Base bu) wft2 in
      let bs = dowfE bs i e b0 x1 m ex t wfe1 in 
      dowfE bs i e ((LB_BvarTy x t)::b0) (x::x2) m body u wfe2
    | WFE_Match _ _ _ _ x1 x2 m eqs b' v pt pv ethen eelse t bt tv btv tpat c alphas xs tc ts vs bthen xthen astyps asvals icompbinds binds _ _ appnd _ wft1 wft2 _ wfv1 wfv2 wfethen wfeelse ->
      let bs = dowfT bs i e b0 tv (K_Base btv) wft1 in
      let bs = dowfT bs i e b0 t (K_Base bt) wft2 in
      let bs = dowfV bs i e b0 x1 m v tv wfv1 in
      let bs = dowfV bs i e b' xs m (V_Const c ts vs) tpat wfv2 in
      let bs = dowfE bs i e bthen xthen m ethen t wfethen in
      dowfE bs i e b0 x2 m eelse t wfeelse
    | WFE_Assume _ _ _ _ m x phi wft -> dowfT bs i e b0 phi (K_Base BK_Erase) wft
    | WFE_WeakenX _ _ _ _ x1 x2 m ee t _ wfe -> dowfE bs i e b0 x1 m ee t wfe
    | WFE_Ascribe _ _ _ _ m ee t wfe -> dowfE bs i e b0 a m ee t wfe
    | WFE_Sub _ _ _ _ m ee t u k wfe _ wft ->
      let bs = dowfE bs i e b0 a m ee t wfe in
      dowfT bs i e b0 u k wft

val pushBvarTy: bvar -> typ -> bindings -> bindings
let pushBvarTy x t b = (LB_BvarTy x t)::b 

val certifyLetBinding : bool -> string -> i:icompartment -> g:environment -> wfIG i g 
                        -> b:bindings -> x:bvar -> e:expr  -> result
let certifyLetBinding letrec fs i g wfig b x e = 
  (* let _ = print_stderr "Trying to certify typing for term:" in *)
  (* let _ = print_stderr (string_of_any_for_coq e) in  *)
  (* let _ = print_stderr "" in *)
  let a = ([]:acontext) in
  let _ = clearBindings(true) in
  let (t, aa, _, _, cert) = check_expr i g wfig b a Term_level e in 
    (*let bs = dowfE emptyBds i f b aa Term_level e t cert in*)
  let _ = println "" in
  let _ = println (strcat "Certified type: " (string_of_any_for_coq t)) in
  let _ = printfile fs "" in
    (*let _ = writeBindings fs bs in*)
  let name = writeCertToFile fs (SomeP cert) in
  let _ = printfile fs "Definition checked_certificate := " in
  let _ = printfile fs (strcat name ".") in
    (*let _ = printfile fs (strcat (strcat "Definition checked_certificate := " name) ".") in*)
  let b' = if letrec then b else pushBvarTy x t b in
  let c = ((Some (i, g, b, aa, e, t, cert)) : cert_t) in
  let res = {bindings=b'; cert=c} in 
    res 

