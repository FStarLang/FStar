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

module Microsoft.FStar.Z3Encoding.BasicDT
open Microsoft.FStar

open Microsoft.Z3
open Util
open Term
open Absyn

type ppmap = HashMultiMap<string,string>
#if HASH
 type map<'a,'b> = HashMultiMap<'a,'b>
 let map_create i = Hashtbl.create i
 let map_tryfind m k = Hashtbl.tryfind m k
 let map_add m k v = Hashtbl.add m k v; m
 let map_replace m k v = Hashtbl.replace m k v; m
#else
 type map<'a,'b> = list<('a*'b)> 
 let map_create i = []
 let map_tryfind m k =
   match findOpt (fun (k', _) -> k=k') m with 
     | None -> None
     | Some(_,v) -> Some v
 let map_add m k v = (k,v)::m
 let map_replace m k v = (k,v)::m
#endif

type opState' = {ops:list<op>; 
                 qops:list<op>;
                 env:option<Tcenv.env>;
                 ctr:int;
                 uvars:list<(Unionfind.uvar<uvar_basis> * kind) * tm * ops>;
                 transformers:(map<int, map<int, list<(typ * tm * option<phi>)>>> * 
                               map<int, (typ * option<phi>)>);
                 bvars:list<bvvar * tm * ops>;
                 fvars:list<var<typ> * tm * ops>;
                 strings:list<byte[] * tm * ops>;
                 floats:list<float * tm * ops>;
                 holds_map:list<sort * string>;
                 cached_ops:list<lident * ops>;
                 unfoldings:list<binders * typ * typ>;
                 labels:list<string * tm>;
                 pp_name_map:ppmap;
                 qid:int;
                 named_typ_map:list<string*tm>}
and opState = {termctx:termctx; st:opState'; strip_labels:bool}
and termctx = ptermctx<residue>
and binders = list<bvvar>
and residue = 
  | MkResidue of (tm * (* kind * *) option<tm> * (renaming -> Expr -> ST<(ops * tm)>))
and tm = term<residue>
and phi        = tm (* documenting terms that are expected to be formulas *)
and renaming = list<Disj<btvdef,bvvdef>*termref<residue>>
and ST<'a> = state<opState, 'a>
and op = op<residue>
and ops = list<op> 
type STR<'a> = ('a * opState)

let replaceDeclaration f def =
  upd (fun st -> 
    let pfx, foundOpt, suffix = Util.prefixUntil st.st.ops (function DeclFun(g, _, _, _) -> f=g | _ -> false) in 
    {st with st={st.st with ops=pfx@def@suffix}})
(* List.split  *)
(* let ops = List.filter (function DeclFun(g, _, _, _) when f = g -> false | _ -> true) st.st.ops in  *)
(*   {st with st={st.st with ops=ops}}) *)

let removeDeclaration f =
  upd (fun st -> 
         let ops = List.filter (function DeclFun(g, _, _, _) when f = g -> false | _ -> true) st.st.ops in 
           {st with st={st.st with ops=ops}})
           
let lookupHoldsMap sort : ST<option<string>> = 
  get >> (fun st -> 
  match findOpt (fun (s, _) -> s=sort) st.st.holds_map with 
    | None -> ret None
    | Some(_, f) -> ret (Some f))

let insertHoldsMap s : ST<unit> = 
  upd (fun st -> {st with st={st.st with holds_map=s::st.st.holds_map}})

let normalizeTerm tm = 
  let crossbinders n subst = 
    let rebindings = 
      Hashtbl.fold (fun key v out -> 
                      match v with 
                        | Inl _ -> out
                        | Inr tm -> (key, Inr (incrBoundV n tm))::out) subst [] in 
      List.iter (fun (key, v) -> Hashtbl.replace subst key v) rebindings in
  let rec norm subst tm = match tm.tm with 
    | True
    | False
    | Funsym _
    | Integer _
    | BoundV _
    | FreeV _ 
    | Z3Term _ -> tm
    | Minus tm -> Minus (norm subst tm)
    | ResFree  tm -> ResFree (norm subst tm)
    | App(f,s,tms) -> App(f,s, norm_array subst tms)
    | Not tm -> Not(norm subst tm)
    | PP(t1, t2) ->  norm2 subst t1 t2 (fun t1 t2 -> PP(t1,t2))
    | Add(t1, t2) -> norm2 subst t1 t2 (fun t1 t2 -> Add(t1,t2))
    | Sub(t1, t2) -> norm2 subst t1 t2 (fun t1 t2 -> Sub(t1,t2))
    | Div(t1, t2) -> norm2 subst t1 t2 (fun t1 t2 -> Div(t1,t2))
    | Mod(t1, t2) -> norm2 subst t1 t2 (fun t1 t2 -> Mod(t1,t2))
    | Mul(t1, t2) -> norm2 subst t1 t2 (fun t1 t2 -> Mul(t1,t2))
    | And(t1,t2) -> norm2 subst t1 t2 (fun t1 t2 -> And(t1,t2))
    | Or(t1,t2) ->  norm2 subst t1 t2 (fun t1 t2 -> Or(t1,t2))
    | Imp(t1,t2) -> norm2 subst t1 t2 (fun t1 t2 -> Imp(t1,t2))
    | Iff(t1,t2) -> norm2 subst t1 t2 (fun t1 t2 -> Iff(t1,t2))
    | Eq(t1,t2) ->  norm2 subst t1 t2 (fun t1 t2 -> Eq(t1,t2))
    | LT(t1,t2) ->  norm2 subst t1 t2 (fun t1 t2 -> LT(t1,t2))
    | LTE(t1,t2) -> norm2 subst t1 t2 (fun t1 t2 -> LTE(t1,t2))
    | GT(t1,t2) ->  norm2 subst t1 t2 (fun t1 t2 -> GT(t1,t2))
    | GTE(t1,t2) -> norm2 subst t1 t2 (fun t1 t2 -> GTE(t1,t2))
    | Select(t1,t2) -> norm2 subst t1 t2 (fun t1 t2 -> Select(t1, t2))
    | Update(t1,t2,t3) -> norm3 subst t1 t2 t3 (fun t1 t2 t3 -> Update(t1,t2,t3))
    | IfThenElse(t1,t2,t3,topt) -> 
        norm3 subst t1 t2 t3 (fun t1 t2 t3 -> 
        let topt = norm_opt subst topt in 
        IfThenElse(t1,t2,t3,topt))
    | Forall(pats,sorts,vars,tm) -> 
        crossbinders (Array.length sorts) subst;
        Forall(pats,sorts,vars, norm subst tm)
    | Exists(pats,sorts,vars,tm) -> 
        crossbinders (Array.length sorts) subst;
        Exists(pats,sorts,vars, norm subst tm)
    | ConstArray(s,sort,tm) -> 
        ConstArray(s, sort, norm subst tm)
    | Cases(tl) -> 
        Cases(norm_list subst tl)
    | Residue(t1,MkResidue(t2, t3opt, builder)) -> 
        let builder' r t = 
          builder r t >> (fun (ops, tm) -> 
          ret (ops, norm subst tm)) in
          Residue(norm subst t1, 
                  MkResidue(norm subst t2, 
                            norm_opt subst t3opt, 
                            builder'))
    | Hole x -> 
        (match Hashtbl.tryfind subst x with 
           | Some (Inl tm')
           | Some (Inr tm') -> 
               if tm.tmsort <> tm'.tmsort 
               then raise (Bad (spr "Sort mismatch in normalize term: expected %A got %A\n" tm.tmsort tm'.tmsort))
               else tm'
           | None -> tm)
    | Application({tm=Function(var,s,tm)}, arg) -> 
        Hashtbl.add subst var (Inr (norm subst arg));
        norm subst tm
    | Function _ -> tm
    | Application(t1,t2) -> 
        let t1 = norm subst t1 in 
          (match t1.tm with 
             | Function _  -> norm subst (Application(t1, t2))
             | _ -> Application(t1, t2))
            (* norm2 subst t1 t2 (fun t1 t2 -> Application(t1,t2)) *)
  and norm_list subst l =
    l |> List.map (fun tm -> norm subst tm)
  and norm_array subst l =
    l |> Array.map (fun tm -> norm subst tm)
  and norm_opt subst = function 
    | None -> None
    | Some t -> Some (norm subst t)
  and norm2 subst t1 t2 f = 
    let t1 = norm subst t1 in 
    let t2 = norm subst t2 in 
      f t1 t2
  and norm3 subst t1 t2 t3 f = 
    let t1 = norm subst t1 in 
    let t2 = norm subst t2 in 
    let t3 = norm subst t3 in 
      f t1 t2 t3
  in 
    (* pr "start norm\n"; *)
  let t = norm (Hashtbl.create 100) tm in 
    (* pr "done\n"; *)
    t
      
let normalizeOp op = match op with 
  | Assume(tm,c,a) -> Assume(normalizeTerm tm, c, a)
  | Query(tm) -> Query(normalizeTerm tm)
  | _ -> op

let mkPrelude typenames termconstrs = 
spr  "(declare-sort Pseudo_term) \n \
      (declare-datatypes () ((Pseudo_term_opt (PTNone) \n \
                                              (PTSome (Primitive_PTSome_proj_0 Pseudo_term))))) \n \
      (declare-sort Ref)\n \
      (declare-datatypes () ((String (String_const (String_const_proj_0 Int))))) \n \
      (declare-datatypes () ((Type_name %s))) \n \
      (declare-datatypes () ((Kind (Kind_star)  \n \
                                   (Kind_erasable) \n \
                                   (Kind_affine) \n \
                                   (Kind_prop) \n \
                                   (Kind_tcon (Kind_tcon_fst Kind) (Kind_tcon_snd Kind)) \n \
                                   (Kind_dcon (Kind_dcon_fst Type) (Kind_dcon_snd Kind))) \n \
                             (Type (Typ_undef) \n \
                                   (Typ_other (Typ_other_fst Int)) \n \
                                   (Typ_btvar (Typ_btvar_fst Int)) \n \
                                   (Typ_const (Typ_const_fst Type_name)) \n \
                                   (Typ_fun   (Typ_fun_fst Type) (Typ_fun_snd Type)) \n \
                                   (Typ_univ  (Typ_univ_fst Kind) (Typ_univ_snd Type)) \n \
                                   (Typ_dtuple (Typ_dtuple_fst Type) (Typ_dtuple_snd Type)) \n \
                                   (Typ_refine (Typ_refine_fst Type) (Typ_refine_snd Type)) \n \
                                   (Typ_app (Typ_app_fst Type) (Typ_app_snd Type)) \n \
                                   (Typ_dep (Typ_dep_fst Type) (Typ_dep_snd Term)) \n \
                                   (Typ_lam (Typ_lam_fst Type) (Typ_lam_snd Type)) \n \
                                   (Typ_tlam (Typ_tlam_fst Kind) (Typ_tlam_snd Type)) \n \
                                   (Typ_affine (Typ_affine_fst Type))) \n \
                             (Term (Term_undef) \n \
                                   (Exp_bvar (Exp_bvar_proj_0 Int))\n \
                                   (Term_other (Term_other_proj_0 Int)) \n \
                                   (BoxInt (BoxInt_proj_0 Int)) \n \
                                   (BoxBool (BoxBool_proj_0 Bool)) \n \
                                   (BoxString (BoxString_proj_0 String)) \n \
                                   (BoxRef (BoxRef_proj_0 Ref)) \n \
                                   %s )))\n"
    typenames termconstrs

(* (assert (forall ((t Type) (x Term)) *)
(*                 (! (= (TypeOf x) t) *)
(*                    :pattern (Term_constr_Prims.V t x)))) *)


let mk_Kind_star  ()     = App("Kind_star", Kind_sort, [||])
let mk_Kind_erasable ()  = App("Kind_erasable", Kind_sort, [||])
let mk_Kind_affine   ()  = App("Kind_affine", Kind_sort, [||])
let mk_Kind_prop     ()  = App("Kind_prop", Kind_sort, [||])
let mk_Kind_dcon t1 t2 = App("Kind_dcon", Arrow(Type_sort, Arrow(Kind_sort, Kind_sort)), [|t1;t2|])
let mk_Kind_tcon t1 t2 = App("Kind_tcon", Arrow(Kind_sort, Arrow(Kind_sort, Kind_sort)), [|t1;t2|])

let boxInt t            = App("BoxInt", Arrow(Int_sort, Term_sort), [| t |]) 
let unboxInt t          = App("BoxInt_proj_0", Arrow(Term_sort, Int_sort), [| t |]) 
let boxBool t           = App("BoxBool", Arrow(Bool_sort, Term_sort), [| t |]) 
let unboxBool t         = App("BoxBool_proj_0", Arrow(Term_sort, Bool_sort), [| t |]) 
let boxString t         = App("BoxString", Arrow(String_sort, Term_sort), [| t |]) 
let unboxString t       = App("BoxString_proj_0", Arrow(Term_sort, String_sort), [| t |]) 
let boxRef t            = App("BoxRef", Arrow(Ref_sort, Term_sort), [| t |]) 
let unboxRef t          = App("BoxRef_proj_0", Arrow(Term_sort, Ref_sort), [| t |]) 
let boxTerm sort t = match sort with 
  | Int_sort -> boxInt t
  | Bool_sort -> boxBool t
  | String_sort -> boxString t
  | Ref_sort -> boxRef t
  | _ -> raise Impos
let unboxTerm sort t = match sort with 
  | Int_sort -> unboxInt t
  | Bool_sort -> unboxBool t
  | String_sort -> unboxString t
  | Ref_sort -> unboxRef t
  | _ -> raise Impos

let mk_Typ_const n      = App("Typ_const", Arrow(Ext "Type_name", Type_sort), [|App(n, Ext "Type_name", [||])|])
let mk_Typ_fun t1 t2    = App("Typ_fun", Arrow(Type_sort, Arrow(Type_sort, Type_sort)), [|t1;t2|])
let mk_Typ_univ t1 t2   = App("Typ_univ", Arrow(Kind_sort, Arrow(Type_sort, Type_sort)), [|t1;t2|])
let mk_Typ_dtuple t1 t2 = App("Typ_dtuple", Arrow(Type_sort, Arrow(Type_sort, Type_sort)), [|t1;t2|])
let mk_Typ_refine t1 t2 = App("Typ_refine", Arrow(Type_sort, Arrow(Type_sort, Type_sort)), [|t1;t2|])
let mk_Typ_app t1 t2    = App("Typ_app", Arrow(Type_sort, Arrow(Type_sort, Type_sort)), [|t1;t2|])
let mk_Typ_dep t1 t2    = App("Typ_dep", Arrow(Type_sort, Arrow(Term_sort, Type_sort)), [|t1;t2|])
let mk_Typ_affine t1    = App("Typ_affine", Arrow(Type_sort, Type_sort), [|t1|])
let mk_Typ_lam t1 t2    = App("Typ_lam", Arrow(Type_sort, Arrow(Type_sort, Type_sort)), [|t1;t2|])
let mk_Typ_tlam t1 t2   = App("Typ_tlam", Arrow(Kind_sort, Arrow(Type_sort, Type_sort)), [|t1;t2|])

let p2t_name = "p2t"
let p2t p = App(p2t_name, Arrow(Pseudo_term_sort, Term_sort), [|p|])

let t2p_name = "t2p"
let t2p t = App(t2p_name, Arrow(Term_sort, Pseudo_term_sort), [| t |])

let ptnone_name = "PTNone"
let ptnone : tm = FreeV(ptnone_name, Pseudo_term_opt_sort)

let ptsome_name = "PTSome"
let ptsome p = App(ptsome_name, Arrow(Pseudo_term_sort, Pseudo_term_opt_sort), [|p|])
let ptsome_proj_0 p = App(mkProj "PTSome" 0, Arrow(Pseudo_term_opt_sort, Pseudo_term_sort), [|p|])

let kOfName = "KindOf"
let kindOf t  = App(kOfName, Arrow(Type_sort, Kind_sort), [| t |]) 

let tOfName = "TypeOf"
let typeOf t  = App(tOfName, Arrow(Term_sort, Type_sort), [| t |]) 

let boolTerm b = if b then True() else False()

let mkTypeConstant i = App("Typ_other", Arrow(Int_sort, Type_sort), [| Integer i |])

let mkTermConstant i = App("Term_other", Arrow(Int_sort, Term_sort), [| Integer i |])
let unitTerm = mkTermConstant -1 
let unitAssumption =
  let unitType = mk_Typ_const (typeNameOfLid Const.unit_lid) in
    Assume(Eq(typeOf unitTerm, unitType), None, AName "unitval")

let mkStringConstant i = App("String_const", Arrow(Int_sort, String_sort), [| Integer i |])

let typeOfV = 
  let tref = termref() in
  let tident = ident("t",dummyRange) in
  let t =  BoundV(1, Type_sort, "t", tref) in 
  let xref = termref() in
  let xident = ident("x",dummyRange) in
  let x =  BoundV(0, Term_sort, "x", xref) in 
  let v = App("Term_constr_Prims.V", Arrow(Type_sort, Arrow(Term_sort, Term_sort)), [| t;x |]) in 
    Assume(Forall([v],
                  [| Type_sort; Term_sort |], 
                  [|(Inl(mkbvd(tident,tident)), tref); 
                    (Inr(mkbvd(xident,xident)), xref)|], 
                  (Imp(Eq(typeOf x, t), 
                       Eq(typeOf v, mk_Typ_app (mk_Typ_const "Type_name_Prims.result") t)))),
           None, 
           AName "V typing")

let typeOfE = 
  let tref = termref() in
  let tident = ident("t",dummyRange) in
  let t =  BoundV(1, Type_sort, "t", tref) in 
  let xref = termref() in
  let xident = ident("x",dummyRange) in
  let x =  BoundV(0, Term_sort, "x", xref) in 
  let v = App("Term_constr_Prims.E", Arrow(Type_sort, Arrow(Term_sort, Term_sort)), [| t;x |]) in 
    Assume(Forall([v],
                  [| Type_sort; Term_sort |], 
                  [|(Inl(mkbvd(tident,tident)), tref); 
                    (Inr(mkbvd(xident,xident)), xref)|], 
                  (Imp(Eq(typeOf x, mk_Typ_const "Type_name_Prims.exn"), 
                       Eq(typeOf v, mk_Typ_app (mk_Typ_const "Type_name_Prims.result") t)))),
           None, 
           AName "E typing")

let typeOfErr = 
  let tref = termref() in
  let tident = ident("t",dummyRange) in
  let t =  BoundV(0, Type_sort, "t", tref) in 
  let v = App("Term_constr_Prims.Err", Arrow(Type_sort, Term_sort), [| t |]) in 
    Assume(Forall([v],
                  [| Type_sort |], 
                  [|(Inl(mkbvd(tident,tident)), tref) |], 
                  (Eq(typeOf v, mk_Typ_app (mk_Typ_const "Type_name_Prims.result") t))),
           None, 
           AName "Err typing")

let intTyping =
  let xref = termref() in
  let xident = ident("x",dummyRange) in
  let x =  BoundV(0, Term_sort, "x", xref) in 
    Assume(Forall([],
                  [| Term_sort |], 
                  [|(Inr(mkbvd(xident,xident)), xref)|], 
                  (Imp(App(mkTester "BoxInt", Arrow(Term_sort, Bool_sort), [|x|]),
                       Eq(typeOf x, mk_Typ_const (typeNameOfLid Const.int_lid))))), 
           None, 
           AName "Int typing")

let boolTyping =
  let xref = termref() in
  let xident = ident("x",dummyRange) in
  let x =  BoundV(0, Term_sort, "x", xref) in 
    Assume(Forall([],
                  [| Term_sort |], 
                  [|(Inr(mkbvd(xident,xident)), xref)|], 
                  (Imp(App(mkTester "BoxBool", Arrow(Term_sort, Bool_sort), [|x|]),
                       Eq(typeOf x, mk_Typ_const (typeNameOfLid Const.bool_lid))))), 
           None, 
           AName "Bool typing")

let stringTyping =
  let xref = termref() in
  let xident = ident("x",dummyRange) in
  let x =  BoundV(0, Term_sort, "x", xref) in 
    Assume(Forall([],
                  [| Term_sort |], 
                  [|(Inr(mkbvd(xident,xident)), xref)|], 
                  (Iff(App(mkTester "BoxString", Arrow(Term_sort, Bool_sort), [|x|]),
                       Eq(typeOf x, mk_Typ_const (typeNameOfLid Const.string_lid))))),
           None, 
           AName "String typing")

let refTyping : op<unit> = 
  let xref = termref() in
  let xident = ident("x",dummyRange) in
  let x =  BoundV(1, Term_sort, "x", xref) in 
  let tref = termref() in
  let tident = ident("t",dummyRange) in
  let t =  BoundV(0, Type_sort, "t", tref) in 
    Assume(Forall([],
                  [| Term_sort; Type_sort |], 
                  [|(Inr(mkbvd(xident,xident)), xref); (Inl(mkbvd(tident,tident)), tref)|], 
                  (Imp(Eq(typeOf x, mk_Typ_app (mk_Typ_const (typeNameOfLid Const.ref_lid)) t), 
                       App(mkTester "BoxRef", Arrow(Term_sort, Bool_sort), [|x|])))),
           None, 
           AName "Ref typing")

let tappKinding = 
  let t1ref = termref() in 
  let t1_id = ident("t1", dummyRange) in
  let t1 = BoundV(1, Type_sort, "t1", t1ref) in 
  let t2ref = termref() in 
  let t2_id = ident("t2", dummyRange) in
  let t2 = BoundV(0, Type_sort, "t2", t2ref) in 
    Assume(Forall([kindOf (mk_Typ_app t1 t2)], 
                  [| Type_sort; Type_sort |], 
                  [| (Inl(mkbvd(t1_id,t1_id)), t1ref); (Inl(mkbvd(t2_id,t2_id)), t2ref) |],
                  (Imp(And(Eq(kindOf t1, mk_Kind_tcon (mk_Kind_star()) (mk_Kind_star())), 
                           Eq(kindOf t2, mk_Kind_star())), 
                       Eq(kindOf (mk_Typ_app t1 t2), mk_Kind_star())))), 
           None, 
           AName "Typ_app kinding")

let pseudoTermInj = 
  let tref = termref() in
  let tident = ident("t",dummyRange) in
  let t =  BoundV(0, Term_sort, "t", tref) in 

  let pref = termref() in
  let pident = ident("p",dummyRange) in
  let p =  BoundV(0, Pseudo_term_sort, "p", pref) in 

  [DeclFun(p2t_name,  [| Pseudo_term_sort |], Term_sort, None);  
   DeclFun(t2p_name,  [| Term_sort |], Pseudo_term_sort, None);  
   Assume(Forall([], 
                 [| Pseudo_term_sort |], 
                 [| (Inl(mkbvd(pident,pident)), pref) |], 
                 Eq(p, t2p(p2t p))),
          None, 
          AName "P2T.T2P"); 
   Assume(Forall([], 
                 [| Term_sort |], 
                 [| (Inl(mkbvd(tident,tident)), tref) |], 
                 Eq(t, p2t(t2p t))),
          None, 
          AName "T2P.P2T")]
                 
let basicOps prelude termctx : list<op> = 
  List.rev
    ([ DefPrelude prelude;
       DeclFun(kOfName,  [| Type_sort |], Kind_sort, None);
       DeclFun(tOfName,  [| Term_sort |], Type_sort, None);
       unitAssumption;
       typeOfV;
       typeOfE;
       typeOfErr;
       boolTyping;
       intTyping;
       stringTyping;
       (* refTyping; *)
       tappKinding]@pseudoTermInj)

let mkTermctx (i:option<string>) (z3:Context) (tns : list<string>) (data:list<string * list<sort>>) : (termctx * list<op>)=
  let mkSym (str:string) = z3.MkSymbol(str) :> Symbol in
  let mkTesterSym str = mkSym <| mkTester str in 
  let pseudoTerm = z3.MkUninterpretedSort (strSort Pseudo_term_sort) :> Sort in 
  let pseudoTermOptConstrs = [z3.MkConstructor(ptnone_name, mkTester ptnone_name, null, null, null);
                              z3.MkConstructor(ptsome_name,  mkTester ptsome_name, [| mkProj ptsome_name 0 |], [| pseudoTerm |], [| 0u |])] in
  let pseudoTermOpt = z3.MkDatatypeSort(strSort Pseudo_term_opt_sort, 
                                        pseudoTermOptConstrs |> Array.ofList) :> Sort in 
  let refSort = z3.MkUninterpretedSort (strSort Ref_sort) :> Sort in 
  let string_constr = [z3.MkConstructor(z3.MkSymbol("String_const") :> Symbol, 
                                        z3.MkSymbol(mkTester "String_const") :> Symbol, 
                                        [| z3.MkSymbol("String_const_proj_0") :> Symbol |], 
                                        [| z3.MkIntSort() :> Sort |], 
                                        [| 0u |])] in 
  let stringSort = z3.MkDatatypeSort (strSort String_sort, Array.ofList string_constr) :> Sort in 
  let smap = mkSortMap z3 in 
  let _ = smap.addSorts [(Int_sort,  z3.MkIntSort() :> Sort); 
                         (Bool_sort, z3.MkBoolSort() :> Sort);
                         (String_sort, stringSort);
                         (Ref_sort, refSort);
                         (Pseudo_term_sort, pseudoTerm);
                         (Pseudo_term_opt_sort, pseudoTermOpt)] in 
  (* kinds are 0u *)
  let kind_constrs = [ z3.MkConstructor("Kind_star", mkTester "Kind_star", null, null, null);
                       z3.MkConstructor("Kind_erasable", mkTester "Kind_erasable", null, null, null);
                       z3.MkConstructor("Kind_affine", mkTester "Kind_affine", null, null, null);
                       z3.MkConstructor("Kind_prop", mkTester "Kind_prop", null, null, null);
                       z3.MkConstructor("Kind_tcon", mkTester "Kind_tcon", [| "Kind_tcon_fst"; "Kind_tcon_snd" |], [| null; null |], [| 0u; 0u |]);
                       z3.MkConstructor("Kind_dcon", mkTester "Kind_dcon", [| "Kind_dcon_fst"; "Kind_dcon_snd" |], [| null; null |], [| 1u; 0u |]);
                     ]  in 
  (* types are 1u *)
  let typename_constrs = tns |> List.map (fun tn -> z3.MkConstructor(tn, 
                                                                     mkTester tn, 
                                                                     null, null, null)) in 
  let typename = z3.MkDatatypeSort("Type_name", typename_constrs |> Array.ofList) :> Sort in 
  let typ_constrs = 
    [ z3.MkConstructor(mkSym "Typ_undef",  mkTesterSym "Typ_undef",  [||],                                                    [| |],                [| |]);
      z3.MkConstructor(mkSym "Typ_other",  mkTesterSym "Typ_other",  Array.map mkSym [| "Typ_other_fst" |],                   [| z3.MkIntSort() :> Sort |], [| 0u |]);
      z3.MkConstructor(mkSym "Typ_btvar",  mkTesterSym "Typ_btvar",  Array.map mkSym [| "Typ_btvar_fst" |],                   [| z3.MkIntSort() :> Sort|], [| 0u |]);
      z3.MkConstructor(mkSym "Typ_const",  mkTesterSym "Typ_const",  Array.map mkSym [| "Typ_const_fst" |],                   [| typename |],       [| 0u |]); 
      z3.MkConstructor(mkSym "Typ_fun",    mkTesterSym "Typ_fun",    Array.map mkSym [| "Typ_fun_fst";    "Typ_fun_snd" |],   [| null; null |],     [| 1u; 1u|]);
      z3.MkConstructor(mkSym "Typ_univ",   mkTesterSym "Typ_univ",   Array.map mkSym [| "Typ_univ_fst";   "Typ_univ_snd" |],  [| null; null |],     [| 0u; 1u|]);
      z3.MkConstructor(mkSym "Typ_dtuple", mkTesterSym "Typ_dtuple", Array.map mkSym [| "Typ_dtuple_fst"; "Typ_dtuple_snd" |],[| null; null |],     [| 1u; 1u|]);
      z3.MkConstructor(mkSym "Typ_refine", mkTesterSym "Typ_refine", Array.map mkSym [| "Typ_refine_fst"; "Typ_refine_snd" |],[| null; null |],     [| 1u; 1u|]);
      z3.MkConstructor(mkSym "Typ_app",    mkTesterSym "Typ_app",    Array.map mkSym [| "Typ_app_fst";    "Typ_app_snd" |],   [| null; null |],     [| 1u; 1u |]);
      z3.MkConstructor(mkSym "Typ_dep",    mkTesterSym "Typ_dep",    Array.map mkSym [| "Typ_dep_fst";    "Typ_dep_snd" |],   [| null; null |],     [| 1u; 2u |]);
      z3.MkConstructor(mkSym "Typ_affine", mkTesterSym "Typ_affine", Array.map mkSym [| "Typ_affine_fst" |],                  [| null |],           [| 1u |]);
      z3.MkConstructor(mkSym "Typ_lam",    mkTesterSym "Typ_lam",    Array.map mkSym [| "Typ_lam_fst";    "Typ_lam_snd" |],   [| null; null |],     [| 1u; 1u|]);
      z3.MkConstructor(mkSym "Typ_tlam",   mkTesterSym "Typ_tlam",   Array.map mkSym [| "Typ_tlam_fst";   "Typ_tlam_snd" |],  [| null; null |],     [| 0u; 1u|]);
    ] in 

  (* Terms are 2u *)
  let others = [z3.MkConstructor(mkSym "Term_undef", mkTesterSym "Term_undef", [| |], [| |], [| |]);
                z3.MkConstructor(mkSym "Term_other", mkTesterSym "Term_other", Array.map mkSym [| "Term_other_proj_0"  |], [| z3.MkIntSort() :> Sort |], [| 0u |]);
                z3.MkConstructor(mkSym "Exp_bvar", mkTesterSym "Exp_bvar", Array.map mkSym [| "Exp_bvar_proj_0"  |], [| z3.MkIntSort() :> Sort |], [| 0u |]);
                z3.MkConstructor(mkSym "BoxInt", mkTesterSym "BoxInt", Array.map mkSym [| "BoxInt_proj_0"  |], [| z3.MkIntSort() :> Sort|], [| 0u |]);
                z3.MkConstructor(mkSym "BoxBool", mkTesterSym "BoxBool", Array.map mkSym [| "BoxBool_proj_0"  |], [| z3.MkBoolSort() :> Sort|], [| 0u |]);
                z3.MkConstructor(mkSym "BoxString", mkTesterSym "BoxString", Array.map mkSym [| "BoxString_proj_0"  |], [| stringSort |], [| 0u |]);
                z3.MkConstructor(mkSym "BoxRef", mkTesterSym "BoxRef", Array.map mkSym [| "BoxRef_proj_0"  |], [| refSort |], [| 0u |])] in
  let termcons = data |> List.map (fun (nm, argsorts) -> 
                                     let arity = List.length argsorts in 
                                     z3.MkConstructor(mkSym nm, 
                                                      mkTesterSym nm,
                                                      Array.ofList <| (Util.list0N (arity - 1) |> List.map (fun i -> mkSym (mkProj nm i))), 
                                                      Array.ofList <| (argsorts |> List.map (function 
                                                                                               | Type_sort 
                                                                                               | Term_sort -> null
                                                                                               | s -> smap.sortToZ3Sort s)),
                                                      Array.ofList <| (argsorts |> List.map (function 
                                                                                               | Type_sort -> 1u 
                                                                                               | Term_sort -> 2u
                                                                                               | s -> 0u)))) in 
  let term_constrs = others@termcons in 
  let termcons_prelude = data |> List.map (fun (nm, argsorts) -> 
                                             let arity = List.length argsorts in 
                                             let args = List.zip  argsorts in 
                                               spr "(%s %s)" nm
                                                 (String.concat "\n"
                                                    (List.map2  (fun i s -> spr "(%s %s)" (mkProj nm i) (strSort s))
                                                       (Util.list0N (arity - 1)) argsorts))) in
  let termcons_prelude = String.concat "\n\t" termcons_prelude in
  let absyn = z3.MkDatatypeSorts([| "Kind"; "Type"; "Term" |], [| Array.ofList kind_constrs; 
                                                                 Array.ofList typ_constrs;
                                                                 Array.ofList term_constrs |]) in 
  let kind, typ, term = absyn.(0), absyn.(1), absyn.(2) in 
  let _ = smap.addSorts [(Kind_sort, kind :> Sort); 
                         (Type_sort, typ :> Sort); 
                         (Term_sort, term :> Sort)] in
  let fds = mkFuncdecls z3 (pseudoTermOptConstrs@string_constr@typename_constrs@kind_constrs@typ_constrs@term_constrs) in 
  let fmap = mkFunSymMap () in 
  let _ = fmap.addFunSyms fds in 
  let termctx = {funSymMap=fmap;
                 sortMap=smap; 
                 z3ctx=z3;
                 z3solver=z3.MkSolver();
                 stream=(match i with None -> None | Some i -> Some (openStream i));
                 id=i} in 
  let prelude = mkPrelude (String.concat "\n\t" (List.map (spr "(%s)") tns)) termcons_prelude in
    termctx, basicOps prelude termctx  
      
(* ******************************************************************************** *)
(* Type normalization *)
(* ******************************************************************************** *)

let normalizeTyp tcenv t : typ = 
  let rebuild subst t args = 
    let t = List.fold_left (fun t arg -> match arg with 
                              | Inl(t2,k,p) -> twithinfo (Typ_app(t,t2)) k p
                              | Inr(e2,k,p) -> twithinfo (Typ_dep(t,e2)) k p) t args in 
      t, ([], subst) in 
  let applyVSubst s x = 
    let x = bvar_to_bvd x in 
      findOpt (function Inl _ -> false | Inr (y, _) -> bvd_eq x y) s in
  let applyTSubst s x = 
    let x = bvar_to_bvd x in 
      findOpt (function Inl (y, _) -> bvd_eq x y | Inr _ -> false) s in
  let rec rt rk vt re (args, subst) binders t =
    let rt env t = rt rk vt re env binders t in 
    (* let k, _ = rk ([],subst) t.sort in  *)
    let k = t.sort in 
    let t = setsort t k in 
    let t = compress t in 
      match t.v with 
        | Typ_const(fv, eref) -> 
            (match Tcenv.lookup_typ_abbrev tcenv fv with 
               | None -> rebuild subst t args
               | Some t -> rt (args, subst) t)
              
        | Typ_btvar bv -> 
            (match applyTSubst subst bv with 
               | None -> rebuild subst t args
               | Some (Inl(_, t)) -> rt (args, subst) t
               | _ -> raise Impos)
              
        | Typ_app(t1,t2) -> 
            let t2, _ = rt ([],subst) t2 in 
              rt ((Inl(t2,t.sort,t.p))::args, subst) t1
                
        | Typ_dep(t1,e2) -> 
            let e2, _ = re ([],subst) binders e2 in 
              rt (Inr(e2,t.sort,t.p)::args, subst) t1 
                
        | Typ_lam(x,t1,body) -> 
            (match args with 
               | [] -> 
                   let t1, _ = rt ([], subst) t1 in 
                   let body, _ = rt ([], subst) body in 
                     twithinfo (Typ_lam(x, t1, body)) t.sort t.p, ([], subst)
               | (Inr(actual,_,_))::rest -> 
                   (* let _ = pr "Binding argument %s to actual parameter %s\n" (string_of_bvd x) (actual.ToString()) in *)
                   let t, _ = rt (rest, (Inr(x, actual)::subst)) body in 
                     t, ([], subst)
               | _ -> raise Impos)
              
        | Typ_tlam(a,k,body) -> 
            (match args with 
               | [] -> 
                   let k, _ = rk ([],subst) binders k in 
                   let body, _ = rt ([], subst) body in 
                     twithinfo (Typ_tlam(a, k, body)) t.sort t.p, ([], subst)
               | (Inl(actual,_,_))::rest -> 
                   (* let _ = pr "Binding argument %s to actual parameter %s\n" (string_of_bvd a) (actual.ToString()) in *)
                   let t, _ = rt (rest, (Inl(a, actual)::subst)) body in 
                     t, ([], subst)
               | (Inr(actual,_,_))::_ -> 
                   pr "Found type %s; \nexpected type app, got type dep %s\n"
                     (t.ToString()) (actual.ToString());
                   raise Impos)
              
        | Typ_ascribed(t, _) ->  rt (args, subst) t

        | _  ->  (* none of the remaining cases can reduce *) 
            let t, _ = vt ([], subst) binders t in 
              rebuild subst t args in 
  let rec re rk rt ve (_,subst) binders e =
    let re = re rk rt ve ([],subst) binders in 
    (* let t, _ = rt ([],subst) e.sort in  *)
    let t = e.sort in
    let e = setsort e t in 
      match e.v with 
        | Exp_bvar bv -> 
            (match applyVSubst subst bv with 
               | None -> e, ([], subst)
               | Some(Inr(_, e)) -> re e
               | _ -> raise Impos)
        | _ -> ve ([],subst) binders e in 
 fst <| AbsynUtils.reduce_typ 
      (fun rk rt re subst binders k -> rk subst binders k)
      rt re
      AbsynUtils.combine_kind
      AbsynUtils.combine_typ
      AbsynUtils.combine_exp
      ([],[]) [] t
      
(* ******************************************************************************** *)
(* Alpha conversion ... fast *)
(* ******************************************************************************** *)
(* type subst = (list<btvdef*typ> * list<bvvdef*exp>) *)
(* type env = subst * bool *)
(* let isalpha = false *)

(* let rec rt<'a> (subst:subst) (t:typ) (cont:typ -> 'a) : 'a = *)
(*   let (tsubst, vsubst) = subst in *)
(*   let cont' (s:typ') : 'a = cont (twithinfo s t.sort t.p) in  *)
(*   let t = compress t in *)
(*     match t.v with *)
(*       | Typ_btvar x -> *)
(*           cont (match applySubst tsubst x with *)
(*                   | Some (_, y) -> y *)
(*                   | _ -> t) *)

(*       | Typ_meta (Meta_cases tl) -> *)
(*           rtspar subst tl  *)
(*             (fun tl -> cont' (Typ_meta(Meta_cases tl))) *)

(*       (\* | _ -> pr "Unexpected %s" (t.ToString()); raise Impos *\) *)

(* and rtspar<'a> (subst:subst) (ts:typ list) (cont: typ list -> 'a) : 'a =  *)
(*   (ts *)
(*   |> List.map (fun t ->  *)
(*                 async { *)
(*                   return (rt<typ> subst t (fun t -> t)) *)
(*                 }) *)
(*   |> Seq.ofList *)
(*   |> Async.Parallel *)
(*   |> Async.RunSynchronously *)
(*   |> List.ofArray  *)
(*   |> cont) *)

let sprFvs fvs = 
  spr "Free variables are: [%s], %s\n" 
    (String.concat "; " (List.map (fun tv -> Pretty.strBvd tv.v) (fst fvs)))
    (String.concat "; " (List.map (fun tv -> Pretty.strBvd tv.v) (snd fvs)))

let exists_sub_term (p : typ -> bool) t : bool = 
  let r = snd <| AbsynUtils.reduce_typ 
      (fun vk rt re -> vk)
      (fun rk vt re env binders t -> 
         if p t then (),1
         else vt env binders t)
      (fun rk rt ve -> ve)
      (fun _ _ e -> ((),e))
      (fun t _ e -> if e > 0 then pr "Pred found(%d): %s\n" e (Pretty.strTyp t); ((), if e > 0 then e+1 else e))
      (fun _ _ e -> ((),e))
      0 [] t in 
    r > 0

(* let remove_tvar ((tsubst, vsubst), isalpha) a =  *)
(*   let tsubst = List.filter (fun (x, _) -> not (bvd_eq x a)) tsubst in  *)
(*     ((tsubst, vsubst), isalpha) *)
      
(* let remove_xvar ((tsubst, vsubst), isalpha) a =  *)
(*   let vsubst = List.filter (fun (x, _) -> not (bvd_eq x a)) vsubst in  *)
(*     ((tsubst, vsubst), isalpha) *)

(* let rec rt<'a> ((subst:subst, isalpha:bool) as env) (t:typ) (cont:typ -> 'a) : 'a = *)
(*   let (tsubst, vsubst) = subst in *)
(*   let cont' (s:typ') : 'a = cont (twithinfo s t.sort t.p) in *)
(*   let alpha x t1 t2 cont = *)
(*     rt env t1 *)
(*       (fun t1 -> *)
(*          let newname = genident None in *)
(*          let y = mkbvd (newname, newname) in *)
(*          let vsubst = (x,ewithsort (Exp_bvar (bvd_to_bvar_s y t1)) t1)::vsubst in *)
(*            rt ((tsubst,vsubst), isalpha) t2 *)
(*              (fun t2 -> *)
(*                 cont y t1 t2)) in  *)
(*   let alpha_k a k t cont =  *)
(*     rk env k *)
(*       (fun k -> *)
(*          let newname = genident None in *)
(*          let b = mkbvd (newname, newname) in *)
(*          let tsubst = (a,twithsort (Typ_btvar (bvd_to_bvar_s b k)) k)::tsubst in *)
(*            rt ((tsubst,vsubst),isalpha) t *)
(*              (fun t -> cont b k t)) in *)
(*   let t0 = t in  *)
(*   (\* let _ = pr "Before compression: %s\n" (Pretty.strTyp t0) in  *\) *)
(*   (\*   if exists_sub_term (fun t -> match t.v with Typ_tlam(a, _, _) when (Pretty.strBvd a = "x_245") -> pr "Pred found(0): %s\n" (Pretty.strTyp t); true | _ -> false) t0 *\) *)
(*   (\*   then raise Impos; *\) *)
(*   let t = compress t in *)
(*   (\* let _ =  *\) *)
(*   (\*   let fvs = freevarsTyp t in  *\) *)
(*   (\*     if List.exists (fun x -> Pretty.strBvd x.v = "x_245") (fst fvs) *\) *)
(*     (\*     then (pr "Compressed type %s\n with fvs=%s\n" (Pretty.strTyp t) (sprFvs fvs); raise Impos) in  *\) *)
(*     match t.v with *)
(*       | Typ_btvar x -> *)
(*           (match applySubst tsubst x with *)
(*              | Some (_, y) -> rt env y cont *)
(*              | _ -> cont t) *)
            
(*       | Typ_lam(x,t1,body) -> *)
(*           if isalpha then *)
(*             alpha x t1 body (fun y t1 body -> cont' (Typ_lam(y, t1, body))) *)
(*           else *)
(*             rts env [(Some x, t1);(None, body)] *)
(*               (fun [t1;body] -> cont' (Typ_lam(x,t1,body))) *)
            
(*       | Typ_fun (nopt, t1, t2) -> *)
(*           (match nopt with  *)
(*              | Some x when isalpha ->  *)
(*                  alpha x t1 t2 (fun x t1 t2 -> cont' (Typ_fun(Some x, t1, t2))) *)
(*              | _ ->  *)
(*                  rts env [(nopt,t1);(None,t2)] *)
(*                    (fun [t1;t2] -> cont' (Typ_fun(nopt, t1, t2)))) *)
            
(*       | Typ_dtuple([(nopt,t1);(_,t2)]) -> *)
(*           (match nopt with  *)
(*              | Some n when isalpha ->  *)
(*                  alpha n t1 t2 (fun n t1 t2 -> cont' (Typ_dtuple([(Some n,t1);(None,t2)]))) *)
(*              | _ ->  *)
(*                  rts env [(nopt,t1);(None,t2)] *)
(*                    (fun [t1;t2] -> cont' (Typ_dtuple([(nopt,t1);(None,t2)])))) *)
            
(*       | Typ_refine (bvd, t, form, b) -> *)
(*           if isalpha then  *)
(*             alpha bvd t form (fun bvd t form -> cont' (Typ_refine (bvd, t, form, b))) *)
(*           else *)
(*             rts env [(Some bvd, t);(None, form)] (fun [t;form] -> cont' (Typ_refine (bvd, t, form, b))) *)
              
(*       | Typ_tlam(a,k,body) -> *)
(*           if isalpha then *)
(*             alpha_k a k body (fun b k body -> cont' (Typ_tlam(b, k, body))) *)
(*           else *)
(*             (rk env k *)
(*                (fun k -> *)
(*                   let env = remove_tvar env a in  *)
(*                     rt env body (fun body -> cont' (Typ_tlam(a,k,body))))) *)
              
(*       | Typ_univ(bvd, k, [], t) -> *)
(*           if isalpha then  *)
(*             alpha_k bvd k t (fun bvd k t -> cont' (Typ_univ(bvd,k,[],t))) *)
(*           else *)
(*             rk env k *)
(*               (fun k -> *)
(*                  let env = remove_tvar env bvd in  *)
(*                    rt env t (fun t -> cont' (Typ_univ(bvd,k,[],t)))) *)

(*       | Typ_uvar _ *)
(*       | Typ_const _ *)
(*       | Typ_unknown -> cont t *)
(*       | Typ_record(fnt_l, topt) -> *)
(*           let fnl, t_l = List.unzip fnt_l in *)
(*             rts env (List.map (fun t -> (None, t)) t_l) *)
(*               (fun tl -> *)
(*                  let fnt_l = List.zip fnl t_l in *)
(*                    match topt with *)
(*                      | None -> cont' (Typ_record(fnt_l, None)) *)
(*                      | Some s -> *)
(*                          rt env s *)
(*                            (fun s -> *)
(*                               cont (twithinfo (Typ_record(fnt_l, Some s)) t.sort t.p))) *)

(*       | Typ_app(t1,t2) -> *)
(*           rts env [(None, t1); (None, t2)] *)
(*             (fun [t1;t2] -> cont' (Typ_app(t1,t2))) *)

(*       | Typ_dep (t, e) -> *)
(*           rt env t *)
(*             (fun t -> *)
(*                re env e (fun e -> *)
(*                              cont' (Typ_dep(t,e)))) *)

(*       | Typ_affine t -> *)
(*           rt env t (fun t -> cont' (Typ_affine(t))) *)
            
(*       | Typ_ascribed(t, k) -> *)
(*           rt env t cont *)
            
(*       | Typ_meta (Meta_cases tl) -> *)
(*           rtspar env tl *)
(*             (fun tl -> cont' (Typ_meta(Meta_cases tl))) *)
            
(*       | Typ_meta (Meta_tid i) -> *)
(*           cont t *)

(*       | Typ_meta (Meta_named(s,t)) -> *)
(*           rt env t (fun t -> cont' (Typ_meta(Meta_named(s,t)))) *)
            
(*       | Typ_meta (Meta_alpha t) -> *)
(*           rt env t (fun t -> cont' (Typ_meta (Meta_alpha t))) *)

(*       | _ -> pr "Unexpected %s" (t.ToString()); raise Impos *)

(* and rtspar<'a> (env:env) (ts:typ list) (cont: typ list -> 'a) : 'a = *)
(*   (Seq.ofList ts *)
(*   |> Seq.map (fun t -> *)
(*                 async { *)
(*                   return (rt<typ> env t (fun t -> t)) *)
(*                 }) *)
(*   |> Async.Parallel *)
(*   |> Async.RunSynchronously *)
(*   |> List.ofArray *)
(*   |> cont) *)

(* (\* and rts_maybe_par<'a> (env:env) (t1:typ) (t2:typ) (cont: typ -> typ -> 'a) : 'a = *\) *)
(* (\*   let t2 = compress t2 in *\) *)
(* (\*     match t2.sort.u with  *\) *)
(* (\*       | Kind_dcon(_, _, {u=Kind_dcon(_, _, _)}) ->  *\) *)
(* (\*           (match t2.v with *\) *)
(* (\*              | Typ_btvar _ *\) *)
(* (\*              | Typ_const _ -> rts env [t1;t2] (fun [t1;t2] -> cont t1 t2) *\) *)
(* (\*              | _ -> rtspar env [t1;t2] (fun [t1;t2] -> cont t1 t2)) *\) *)
(* (\*       | _ -> rts env [t1;t2] (fun [t1;t2] -> cont t1 t2) *\) *)
          
(* and rts<'a> (env:env) (ts:(option<bvvdef> * typ) list) (cont: typ list -> 'a) : 'a =  *)
(*   match ts with *)
(*     | [] -> cont [] *)
(*     | (xopt,t)::tl -> rt env t (fun t ->  *)
(*                                   let env = match xopt with  *)
(*                                     | None -> env *)
(*                                     | Some x -> remove_xvar env x in  *)
(*                                     rts env tl (fun tl -> cont (t::tl))) *)
      
(* and re<'a> ((subst, _) as env:env) (e:exp) (cont:exp -> 'a) : 'a = *)
(*   let cont' f = cont (ewithinfo f e.sort e.p) in *)
(*     match e.v with *)
(*       | Exp_bvar x -> *)
(*           (match applySubst (snd subst) x with *)
(*              | Some (_, y) -> re env y cont *)
(*              | _ -> cont e) *)
            
(*       | Exp_bot *)
(*       | Exp_fvar _ *)
(*       | Exp_constant _ -> cont e *)

(*       | Exp_constr_app (v, tl, [], el) ->  *)
(*           rts env (List.map (fun t -> None, t) tl) *)
(*             (fun tl -> *)
(*                res env el *)
(*                  (fun el -> *)
(*                     cont' (Exp_constr_app(v, tl, [], el)))) *)

(*       | Exp_primop(op, el) -> *)
(*           res env el (fun el -> cont' (Exp_primop(op,el))) *)
            
(*       | Exp_abs (bvd, t, e) -> *)
(*           rt env t *)
(*             (fun t -> *)
(*                re (remove_xvar env bvd) e *)
(*                  (fun e -> cont' (Exp_abs(bvd, t, e)))) *)
            
(*       | Exp_tabs(bvd, k, [], e) -> *)
(*           rk env k *)
(*             (fun k -> *)
(*                let env = remove_tvar env bvd in  *)
(*                  re env e *)
(*                    (fun e -> *)
(*                       cont' (Exp_tabs(bvd, k, [], e)))) *)
            
(*       | Exp_app (e1, e2) -> *)
(*           res env [e1;e2] *)
(*             (fun [e1;e2] -> cont' (Exp_app(e1,e2))) *)
            
(*       | Exp_tapp (e, t) -> *)
(*           re env e *)
(*             (fun e -> *)
(*                rt env t *)
(*                  (fun t -> cont' (Exp_tapp(e,t)))) *)
            
(*       | Exp_match(e, eqns, def) -> *)
(*           re env e *)
(*             (fun e -> *)
(*                let pats, branches = List.unzip eqns in *)
(*                let env = List.fold_left (fun env (Pat_variant(_, tvs, _, xvs, _)) -> *)
(*                                            let env = List.fold_left (fun env t -> match t.v with Typ_btvar a -> remove_tvar env a.v | _ -> env) env tvs in  *)
(*                                              List.fold_left (fun env x -> remove_xvar env x.v) env xvs) env pats in  *)
(*                  respar env branches *)
(*                    (fun branches -> *)
(*                       re env def *)
(*                         (fun def -> *)
(*                            cont' (Exp_match(e, List.zip pats branches, def))))) *)
            
            
(*       | Exp_cond (e1, e2, e3) -> *)
(*           respar env [e1;e2;e3] *)
(*             (fun [e1;e2;e3] -> cont' (Exp_cond(e1, e2, e3))) *)
            
(*       | Exp_recd (lidopt, tl, [], fn_e_l) -> *)
(*           rts env (List.map (fun t -> None, t) tl) *)
(*             (fun tl -> *)
(*                let fn, el = List.unzip fn_e_l in *)
(*                  res env el (fun el -> cont' (Exp_recd(lidopt, tl, [], List.zip fn el)))) *)
            
(*       | Exp_proj (e, fn) -> *)
(*           re env e (fun e -> cont' (Exp_proj(e, fn))) *)
            
(*       | Exp_ascribed (e,t,ev) -> *)
(*           re env e cont *)

(*       | Exp_let (b, bvd_t_e_l, e) -> *)
(*           let xs,tl,el = List.unzip3 bvd_t_e_l in *)
(*             rts env (List.map (fun t -> None, t) tl) *)
(*               (fun tl -> *)
(*                  let env = List.fold_left remove_xvar env xs in  *)
(*                  res env el *)
(*                    (fun el -> *)
(*                       re env e (fun e -> cont' (Exp_let(b, List.zip3 xs tl el, e))))) *)
              
(*       | Exp_gvar _ -> raise Impos *)
          
(*       | Exp_extern_call(eref, id, t, tl, el) -> *)
(*           rts env (List.map (fun t -> None, t) (t::tl)) *)
(*             (fun (t::tl) -> *)
(*                res env el *)
(*                  (fun el -> cont' (Exp_extern_call(eref, id, t, tl, el)))) *)
            
(*       | e -> failwith (spr "Unhandled case %A:" e) *)

(* and respar<'a> (env:env) (es:exp list) (cont: exp list -> 'a) : 'a =  *)
(*   (Seq.ofList es *)
(*   |> Seq.map (fun e -> *)
(*                 async { *)
(*                   return (re<exp> env e (fun e -> e)) *)
(*                 }) *)
(*   |> Async.Parallel *)
(*   |> Async.RunSynchronously *)
(*   |> List.ofArray *)
(*   |> cont) *)
  
(* and res<'a> (env:env) (es:exp list) (cont: exp list -> 'a) : 'a =  *)
(*   match es with *)
(*     | [] -> cont [] *)
(*     | e::el -> re env e (fun e -> res env el (fun el -> cont (e::el))) *)
        
(* and rk<'a> (((tsubst,vsubst), isalpha) as env:env) (k:kind) (cont:kind -> 'a) : 'a = *)
(*   let alpha x t k cont = *)
(*     rt env t *)
(*       (fun t -> *)
(*          let newname = genident None in *)
(*          let y = mkbvd (newname, newname) in *)
(*          let vsubst = (x,ewithsort (Exp_bvar (bvd_to_bvar_s y t)) t)::vsubst in *)
(*            rk ((tsubst,vsubst), isalpha) k *)
(*              (fun k -> *)
(*                 cont y t k)) in  *)
(*   let alpha_k a k1 k2 cont =  *)
(*     rk env k1 *)
(*       (fun k1 -> *)
(*          let newname = genident None in *)
(*          let b = mkbvd (newname, newname) in *)
(*          let tsubst = (a,twithsort (Typ_btvar (bvd_to_bvar_s b k)) k)::tsubst in *)
(*            rk ((tsubst,vsubst), isalpha) k2 *)
(*              (fun k2 -> cont b k1 k2)) in *)
(*   let cont' l :'a = cont (withhash l) in *)
(*     match k(\* .u *\)with *)
(*       | Kind_boxed k -> rk env k cont *)
(*       | Kind_star *)
(*       | Kind_affine *)
(*       | Kind_prop *)
(*       | Kind_erasable *)
(*       | Kind_unknown -> cont k *)
(*       | Kind_tcon (aopt, k1, k2) -> *)
(*           (match aopt with  *)
(*              | Some a when isalpha ->  *)
(*                  alpha_k a k1 k2 (fun b k1 k2 -> cont' (Kind_tcon(Some b, k1, k2))) *)
(*              | _ ->  *)
(*                  rk<'a> env k1 *)
(*                    (fun k1 -> *)
(*                       let env = match aopt with  *)
(*                         | None -> env *)
(*                         | Some a -> remove_tvar env a in  *)
(*                       rk<'a> env k2 (fun k2 -> cont' (Kind_tcon(aopt, k1, k2))))) *)
(*       | Kind_dcon (xopt, t, k) -> *)
(*           (match xopt with  *)
(*              | Some x when isalpha ->  *)
(*                  alpha x t k (fun y t k -> cont' (Kind_dcon(Some y, t, k))) *)
(*              | _ ->  *)
(*                  let env = match xopt with  *)
(*                    | None -> env *)
(*                    | Some x -> remove_tvar env x in  *)
(*                    rt<'a> env t *)
(*                      (fun t -> *)
(*                         rk<'a> env k (fun k -> cont' (Kind_dcon(xopt, t, k))))) *)
            
            
(* let alpha_fast t = rt (([],[]),true) t (fun t -> t) *)
(* let subst_fast substs t =  *)
(*   (\* let _ = List.iter (fun (x,t) -> pr "['%s -> %s]\n" (Pretty.strBvd x) (Pretty.strTyp t)) (fst substs) in  *\) *)
(*   (\* let _ = List.iter (fun (x,e) -> pr "[%s -> %s]\n" (Pretty.strBvd x) (Pretty.strExp e)) (snd substs) in  *\) *)
(*   (\* let fvs = freevarsTyp t in  *\) *)
(*   (\*   pr "%s\n" (sprFvs fvs); *\) *)
(*     (\* substitute_l_typ_or_exp t ((List.map Inl (fst substs))@(List.map Inr (snd substs))) *\) *)
(*     rt (substs,false) t (fun t -> t) *)
(*       (\* let subst_fast substs t = rt (substs,false) t (fun t -> t) *\) *)


