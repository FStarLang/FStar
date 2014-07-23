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
 
module Microsoft.FStar.Z3Encoding.DecodeTyp

open Microsoft.FStar
open Z3Encoding.Env
open Z3Encoding.BasicDT
open Microsoft.Z3
open Util
open Absyn
open Term
open Profiling 
open KindAbbrevs


type goals = list<tm>
type qnames     = list<string> 
type qvars      = list<tm>
type qsorts     = list<sort>

let takeUntil f = 
  let rec aux out = function 
    | [] -> List.rev out, []
    | hd::tl when f hd -> List.rev out, (hd::tl)
    | hd::tl -> aux (hd::out) tl in 
    aux [] 

let rec sortsFromTyp t = match t.v with 
  | Typ_univ(_, _, _, t) -> Type_sort::(sortsFromTyp t)
  | Typ_fun(_, _, t) -> Term_sort::(sortsFromTyp t)
  | _ -> [] 

let rec sortMapFromTyp t = match t.v with 
  | Typ_univ(a, k, _, t) -> (Inl(a,k), Type_sort)::(sortMapFromTyp t)
  | Typ_fun(x, t0, t) -> (Inr(x,t0), Term_sort)::(sortMapFromTyp t)
  | _ -> [] 


let addOp op : ST<unit>   = upd (fun s -> {s with st={s.st with ops=(normalizeOp op)::s.st.ops}})
let addOps ops : ST<unit> = upd (fun s -> {s with st={s.st with ops=(List.map normalizeOp ops)@s.st.ops}})
let addQops ops : ST<unit> = upd (fun s -> {s with st={s.st with qops=(List.map normalizeOp ops)@s.st.qops}})
let addPPName (k,v) (h:opState) : STR<unit> = 
  let s, h = get h in 
    Hashtbl.add s.st.pp_name_map k v; 
    (), h
let addUnfolding uf : ST<unit> = upd (fun s -> {s with st={s.st with unfoldings=uf::s.st.unfoldings}})
let internUvar uvar_k term ops : ST<unit> = 
  let ops = List.map normalizeOp ops in
  upd (fun s -> {s with st={s.st with uvars=(uvar_k,term,ops)::s.st.uvars}})
let internString bytes term ops : ST<unit> =
  let ops = List.map normalizeOp ops in
    upd (fun s -> {s with st={s.st with strings=(bytes,term,ops)::s.st.strings}})
let internFloat f term ops : ST<unit> = 
  let ops = List.map normalizeOp ops in
    upd (fun s -> {s with st={s.st with floats=(f,term,ops)::s.st.floats}})
let internBvar bv term ops : ST<unit> = 
  let ops = List.map normalizeOp ops in
    upd (fun s -> {s with st={s.st with bvars=(bv,term,ops)::s.st.bvars}})
let internFvar fv term ops : ST<unit> = 
  let ops = List.map normalizeOp ops in
    upd (fun s -> {s with st={s.st with fvars=(fv,term,ops)::s.st.fvars}})
let internTransformer str typ term phiopt : ST<unit> = 
  (* let _ = if !Options.silent then () else pr "Interning type %s at term %A\n" (typ.ToString()) term in  *)
    upd (fun s -> 
           let tx, rev = s.st.transformers in 
           let rev = match term.tm with 
             | App("Typ_other", _, [| {tm=Integer i} |]) -> 
                 map_add rev i (typ, phiopt)
             | _ -> raise Impos in 
           let hkt = AbsynUtils.hashkey_typ typ in 
           let hkk = AbsynUtils.hashkey_kind typ.sort in 
           let tx = match map_tryfind tx hkt with
             | None -> 
                 let ktable = map_create 17 in
                 let ktable = map_add ktable hkk [typ,term,phiopt] in 
                   map_add tx hkt ktable
             | Some ktable -> 
                 match map_tryfind ktable hkk with
                   | None -> map_replace tx hkt (map_add ktable hkk [typ,term,phiopt])
                   | Some l -> map_replace tx hkt (map_replace ktable hkk ((typ,term,phiopt)::l)) in 
             {s with st={s.st with transformers=(tx,rev)}})
      (* {s with transformers=(str,typ,term,phiopt)::s.transformers}) *)
let gammaLid = [ident("GAMMA", 0L)]
let incrCtr h : STR<int> = 
  let s, h = get h in 
  let _, h = put {s with st={s.st with ctr=s.st.ctr + 1}} h in 
    s.st.ctr, h

type env = (list<Disj<(bvvdef*typ),(btvdef*kind)>> * opState)
let get_tcenv (_, opstate) = match opstate.st.env with 
    | None -> raise Impos
    | Some tcenv -> tcenv
let push_typ (e1, e2) x t = (Inl(x, t))::e1, e2
let push_kind (e1, e2) x k = (Inr(x, k))::e1, e2
let lookup (e, _) ix = 
  if ix >= List.length e 
  then failwith "decoding failed: index out of bounds"
  else List.nth e ix
let lookup_bvar_ix e ix = 
  match lookup e ix with 
    | Inl(x, t) -> Absyn.bvd_to_bvar_s x t
    | _ -> failwith "decoding failed: expected type, got kind"
let lookup_btvar_ix e ix = 
  match lookup e ix with 
    | Inr(x, k) -> Absyn.bvd_to_bvar_s x k
    | _ -> failwith "decoding failed: expected kind, got type"
let lookup_lid e lid = Tcenv.lookup_lid (get_tcenv e) lid
let lookup_bvar e bv = Tcenv.lookup_bvar (get_tcenv e) bv
let lookup_typ_lid e lid = Tcenv.lookup_typ_lid (get_tcenv e) lid

let decodeConstant (_, opState) i = 
   let findExp l f = 
     match findOpt (fun (_, t, _) -> match t.tm with 
                      | App("Term_other", _, [| {tm=Integer j} |]) when i=j -> true
                      | _ -> false)  l with 
       | Some (v, _, _) -> Some (f v)
       | None -> None in 
   let res = any  [(fun () -> findExp opState.st.strings (fun str -> ewithsort (Exp_constant (Sugar.Const_string(str, dummyRange))) Const.string_typ));
                   (fun () -> findExp opState.st.floats (fun f -> ewithsort (Exp_constant(Sugar.Const_float f)) Const.float_typ));
                   (fun () -> findExp opState.st.bvars (fun bv -> ewithsort (Exp_bvar(bv)) bv.sort));
                   (fun () -> findExp opState.st.fvars (fun fv -> ewithsort (Exp_fvar(fv, None)) fv.sort));] in
     match res with 
       | None -> raise (Err(spr "Unable to decode constant %A\n" i))
       | Some e -> e

let decodeTypConstant (_, opState) i = 
  let _, rev = opState.st.transformers in 
    match map_tryfind rev i with 
      | None -> raise (Err(spr "Unable to decode type constant %A\n" i))
      | Some x -> x
       
let decodeConstantVar (_, opState) i = 
   let findIn l = 
     findOpt (fun (_, t, _) -> match t.tm with 
                | FreeV(nm, _) -> nm=i
                | _ -> false)  l in
     match findIn opState.st.strings with 
       | Some (str, _, _) -> ewithsort (Exp_constant (Sugar.Const_string(str, dummyRange))) Const.string_typ
       | _ -> raise (Err("Unable to decode constant"))

exception Decoding_failure of (int * Expr)
let decodeTransformer {z3ctx=z3ctx; sortMap=sortMap} env (tm:Expr) : (typ * phi) = 
  if not (tm.Sort.Equals(sortMap.sortToZ3Sort Type_sort))
  then raise (Err("Unexpected sort in decodeTransformer"));
  let args : Expr [] = tm.Args in 
    match tm.FuncDecl.Name.ToString() with
      | "Typ_other" -> 
          let ix = (args.(0) :?> IntNum).Int in 
          let typ, phiopt = decodeTypConstant env ix in 
            (match phiopt with 
               | None -> raise (Decoding_failure(1,tm))
               | Some phi -> typ, phi)
      | "Typ_undef" -> raise (Decoding_failure(2,tm))
          
           
let rec decodeTyp ({z3ctx=z3ctx;sortMap=sortMap} as tctx) env (tm:Expr) : typ = 
  if not (tm.Sort.Equals(sortMap.sortToZ3Sort Type_sort))
  then raise (Err("Unexpected sort in decodeTyp"));
  let args = tm.Args in 
    match tm.FuncDecl.Name.ToString() with
      | "Typ_undef" -> raise (Decoding_failure(3, tm))
      | "Typ_other" -> 
          let ix = (args.(0) :?> IntNum).Int in
            fst (decodeTypConstant env ix)
      | "Typ_btvar" -> 
          let ix = (args.(0) :?> IntNum).Int in
          let bv = lookup_btvar_ix env ix in 
            twithsort (Typ_btvar(bv)) bv.sort
      | "Typ_const" -> 
          let tc = decodeTypeName z3ctx env (tm.Args.(0)) in 
            twithsort (Typ_const(tc,None)) tc.sort
      | "Typ_fun" -> 
          let t1 = decodeTyp tctx env (args.(0)) in 
          let x = Absyn.new_bvd None in 
            twithsort (Typ_fun(Some x, t1, decodeTyp tctx (push_typ env x t1) (args.(1)))) Kind_star
      | "Typ_dtuple" -> 
          let t1 = decodeTyp tctx env (args.(0)) in 
          let x = Absyn.new_bvd None in 
            twithsort (Typ_dtuple([(Some x, t1);(None, decodeTyp tctx (push_typ env x t1) (args.(1)))])) Kind_star
      | "Typ_refine" -> 
          let t1 = decodeTyp tctx env (args.(0)) in 
          let x = Absyn.new_bvd None in 
            twithsort (Typ_refine(x, t1, decodeTyp tctx (push_typ env x t1) (args.(1)), true)) Kind_star
      | "Typ_univ" ->
          let k = decodeKind tctx env (args.(0)) in 
          let x = Absyn.new_bvd None in 
            twithsort (Typ_univ(x, k, [], decodeTyp tctx (push_kind env x k) (args.(1)))) Kind_star
      | "Typ_app" -> 
          let t1 = decodeTyp tctx env (args.(0)) in 
          let t2 = decodeTyp tctx env (args.(1)) in 
            twithsort (Typ_app(t1, t2)) (open_kind t1.sort t2)
      | "Typ_dep" -> 
          let t1 = decodeTyp tctx env (args.(0)) in 
          let v2 = decodeVal tctx env (args.(1)) in 
            twithsort (Typ_dep(t1, v2)) (open_kind_with_exp t1.sort v2)
      | "Typ_affine" -> 
          let t = decodeTyp tctx env (args.(0)) in 
            twithsort (Typ_affine(t)) Kind_affine
      | "Typ_lam" -> 
          let t1 = decodeTyp tctx env (args.(0)) in 
          let x = Absyn.new_bvd None in 
          let t2 = decodeTyp tctx (push_typ env x t1) (args.(1)) in
            twithsort (Typ_lam(x, t1, t2)) (Kind_dcon(Some x, t1, t2.sort))
      | "Typ_tlam" ->
          let k = decodeKind tctx env (args.(0)) in 
          let x = Absyn.new_bvd None in 
          let t = decodeTyp tctx (push_kind env x k) (args.(1)) in
            twithsort (Typ_tlam(x, k, t)) (Kind_tcon(Some x, k, t.sort))
      | _ -> raise Impos 

and decodeKind tctx env (tm:Expr) : kind = 
  if not (tm.Sort.Equals(tctx.sortMap.sortToZ3Sort Kind_sort))
  then raise (Err("Unexpected sort in decodeKind"));
  let args = tm.Args in 
    match tm.FuncDecl.Name.ToString() with
      | "Kind_star" -> Kind_star
      | "Kind_erasable" -> Kind_erasable
      | "Kind_affine" -> Kind_affine
      | "Kind_prop" -> Kind_prop
      | "Kind_tcon" -> 
          let k1 = decodeKind tctx env (args.(0)) in 
          let x = Absyn.new_bvd None in 
          let k2 = decodeKind tctx (push_kind env x k1) (args.(1)) in 
            Kind_tcon(Some x, k1, k2)
      | "Kind_dcon" -> 
          let t1 = decodeTyp tctx env (args.(0)) in 
          let x = Absyn.new_bvd None in 
          let k2 = decodeKind tctx (push_typ env x t1) (args.(1)) in 
            Kind_dcon(Some x, t1, k2)
      | _ -> raise Impos

and decodeTypeName tctx env (tm:Expr) : var<kind> = 
  let nm = tm.FuncDecl.Name.ToString().Substring(10) in //new String("Type_name_").Length
  let lid = Sugar.lid_of_text nm dummyRange in 
  let k = lookup_typ_lid env lid in 
    fvwithsort lid k
    
and decodeVal tctx env (tm:Expr) : exp = 
  if not (tm.Sort.Equals(tctx.sortMap.sortToZ3Sort Term_sort))
  then raise (Err("Unexpected sort in decodeKind"));
  let args = tm.Args in 
  let nm = tm.FuncDecl.Name.ToString() in 
    if nm.StartsWith("Term_fvar_")
    then 
      let lid = Sugar.lid_of_text (nm.Substring(10)) dummyRange in 
      let t = lookup_lid env lid in
      let var = fvwithsort lid t in 
        ewithsort (Exp_fvar(var, None)) t
    else if nm.StartsWith("Term_bvar_")
    then 
      let x = Absyn.bvd_to_bvar_s (Absyn.bvdef_of_str (nm.Substring(10))) tunknown in 
      let t = lookup_bvar env x in
      let x = setsort x t in 
        ewithsort (Exp_bvar(x)) t
    else if nm.StartsWith("const_string")
    then decodeConstantVar env nm
    else if nm.StartsWith("Term_constr_")
    then 
      let lid = Sugar.lid_of_text (nm.Substring(12)) dummyRange in 
      let t = lookup_lid env lid in
      let var = fvwithsort lid t in 
      let sorts = sortsFromTyp t in 
        if args.Length <> sorts.Length then raise Impos;
        let args = List.map2 (fun arg sort -> match sort with 
                                | Type_sort -> Inl (decodeTyp tctx env arg)
                                | Term_sort -> Inr (decodeVal tctx env arg))
          (List.ofArray args) sorts in 
        let t = AbsynUtils.open_typ_with_typs_or_exps t args in 
        let typs, tms = takeUntil (function Inr _ -> true | _ -> false) args in 
        let typs = List.map (function Inl t -> t) typs in 
        let tms = List.map (function Inr e -> e) tms in 
          ewithsort (Exp_constr_app(var, typs, [], tms)) t
    else match nm with 
      | "Term_other" -> 
          let i = (args.(0) :?> IntNum).Int in
            if i = -1
            then ewithsort (Exp_constant (Sugar.Const_unit)) Const.unit_typ
            else decodeConstant env i
      | "Exp_bvar" ->
          let ix = (args.(0) :?> IntNum).Int in
          let bv = lookup_bvar_ix env ix in 
            ewithsort (Exp_bvar(bv)) bv.sort
      | "BoxInt" -> 
          let i = (args.(0) :?> IntNum).Int in
            ewithsort (Exp_constant (Sugar.Const_int32 i)) Const.int_typ
      | "BoxBool" -> 
            let b = args.(0).IsTrue in
            ewithsort (Exp_constant (Sugar.Const_bool b)) Const.bool_typ
      | _ -> 
          failwith (spr "NYI: decodeVal for %s" (tm.ToString()))
