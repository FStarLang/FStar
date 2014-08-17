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
module Microsoft.FStar.Absyn.Syntax
(* Type definitions for the core AST *)

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.LazySet

exception Err of string
exception Error of string * Range.range
exception Warning of string * Range.range

type ident = {idText:string;
              idRange:Range.range}
type LongIdent = {ns:list<ident>; 
                  ident:ident; 
                  nsstr:string;
                  str:string}
type lident = LongIdent
type withinfo_t<'a,'t> = {
  v: 'a; 
  sort: 't;
  p: Range.range; 
} 
type var<'t>  = withinfo_t<lident,'t>
type fieldname = lident
type inst<'a> = ref<option<'a>>
type bvdef<'a> = {ppname:ident; realname:ident}
type bvar<'a,'t> = withinfo_t<bvdef<'a>,'t> 
(* Bound vars have a name for pretty printing, 
   and a unique name generated during desugaring. 
   Only the latter is used during type checking.  *)
  
(* Term language *)
type sconst = 
  | Const_unit
  | Const_uint8       of byte
  | Const_bool        of bool
  | Const_int32       of int32
  | Const_int64       of int64
  | Const_char        of char
  | Const_float       of double
  | Const_bytearray   of array<byte> * Range.range 
  | Const_string      of array<byte> * Range.range           (* unicode encoded, F#/Caml independent *)

type memo<'a> = ref<option<'a>>
type typ' =  
  | Typ_btvar    of btvar
  | Typ_const    of ftvar 
  | Typ_fun      of option<bvvdef> * typ * comp * bool       (* x:t -> M t' wp  or  t -> M t' wp, bool marks implicit arguments *)
  | Typ_univ     of btvdef * knd  * comp                     (* 'a:k -> M t wp *)
  | Typ_refine   of bvvdef * typ * typ                       (* x:t{phi} *)
  | Typ_app      of typ * typ * bool                         (* t t' -- bool marks an explicitly provided implicit arg *) 
  | Typ_dep      of typ * exp * bool                         (* t e -- bool marks an explicitly provided implicit arg *)  
  | Typ_lam      of bvvdef * typ * typ                       (* fun (x:t) => T *)
  | Typ_tlam     of btvdef * knd * typ                       (* fun ('a:k) => T *) 
  | Typ_ascribed of typ * knd                                (* t <: k *)
  | Typ_meta     of meta_t                                   (* Not really in the type language; a way to stash convenient metadata with types *)
  | Typ_uvar     of uvar_t * knd                             (* not present after 1st round tc *)
  | Typ_delayed  of typ * subst * memo<typ>                  (* A delayed substitution---always force it before inspecting the first arg *)
  | Typ_unknown                                              (* not present after 1st round tc *)
and typ = syntax<typ',knd>
and comp_typ = {
  effect_name:lident; 
  result_typ:typ; 
  effect_args:list<either<typ,exp>>;
  flags:list<cflags>
  }
and comp' = 
  | Total of typ
  | Comp of comp_typ                    
  | Flex of uvar_c * typ
and comp = syntax<comp', unit>
and cflags = 
  | TOTAL 
  | MLEFFECT 
  | RETURN 
  | SOMETRIVIAL
and uvar_c = Unionfind.uvar<comp_typ_uvar_basis>
and comp_typ_uvar_basis = 
  | Floating 
  | Resolved of comp
and uvar_t = Unionfind.uvar<uvar_basis<typ,knd>>
and meta_t = 
  | Meta_pattern of typ * list<either<typ,exp>>
  | Meta_named of typ * lident                               (* Useful for pretty printing to keep the type abbreviation around *)
and uvar_basis<'a,'b> = 
  | Uvar of ('a -> 'b -> bool)                               (* A well-formedness check to ensure that all names are in scope *)
  | Fixed of 'a
and exp' =
  | Exp_bvar       of bvvar
  | Exp_fvar       of fvvar * bool                            (* flag indicates a constructor *)
  | Exp_constant   of sconst
  | Exp_abs        of bvvdef * typ * exp 
  | Exp_tabs       of btvdef * knd * exp            
  | Exp_app        of exp * exp * bool                           (* flag indicates whether the argument is explicit instantiation of an implict param *)
  | Exp_tapp       of exp * typ             
  | Exp_match      of exp * list<(pat * option<exp> * exp)>      (* optional when clause in each equation *)
  | Exp_ascribed   of exp * typ 
  | Exp_let        of letbindings * exp                          (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
  | Exp_uvar       of uvar_e * typ                               (* not present after 1st round tc *)
  | Exp_delayed    of exp * subst * memo<exp>                    (* A delayed substitution --- always force it before inspecting the first arg *)
  | Exp_meta       of meta_e                                     (* No longer tag every expression with info, only selectively *)
and exp = syntax<exp',typ>
and meta_e = 
  | Meta_desugared of exp * meta_source_info                     (* Node tagged with some information about source term before desugaring *)
  | Meta_datainst  of exp * option<typ>                          (* Expect the data constructor e to build a t-typed value; only used internally to pretyping; not visible elsewhere *)
and meta_source_info =
  | Data_app
  | Sequence                   
  | Primop                                  (* ... add more cases here as needed for better code generation *)
and uvar_e = Unionfind.uvar<uvar_basis<exp,typ>>
and btvdef = bvdef<typ>
and bvvdef = bvdef<exp>
and pat = 
  | Pat_cons     of lident * list<pat>
  | Pat_var      of bvvdef
  | Pat_tvar     of btvdef
  | Pat_constant of sconst
  | Pat_disj     of list<pat>
  | Pat_wild
  | Pat_twild
  | Pat_withinfo of pat * Range.range
and knd' =
  | Kind_type
  | Kind_effect
  | Kind_abbrev of kabbrev * knd                          (* keep the abbreviation around for printing *)
  | Kind_tcon of option<btvdef> * knd * knd * bool    (* 'a:k -> k'; bool marks implicit *)
  | Kind_dcon of option<bvvdef> * typ * knd * bool        (* x:t -> k; bool marks implicit *)
  | Kind_uvar of uvar_k                                   (* not present after 1st round tc *)
  | Kind_delayed of knd * subst * memo<knd>               (* delayed substitution --- always force before inspecting first element *)
  | Kind_unknown                                          (* not present after 1st round tc *)
and knd = syntax<knd', unit>

and kabbrev = lident * list<either<typ,exp>>
and uvar_k = Unionfind.uvar<uvar_basis<knd,unit>>
and lbname = either<bvvdef, lident>
and letbindings = bool * list<(lbname * typ * exp)> (* let recs may have more than one element; top-level lets have lidents *)
and subst' = list<subst_elt>
and subst = {
    subst:subst';
    subst_fvs:memo<freevars>;
}
and subst_map = Util.smap<either<typ, exp>>
and subst_elt = either<(btvdef*typ), (bvvdef*exp)>
and fvar = either<btvdef, bvvdef>
and freevars = {
  ftvs: list<btvar>;
  fxvs: list<bvvar>;
}
and uvars = {
  uvars_k: list<uvar_k>;
  uvars_t: list<(uvar_t*knd)>;
  uvars_e: list<(uvar_e*typ)>;
  uvars_c: list<uvar_c>;
}
and syntax<'a,'b> = {
    n:'a;
    tk:'b;
    pos:Range.range;
    fvs:memo<freevars>;
    uvs:memo<uvars>;
}
and btvar = bvar<typ,knd>
and bvvar = bvar<exp,typ>
and ftvar = var<knd>
and fvvar = var<typ>

type formula = typ
type formulae = list<typ>

type tparam =
  | Tparam_typ  of btvdef * knd (* idents for pretty printing *)
  | Tparam_term of bvvdef * typ

type qualifier = 
  | Private 
  | Public 
  | Assumption
  | Definition  
  | Query
  | Lemma
  | Logic
  | Discriminator of lident                          (* discriminator for a datacon l *)
  | Projector of lident * either<btvdef, bvvdef>     (* projector for datacon l's argument 'a or x *)
  | RecordType of list<ident>                        (* unmangled field names *)
  | RecordConstructor of list<ident>                 (* unmangled field names *)
  | ExceptionConstructor
  | Effect 
 
type monad_abbrev = {
  mabbrev:lident;
  parms:list<tparam>;
  def:typ
  }
type monad_order = {
  source:lident;
  target:lident;
  lift: typ
 }
type monad_lat = list<monad_order>
type monad_decl = {
    mname:lident;
    total:bool;
    signature:knd;
    ret:typ;
    bind_wp:typ;
    bind_wlp:typ;
    ite_wp:typ;
    ite_wlp:typ;
    wp_binop:typ;
    wp_as_type:typ;
    close_wp:typ;
    close_wp_t:typ;
    assert_p:typ;
    assume_p:typ;
    null_wp:typ;
    trivial:typ;
    abbrevs:list<sigelt> 
 }
and sigelt =
  | Sig_tycon          of lident * list<tparam> * knd * list<lident> * list<lident> * list<qualifier> * Range.range (* bool is for a prop, list<lident> identifies mutuals, second list<lident> are all the constructors *)
  | Sig_typ_abbrev     of lident * list<tparam> * knd * typ * list<qualifier> * Range.range 
  | Sig_datacon        of lident * typ * lident * list<qualifier> * Range.range  (* second lident is the name of the type this constructs *)
  | Sig_val_decl       of lident * typ * list<qualifier> * Range.range 
  | Sig_assume         of lident * formula * list<qualifier> * Range.range 
  | Sig_let            of letbindings * Range.range 
  | Sig_main           of exp * Range.range 
  | Sig_bundle         of list<sigelt> * Range.range  (* an inductive type is a bundle of all mutually defined Sig_tycons and Sig_datacons *)
  | Sig_monads         of list<monad_decl> * monad_lat * Range.range
type sigelts = list<sigelt>

type modul = {
  name: lident;
  declarations: sigelts;
  exports: sigelts;
  is_interface:bool
}

(*********************************************************************************)
(* Identifiers to/from strings *)    
(*********************************************************************************)
type path = list<string>
let dummyRange = 0L
let withinfo v s r = {v=v; sort=s; p=r}
let withsort v s = withinfo v s dummyRange
let mk_ident (text,range) = {idText=text; idRange=range}
let id_of_text str = mk_ident(str, dummyRange)
let text_of_id (id:ident) = id.idText
let text_of_path path = Util.concat_l "." path
let path_of_text text = String.split ['.'] text
let path_of_ns ns = List.map text_of_id ns
let path_of_lid lid = List.map text_of_id (lid.ns@[lid.ident])
let ids_of_lid lid = lid.ns@[lid.ident]
let lid_of_ids ids = 
    let ns, id = Util.prefix ids in 
    let nsstr = List.map text_of_id ns |> text_of_path in
    {ns=ns; 
     ident=id; 
     nsstr=nsstr; 
     str=(if nsstr="" then id.idText else nsstr ^ "." ^ id.idText)}
let lid_of_path path pos = 
    let ids = List.map (fun s -> mk_ident(s, pos)) path in
    lid_of_ids ids
let text_of_lid lid = lid.str
let lid_equals l1 l2 = l1.str = l2.str
let bvd_eq (bvd1:bvdef<'a>) (bvd2:bvdef<'a>) = bvd1.realname=bvd2.realname
let order_bvd x y = match x, y with 
  | Inl _, Inr _ -> -1
  | Inr _, Inl _ -> 1
  | Inl x, Inl y -> String.compare x.realname.idText y.realname.idText
  | Inr x, Inr y -> String.compare x.realname.idText y.realname.idText

let range_of_lid (lid:LongIdent) = lid.ident.idRange
let range_of_lbname (l:lbname) = match l with
    | Inl x -> x.ppname.idRange
    | Inr l -> range_of_lid l

(*********************************************************************************)
(* Syntax builders *)
(*********************************************************************************)

open Microsoft.FStar.Range

let syn p k f = f k p
let mk_fvs () = Util.mk_ref None
let mk_uvs () = Util.mk_ref None
let no_fvs = {
    ftvs=[]; fxvs=[]; 
}
let no_uvs = {
    uvars_k=[]; uvars_t=[]; uvars_e=[]; uvars_c=[]
}

let mk_Kind_type = {n=Kind_type; pos=dummyRange; tk=(); uvs=mk_uvs(); fvs=mk_fvs()}
let mk_Kind_effect = {n=Kind_effect; pos=dummyRange; tk=(); uvs=mk_uvs(); fvs=mk_fvs()}
let mk_Kind_abbrev ((kabr:kabbrev), (k:knd)) p = {
    n=Kind_abbrev(kabr, k);
    pos=p;
    tk=();
    uvs=mk_uvs(); fvs=mk_fvs()
}
let mk_Kind_tcon ((a:option<btvdef>),(k1:knd),(k2:knd),(b:bool)) p = {
    n=Kind_tcon(a, k1, k2, b);
    pos=p;
    tk=();
    uvs=mk_uvs(); fvs=mk_fvs();//union k1.fvs (match a with None -> k2.fvs | Some a -> difference k2.fvs (set_of_list [Inl a]));
}
let mk_Kind_dcon ((a:option<bvvdef>),(t1:typ),(k2:knd),(b:bool)) p = {
    n=Kind_dcon(a, t1, k2, b);
    pos=p;
    tk=();
    uvs=mk_uvs(); fvs=mk_fvs();//union t1.fvs (match a with None -> k2.fvs | Some a -> difference k2.fvs (set_of_list [Inr a]));
}
let mk_Kind_uvar (uv:uvar_k) p = {
    n=Kind_uvar uv;
    pos=p;
    tk=();
    uvs=mk_uvs(); fvs=mk_fvs();
    
}
let mk_Kind_delayed ((k:knd),(s:subst),(m:memo<knd>)) p = {
    n=Kind_delayed(k, s, m);
    pos=p;
    tk=();
    uvs=mk_uvs(); fvs=mk_fvs();//union k.fvs s.subst_fvs;
    
}
let mk_Kind_unknown  = {n=Kind_unknown; pos=dummyRange; tk=(); uvs=mk_uvs(); fvs=mk_fvs()}

let mk_Typ_btvar    (x:btvar) (k:knd) (p:range) = {n=Typ_btvar x; tk=k; pos=p; uvs=mk_uvs(); fvs=mk_fvs();}//set_of_list [Inl x.v]}
let mk_Typ_const    (x:ftvar) (k:knd) (p:range) = {n=Typ_const x; tk=k; pos=p; uvs=mk_uvs(); fvs=mk_fvs()}
let mk_Typ_fun      ((x:option<bvvdef>),(t:typ),(c:comp),(b:bool)) (k:knd) (p:range) = {
    n=Typ_fun(x, t, c, b); 
    tk=k;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//(match x with None -> union t.fvs c.fvs | Some x -> union t.fvs (difference c.fvs (set_of_list [Inr x])));
    
}
let mk_Typ_univ     ((x:btvdef),(k:knd),(c:comp)) (k':knd) (p:range) = {
    n=Typ_univ(x, k, c);
    tk=k';
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//difference (union k.fvs c.fvs) (set_of_list [Inl x]);
    
}
let mk_Typ_refine   ((x:bvvdef),(t:typ),(phi:typ)) (k:knd) (p:range) = {
    n=Typ_refine(x, t, phi);
    tk=k;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//union t.fvs (difference phi.fvs (set_of_list [Inr x]));
    
}
let mk_Typ_app      ((t1:typ),(t2:typ),(b:bool)) (k:knd) (p:range) = {
    n=Typ_app(t1, t2, b);
    tk=k;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//union t1.fvs t2.fvs;
    
}
let mk_Typ_dep      ((t:typ),(e:exp),(b:bool)) (k:knd) (p:range) = {
    n=Typ_dep(t, e, b);
    tk=k;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//union t.fvs e.fvs;
    
}
let mk_Typ_lam      ((x:bvvdef),(t1:typ),(t2:typ)) (k:knd) (p:range) = {
    n=Typ_lam(x, t1, t2);
    tk=k;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//union t1.fvs (difference t2.fvs (set_of_list [Inr x]));
    
}
let mk_Typ_tlam     ((a:btvdef),(k:knd),(t:typ)) (k':knd) (p:range) = {
    n=Typ_tlam(a, k, t);
    tk=k';
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//union k.fvs (difference t.fvs (set_of_list [Inl a]));
    
}
let mk_Typ_ascribed' ((t:typ),(k:knd)) (k':knd) (p:range) = {
    n=Typ_ascribed(t, k);
    tk=k';
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//union t.fvs k.fvs;
    
}
let mk_Typ_ascribed ((t:typ),(k:knd)) (p:range) = mk_Typ_ascribed' (t, k) k p

let mk_Typ_meta'    (m:meta_t) (k:knd) p = 
    {n=Typ_meta m;
     tk=k;
     pos=p;
     uvs=mk_uvs(); fvs=mk_fvs();//fvs;
    }
let mk_Typ_meta     (m:meta_t) = match m with 
    | Meta_pattern(t, _) 
    | Meta_named(t, _) ->  mk_Typ_meta' m t.tk t.pos 

let mk_Typ_uvar'     ((u:uvar_t),(k:knd)) (k':knd) (p:range) = {
    n=Typ_uvar(u, k);
    tk=k';
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//emp_fvs;
    
}
let mk_Typ_uvar (u, k) p = mk_Typ_uvar' (u, k) k p 
let mk_Typ_delayed  ((t:typ),(s:subst),(m:memo<typ>)) (k:knd) (p:range) = {
    n=Typ_delayed(t, s, m);
    tk=k;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//union t.fvs s.subst_fvs;
    
}
let mk_Typ_unknown  = {n=Typ_unknown; pos=dummyRange; tk=mk_Kind_unknown; uvs=mk_uvs(); fvs=mk_fvs()}

let mk_Total t = {
    n=Total t;
    tk=();
    pos=t.pos;
    uvs=mk_uvs(); fvs=mk_fvs();
    
}
let mk_Flex (u,t) = {
    n=Flex(u,t);
    tk=();
    pos=t.pos;
    uvs=mk_uvs(); fvs=mk_fvs();//t.fvs;
    
}

let mk_Comp (ct:comp_typ) = 
    {n=Comp ct;
     tk=();
     pos=ct.result_typ.pos;
     uvs=mk_uvs(); fvs=mk_fvs();//set_of_thunk fvs;
    }

let mk_Exp_bvar (x:bvvar) (t:typ) p = {
    n=Exp_bvar x;
    tk=t;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//set_of_list [Inr x.v];
    
}
let mk_Exp_fvar ((x:fvvar),(b:bool)) (t:typ) p = {
    n=Exp_fvar(x, b);
    tk=t;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//emp_fvs;
    
} 

let mk_Exp_constant (s:sconst) (t:typ) p = {
    n=Exp_constant s;
    tk=t;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//emp_fvs;
    
} 
let mk_Exp_abs ((x:bvvdef),(t:typ),(e:exp)) (t':typ) p = {
    n=Exp_abs(x, t, e);
    tk=t';
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//union t.fvs (difference e.fvs (set_of_list [Inr x]));
    
}
let mk_Exp_tabs ((a:btvdef),(k:knd),(e:exp)) (t:typ) p = {
    n=Exp_tabs(a, k, e);
    tk=t;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//union t.fvs (difference e.fvs (set_of_list [Inl a]));
    
}
let mk_Exp_app ((e1:exp),(e2:exp),(b:bool)) (t:typ) p = {
    n=Exp_app(e1, e2, b);
    tk=t;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//union e1.fvs e2.fvs;
    
}
let mk_Exp_tapp ((e:exp),(t:typ)) (t':typ) p = {
    n=Exp_tapp(e, t);
    tk=t';
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//union e.fvs t.fvs;
    
}

let rec pat_vars r = function 
  | Pat_cons(_, ps) -> 
    let vars = List.collect (pat_vars r) ps in 
    if vars |> nodups (fun x y -> match x, y with 
      | Inl x, Inl y -> bvd_eq x y
      | Inr x, Inr y -> bvd_eq x y
      | _ -> false) 
    then vars
    else raise (Error("Pattern variables may not occur more than once", r))
  | Pat_var x -> [Inr x]
  | Pat_tvar a -> [Inl a]
  | Pat_disj ps -> 
    let vars = List.map (pat_vars r) ps in 
    if not (List.tl vars |> Util.for_all (Util.set_eq order_bvd (List.hd vars)))
    then 
      let vars = Util.concat_l ";\n" (vars |> 
          List.map (fun v -> Util.concat_l ", " (List.map (function 
            | Inr x -> x.ppname.idText
            | Inl x -> x.ppname.idText) v))) in
      raise (Error(Util.format1 "Each branch of this pattern binds different variables: %s" vars, r))
    else List.hd vars
  | Pat_wild 
  | Pat_twild
  | Pat_constant _ -> []
  | Pat_withinfo (p, r) -> pat_vars r p


let mk_Exp_match ((e:exp),(pats:list<(pat * option<exp> * exp)>)) (t:typ) p = 
    {
       n=Exp_match(e, pats);
       tk=t;
       pos=p;
       uvs=mk_uvs(); fvs=mk_fvs();//union e.fvs (set_of_thunk fv_branches);
    } 
let mk_Exp_ascribed' ((e:exp),(t:typ)) (t':typ) p = {
    n=Exp_ascribed(e, t);
    tk=t';
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//union e.fvs t.fvs;
    
}
let mk_Exp_ascribed ((e:exp),(t:typ)) p = mk_Exp_ascribed' (e, t) t p
let mk_Exp_let ((lbs:letbindings),(e:exp)) (t:typ) p = 
   {
    n=Exp_let(lbs, e);
    tk=t;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//union e.fvs (set_of_thunk fv_lbs);
   }

let mk_Exp_uvar' ((u:uvar_e),(t:typ)) (t':typ) p = {
    n=Exp_uvar(u, t);
    tk=t';
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//emp_fvs;
    
}
let mk_Exp_uvar  ((u:uvar_e),(t:typ)) p = mk_Exp_uvar' (u, t) t p

let mk_Exp_delayed ((e:exp),(s:subst),(m:memo<exp>)) (t:typ) p = {
    n=Exp_delayed(e, s, m);
    tk=t;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();//union e.fvs s.subst_fvs;
    
}
let mk_Exp_meta' (m:meta_e) (t:typ) p = 
    { 
        n=Exp_meta m;
        tk=t;
        pos=p;
        uvs=mk_uvs(); fvs=mk_fvs();//fvs;
    }
let mk_Exp_meta (m:meta_e) = match m with
      | Meta_desugared(e, _)  
      | Meta_datainst(e, _) -> mk_Exp_meta' m e.tk e.pos

let mk_subst (s:subst') = 
    {subst=s;
     subst_fvs=mk_fvs()}

let extend_subst x s = 
    {subst=x::s.subst;
     subst_fvs=mk_fvs();//fvs;
    }

let tun   = mk_Typ_unknown
let kun   = mk_Kind_unknown
let ktype = mk_Kind_type
