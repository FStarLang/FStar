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
  | Typ_fun      of binders * comp                           (* (ai:ki|xi:ti) -> M t' wp *)
  | Typ_refine   of bvvar * typ                             (* x:t{phi} *)
  | Typ_app      of typ * args                               (* args in reverse order *)
  | Typ_lam      of binders * typ                            (* fun (ai|xi:tau_i) => T *)
  | Typ_ascribed of typ * knd                                (* t <: k *)
  | Typ_meta     of meta_t                                   (* Not really in the type language; a way to stash convenient metadata with types *)
  | Typ_uvar     of uvar_t * knd                             (* not present after 1st round tc *)
  | Typ_delayed  of typ * subst_t * memo<typ>                  (* A delayed substitution---always force it before inspecting the first arg *)
  | Typ_unknown                                              (* not present after 1st round tc *)
and arg = either<typ,exp> * bool                                        (* bool marks an explicitly provided implicit arg *)
and args = list<arg>
and binder = either<btvar,bvvar> * bool
and binders = list<binder>
and typ = syntax<typ',knd>
and comp_typ = {
  effect_name:lident; 
  result_typ:typ; 
  effect_args:args;
  flags:list<cflags>
  }
and comp' = 
  | Total of typ
  | Comp of comp_typ                    
and comp = syntax<comp', unit>
and cflags = 
  | TOTAL 
  | MLEFFECT 
  | RETURN 
  | SOMETRIVIAL
  | LEMMA
and uvar_t = Unionfind.uvar<uvar_basis<typ,knd>>
and meta_t = 
  | Meta_pattern of typ * list<arg>
  | Meta_named of typ * lident                               (* Useful for pretty printing to keep the type abbreviation around *)
  | Meta_labeled of typ * string * bool                      (* Sub-terms in a VC are labeled with error messages to be reported, used in SMT encoding *)
  | Meta_refresh_label of typ * option<bool> * Range.range   (* Add the range to the label of any labeled sub-term of the type *)
and uvar_basis<'a,'b> = 
  | Uvar of ('a -> 'b -> bool)                               (* A well-formedness check to ensure that all names are in scope *)
  | Fixed of 'a
and exp' =
  | Exp_bvar       of bvvar
  | Exp_fvar       of fvvar * bool                            (* flag indicates a constructor *)
  | Exp_constant   of sconst
  | Exp_abs        of binders * exp 
  | Exp_app        of exp * args                                 (* args in order from left to right *)
  | Exp_match      of exp * list<(pat * option<exp> * exp)>      (* optional when clause in each equation *)
  | Exp_ascribed   of exp * typ 
  | Exp_let        of letbindings * exp                          (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
  | Exp_uvar       of uvar_e * typ                               (* not present after 1st round tc *)
  | Exp_delayed    of exp * subst_t * memo<exp>                    (* A delayed substitution --- always force it before inspecting the first arg *)
  | Exp_meta       of meta_e                                     (* No longer tag every expression with info, only selectively *)
and exp = syntax<exp',typ>
and meta_e = 
  | Meta_desugared     of exp * meta_source_info                 (* Node tagged with some information about source term before desugaring *)
  | Meta_datainst      of exp * option<typ>                      (* Expect the data constructor e to build a t-typed value; only used internally to pretyping; not visible elsewhere *)
and meta_source_info =
  | Data_app
  | Sequence                   
  | Primop                                  (* ... add more cases here as needed for better code generation *)
and uvar_e = Unionfind.uvar<uvar_basis<exp,typ>>
and btvdef = bvdef<typ>
and bvvdef = bvdef<exp>
and pat' = 
  | Pat_disj     of list<pat>
  | Pat_constant of sconst
  | Pat_cons     of fvvar * list<pat>
  | Pat_var      of bvvar
  | Pat_tvar     of btvar
  | Pat_wild     of bvvar                                 (* need stable names for even the wild patterns *)
  | Pat_twild    of btvar
  | Pat_dot_term of bvvar * exp
  | Pat_dot_typ  of btvar * typ
and pat = withinfo_t<pat',either<knd,typ>>                (* the meta-data is a typ, except for Pat_dot_typ and Pat_tvar, where it is a kind (not strictly needed) *)
and knd' =
  | Kind_type
  | Kind_effect
  | Kind_abbrev of kabbrev * knd                          (* keep the abbreviation around for printing *)
  | Kind_arrow of binders * knd                           (* (ai:ki|xi:ti) => k' *)
  | Kind_uvar of uvar_k_app                               (* not present after 1st round tc *)
  | Kind_lam of binders * knd                             (* not present after 1st round tc *)
  | Kind_delayed of knd * subst_t * memo<knd>               (* delayed substitution --- always force before inspecting first element *)
  | Kind_unknown                                          (* not present after 1st round tc *)
and knd = syntax<knd', unit>
and uvar_k_app = uvar_k * args
and kabbrev = lident * args
and uvar_k = Unionfind.uvar<uvar_basis<knd,unit>>
and lbname = either<bvvdef, lident>
and letbindings = bool * list<(lbname * typ * exp)> (* let recs may have more than one element; top-level lets have lidents *)
and subst_t = list<list<subst_elt>>
and subst_map = Util.smap<either<typ, exp>>
and subst_elt = either<(btvdef*typ), (bvvdef*exp)>
and fvar = either<btvdef, bvvdef>
and freevars = {
  ftvs: set<btvar>;
  fxvs: set<bvvar>;
}
and uvars = {
  uvars_k: set<uvar_k>;
  uvars_t: set<(uvar_t*knd)>;
  uvars_e: set<(uvar_e*typ)>;
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

type subst = list<subst_elt>
type either_var = either<btvar, bvvar>
type freevars_l = list<either_var>
type formula = typ
type formulae = list<typ>
type qualifier = 
  | Private 
  | Public 
  | Assumption
  | Definition  
  | Query
  | Lemma
  | Opaque
  | Logic
  | Discriminator of lident                          (* discriminator for a datacon l *)
  | Projector of lident * either<btvdef, bvvdef>     (* projector for datacon l's argument 'a or x *)
  | RecordType of list<ident>                        (* unmangled field names *)
  | RecordConstructor of list<ident>                 (* unmangled field names *)
  | ExceptionConstructor
  | Effect 
 
type tycon = lident * binders * knd
type monad_abbrev = {
  mabbrev:lident;
  parms:binders;
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
    if_then_else:typ;
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
    abbrevs:list<sigelt>;
    kind_abbrevs: list<(lident * list<either<btvdef, bvvdef>> * knd)> 
 }
and sigelt =
  | Sig_tycon          of lident * binders * knd * list<lident> * list<lident> * list<qualifier> * Range.range (* bool is for a prop, list<lident> identifies mutuals, second list<lident> are all the constructors *)
  | Sig_typ_abbrev     of lident * binders * knd * typ * list<qualifier> * Range.range 
  | Sig_datacon        of lident * typ * tycon * list<qualifier> * Range.range  
  | Sig_val_decl       of lident * typ * list<qualifier> * Range.range 
  | Sig_assume         of lident * formula * list<qualifier> * Range.range 
  | Sig_let            of letbindings * Range.range * list<lident>
  | Sig_main           of exp * Range.range 
  | Sig_bundle         of list<sigelt> * Range.range * list<lident> (* an inductive type is a bundle of all mutually defined Sig_tycons and Sig_datacons *)
  | Sig_monads         of list<monad_decl> * monad_lat * Range.range * list<lident>
type sigelts = list<sigelt>

type modul = {
  name: lident;
  declarations: sigelts;
  exports: sigelts;
  is_interface:bool;
  is_deserialized:bool (* flag to indicate that the module was read from disk, and hence need not be type checked*)
}

type ktec = 
    | K of knd
    | T of typ
    | E of exp
    | C of comp

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
let bvd_eq (bvd1:bvdef<'a>) (bvd2:bvdef<'a>) = bvd1.realname.idText=bvd2.realname.idText
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
let new_ftv_set () = Util.new_set (fun x y -> Util.compare x.v.realname.idText y.v.realname.idText) (fun x -> Util.hashcode x.v.realname.idText)
let new_uv_set () = Util.new_set (fun x y -> Unionfind.uvar_id x - Unionfind.uvar_id y) Unionfind.uvar_id
let new_uvt_set () = Util.new_set (fun (x, _) (y, _) -> Unionfind.uvar_id x - Unionfind.uvar_id y) (fun (x, _) -> Unionfind.uvar_id x)
let no_fvs = {
    ftvs=new_ftv_set();
    fxvs=new_ftv_set();
}
let no_uvs = {
    uvars_k=new_uv_set(); 
    uvars_t=new_uvt_set(); 
    uvars_e=new_uvt_set(); 
}
let freevars_of_list l = 
    l |> List.fold_left (fun out -> function
        | Inl btv -> {out with ftvs=Util.set_add btv out.ftvs}
        | Inr bxv -> {out with fxvs=Util.set_add bxv out.fxvs}) no_fvs
let list_of_freevars fvs = 
   (Util.set_elements fvs.ftvs |> List.map Inl)@(Util.set_elements fvs.fxvs |> List.map Inr)

let mk_Kind_type = {n=Kind_type; pos=dummyRange; tk=(); uvs=mk_uvs(); fvs=mk_fvs()}
let mk_Kind_effect = {n=Kind_effect; pos=dummyRange; tk=(); uvs=mk_uvs(); fvs=mk_fvs()}
let mk_Kind_abbrev ((kabr:kabbrev), (k:knd)) p = {
    n=Kind_abbrev(kabr, k);
    pos=p;
    tk=();
    uvs=mk_uvs(); fvs=mk_fvs()
}
let mk_Kind_arrow ((bs:binders),(k:knd)) p = {
    n=Kind_arrow(bs, k);
    pos=p;
    tk=();
    uvs=mk_uvs(); fvs=mk_fvs();
}
let mk_Kind_arrow' ((bs:binders), (k:knd)) p = 
    match bs with 
        | [] -> k
        | _ ->  match k.n with Kind_arrow(bs', k') -> mk_Kind_arrow(bs@bs', k') p | _ -> mk_Kind_arrow(bs, k) p

let mk_Kind_uvar (uv:uvar_k_app) p = {
    n=Kind_uvar uv;
    pos=p;
    tk=();
    uvs=mk_uvs(); fvs=mk_fvs();
    
}
let mk_Kind_lam ((vs:binders), (k:knd)) p = {
    n=Kind_lam(vs, k);
    pos=p;
    tk=();
    uvs=mk_uvs(); fvs=mk_fvs();
}
let mk_Kind_delayed ((k:knd),(s:subst_t),(m:memo<knd>)) p = {
    n=Kind_delayed(k, s, m);
    pos=p;
    tk=();
    uvs=mk_uvs(); fvs=mk_fvs();//union k.fvs s.subst_fvs;
    
}
let mk_Kind_unknown  = {n=Kind_unknown; pos=dummyRange; tk=(); uvs=mk_uvs(); fvs=mk_fvs()}

let mk_Typ_btvar    (x:btvar) (k:knd) (p:range) = {n=Typ_btvar x; tk=k; pos=p; uvs=mk_uvs(); fvs=mk_fvs();}
let mk_Typ_const    (x:ftvar) (k:knd) (p:range) = {n=Typ_const x; tk=k; pos=p; uvs=mk_uvs(); fvs=mk_fvs()}
let rec check_fun (bs:binders) (c:comp) p = 
    match bs with 
        | [] -> failwith "Empty binders"
        | _  -> Typ_fun(bs, c)
let mk_Typ_fun      ((bs:binders),(c:comp)) (k:knd) (p:range) = {
    n=check_fun bs c p;
    tk=k;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
}
let mk_Typ_refine   ((x:bvvar),(phi:typ)) (k:knd) (p:range) = {
    n=Typ_refine(x, phi);
    tk=k;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
}
let mk_Typ_app      ((t1:typ),(args:list<arg>)) (k:knd) (p:range) = {
    n=(match args with [] -> failwith "Empty arg list!" | _ -> Typ_app(t1, args));
    tk=k;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
}
let mk_Typ_app' ((t1:typ), (args:list<arg>)) (k:knd) (p:range) = 
    match args with 
        | [] -> t1
        | _ -> mk_Typ_app (t1, args) k p
let extend_typ_app ((t:typ), (arg:arg)) (k:knd) p = match t.n with 
    | Typ_app(h, args) -> mk_Typ_app(h, args@[arg]) k p
    | _ -> mk_Typ_app(t, [arg]) k p
let mk_Typ_lam      ((b:binders),(t:typ)) (k:knd) (p:range) = {
    n=(match b with [] -> failwith "Empty binders!" | _ -> Typ_lam(b, t));
    tk=k;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
}
let mk_Typ_lam'      ((b:binder), (t2:typ)) (k:knd) (p:range) = {
    n=(match t2.n with Typ_lam(binders, body) -> Typ_lam(b::binders, body) | _ -> Typ_lam([b], t2));
    tk=k;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
    
}
let mk_Typ_ascribed' ((t:typ),(k:knd)) (k':knd) (p:range) = {
    n=Typ_ascribed(t, k);
    tk=k';
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
    
}
let mk_Typ_ascribed ((t:typ),(k:knd)) (p:range) = mk_Typ_ascribed' (t, k) k p

let mk_Typ_meta'    (m:meta_t) (k:knd) p = 
    {n=Typ_meta m;
     tk=k;
     pos=p;
     uvs=mk_uvs(); fvs=mk_fvs();
    }
let mk_Typ_meta     (m:meta_t) = match m with 
    | Meta_pattern(t, _) 
    | Meta_named(t, _)
    | Meta_labeled(t, _, _) 
    | Meta_refresh_label(t, _, _) -> mk_Typ_meta' m t.tk t.pos 

let mk_Typ_uvar'     ((u:uvar_t),(k:knd)) (k':knd) (p:range) = {
    n=Typ_uvar(u, k);
    tk=k';
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
    
}
let mk_Typ_uvar (u, k) p = mk_Typ_uvar' (u, k) k p 
let mk_Typ_delayed  ((t:typ),(s:subst_t),(m:memo<typ>)) (k:knd) (p:range) = {
    n=(match t.n with Typ_delayed _ -> failwith "NESTED DELAYED TYPES!" | _ -> Typ_delayed(t, s, m));
    tk=k;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
}
let mk_Typ_unknown  = {n=Typ_unknown; pos=dummyRange; tk=mk_Kind_unknown; uvs=mk_uvs(); fvs=mk_fvs()}

let mk_Total t = {
    n=Total t;
    tk=();
    pos=t.pos;
    uvs=mk_uvs(); fvs=mk_fvs();
}
let mk_Comp (ct:comp_typ) = 
    {n=Comp ct;
     tk=();
     pos=ct.result_typ.pos;
     uvs=mk_uvs(); fvs=mk_fvs();
}
let mk_Exp_bvar (x:bvvar) (t:typ) p = {
    n=Exp_bvar x;
    tk=t;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
}
let mk_Exp_fvar ((x:fvvar),(b:bool)) (t:typ) p = {
    n=Exp_fvar(x, b);
    tk=t;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
} 
let mk_Exp_constant (s:sconst) (t:typ) p = {
    n=Exp_constant s;
    tk=t;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
} 
let mk_Exp_abs ((b:binders),(e:exp)) (t':typ) p = {
    n=(match b with [] -> failwith "abstraction with no binders!" | _ -> Exp_abs(b, e));
    tk=t';
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
}
let mk_Exp_abs' ((b:binders),(e:exp)) (t':typ) p = {
    n=(match b, e.n with 
        | _, Exp_abs(binders, body) -> Exp_abs(b@binders, body) 
        | [], _ -> failwith "abstraction with no binders!"
        | _ -> Exp_abs(b, e));
    tk=t';
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
}
let mk_Exp_app ((e1:exp),(args:args)) (t:typ) p = {
    n=(match args with [] -> failwith "Empty args!" | _ -> Exp_app(e1, args));
    tk=t;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
}
let mk_Exp_app_flat ((e1:exp), (args:args)) (t:typ) p =
    match e1.n with 
        | Exp_app(e1', args') -> mk_Exp_app(e1', args'@args) t p
        | _ -> mk_Exp_app(e1, args) t p
let mk_Exp_app' ((e1:exp), (args:list<arg>)) (t:typ) (p:range) = 
    match args with 
        | [] -> e1
        | _ -> mk_Exp_app (e1, args) t p
let rec pat_vars p = match p.v with
  | Pat_cons(_, ps) -> 
    let vars = List.collect pat_vars ps in 
    if vars |> nodups (fun x y -> match x, y with 
      | Inl x, Inl y -> bvd_eq x y
      | Inr x, Inr y -> bvd_eq x y
      | _ -> false) 
    then vars
    else raise (Error("Pattern variables may not occur more than once", p.p))
  | Pat_var x -> [Inr x.v]
  | Pat_tvar a -> [Inl a.v]
  | Pat_disj ps -> 
    let vars = List.map pat_vars ps in 
    if not (List.tl vars |> Util.for_all (Util.set_eq order_bvd (List.hd vars)))
    then 
      let vars = Util.concat_l ";\n" (vars |> 
          List.map (fun v -> Util.concat_l ", " (List.map (function 
            | Inr x -> x.ppname.idText
            | Inl x -> x.ppname.idText) v))) in
      raise (Error(Util.format1 "Each branch of this pattern binds different variables: %s" vars, p.p))
    else List.hd vars
  | Pat_dot_term _
  | Pat_dot_typ _
  | Pat_wild _
  | Pat_twild _
  | Pat_constant _ -> []

let mk_Exp_match ((e:exp),(pats:list<(pat * option<exp> * exp)>)) (t:typ) p = 
    {
       n=Exp_match(e, pats);
       tk=t;
       pos=p;
       uvs=mk_uvs(); fvs=mk_fvs();
    } 
let mk_Exp_ascribed' ((e:exp),(t:typ)) (t':typ) p = {
    n=Exp_ascribed(e, t);
    tk=t';
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
    
}
let mk_Exp_ascribed ((e:exp),(t:typ)) p = mk_Exp_ascribed' (e, t) t p
let mk_Exp_let ((lbs:letbindings),(e:exp)) (t:typ) p = 
   {
    n=Exp_let(lbs, e);
    tk=t;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
   }

let mk_Exp_uvar' ((u:uvar_e),(t:typ)) (t':typ) p = {
    n=Exp_uvar(u, t);
    tk=t';
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
    
}
let mk_Exp_uvar  ((u:uvar_e),(t:typ)) p = mk_Exp_uvar' (u, t) t p

let mk_Exp_delayed ((e:exp),(s:subst_t),(m:memo<exp>)) (t:typ) p = {
    n=Exp_delayed(e, s, m);
    tk=t;
    pos=p;
    uvs=mk_uvs(); fvs=mk_fvs();
    
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
      | Meta_datainst(e, _)  -> mk_Exp_meta' m e.tk e.pos

let mk_subst (s:subst) = s
let extend_subst x s : subst = x::s
let argpos (x:arg) = match x with
    | Inl t, _ -> t.pos
    | Inr e, _ -> e.pos
    
let tun   = mk_Typ_unknown
let kun   = mk_Kind_unknown
let ktype = mk_Kind_type
let keffect = mk_Kind_effect
let null_id  = mk_ident("_", dummyRange)
let null_bvd = {ppname=null_id; realname=null_id}
let null_bvar k = {v=null_bvd; sort=k; p=dummyRange}
let t_binder (a:btvar) : binder = Inl a, false
let v_binder (a:bvvar) : binder = Inr a, false
let null_t_binder t : binder = Inl (null_bvar t), false
let null_v_binder t : binder = Inr (null_bvar t), false
let targ t : arg = Inl t, false
let varg v : arg = Inr v, false
let is_null_bvd (b:bvdef<'a>) = b.realname.idText = null_id.idText
let is_null_bvar (b:bvar<'a,'b>) = is_null_bvd b.v
let is_null_binder (b:binder) = match b with
    | Inl a, _ -> is_null_bvar a
    | Inr x, _ -> is_null_bvar x

let freevars_of_binders (bs:binders) : freevars = 
    bs |> List.fold_left (fun out -> function
        | Inl btv, _ -> {out with ftvs=Util.set_add btv out.ftvs}
        | Inr bxv, _ -> {out with fxvs=Util.set_add bxv out.fxvs}) no_fvs

let binders_of_list fvs : binders = (fvs |> List.map (fun t -> t, false))
let binders_of_freevars fvs = 
   (Util.set_elements fvs.ftvs |> List.map t_binder)@(Util.set_elements fvs.fxvs |> List.map v_binder)
