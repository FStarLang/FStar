(*
   Copyright 2008-2015 Abhishek Anand, Nikhil Swamy and Microsoft Research

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
module FStar.Extraction.ML.ExtractTyp
open Prims
open FStar.Absyn
open FStar.Extraction.ML.Syntax
open FStar.Util
open FStar.Tc.Env
open FStar.Absyn.Syntax
open FStar
open FStar.Tc.Normalize
open FStar.Absyn.Print
open FStar.Extraction.ML.Env

let binderIsExp (bn:binder): bool = is_inr (fst bn)

let rec argIsExp (k:knd) (typeName : string) : list<bool> =
    match (Util.compress_kind k).n with
        | Kind_type -> []
        | Kind_arrow (bs,r) -> List.append (List.map binderIsExp bs) (argIsExp r typeName)
        | Kind_delayed (k, _ ,_) -> failwith "extraction.numIndices : expected a compressed argument"
        | Kind_abbrev(_, k) -> argIsExp k typeName
        | _ -> failwith ("unexpected signature of inductive type" ^ typeName)

let  numIndices (k:knd) (typeName : string (*this argument is just for debugging purposes*))
  : int = List.length (argIsExp k typeName)

(*used for completion of missing arguments to type constructors*)
let mlty_of_isExp (b:bool) : mlty =
    if b then erasedContent else unknownType


let delta_norm_eff =
    let cache = Util.smap_create 20 in
    let rec delta_norm_eff g (l:lident) =
        match Util.smap_try_find cache l.str with
            | Some l -> l
            | None ->
              let res = match Tc.Env.lookup_effect_abbrev g.tcenv l with
                | None -> l
                | Some (_, c) -> delta_norm_eff g (Util.comp_effect_name c) in
              Util.smap_add cache l.str res;
              res in
    delta_norm_eff

let translate_eff g l : e_tag =
    let l = delta_norm_eff g l in
    if lid_equals l Const.effect_PURE_lid 
    then E_PURE
    else if lid_equals l Const.effect_GHOST_lid
    then E_GHOST
    else E_IMPURE

(*generates inp_1 -> E_PURE (inp_2 -> ...  E_PURE (inp_n -> f out)) *)
let rec curry (inp: (list<mlty>)) (f : e_tag) (out: mlty) =
  match inp with
    | [] -> out
    | [h] -> MLTY_Fun (h, f, out)
    | h1::h2::tl -> MLTY_Fun(h1, E_PURE, curry (h2::tl) f out)

(*
  Below, "the thesis" refers to:
  Letouzey, P. “Programmation Fonctionnelle Certifiée – L’extraction de Programmes Dans L’assistant Coq.” Université Paris-Sud, 2004.
  http://www.pps.univ-paris-diderot.fr/~letouzey/download/these_letouzey_English.ps.gz
*)

(*\box type in the thesis, to be used to denote the result of erasure of logical (computationally irrelevant) content.
  The actual definiton is a bit complicated, because we need for any x, \box x to be convertible to \box.
*)

type context = env


let extendContextWithRepAsTyVar (b : either<btvar,bvvar> * either<btvar,bvvar>) (c:context): context =
    match b with
        | (Inl bt, Inl btr) ->
                   //printfn "mapping from %A\n" btr.v.realname;
                   //printfn "to %A\n" bt.v.realname;
           extend_ty c btr (Some ((MLTY_Var (btvar_as_mltyvar bt))))
        | (Inr bv, Inr _ ) -> extend_bv c bv ([], erasedContent) false false
        | _ -> failwith "Impossible case"


let extendContextWithRepAsTyVars (b : list< (either<btvar,bvvar> * either<btvar,bvvar>) > ) (c:context): context =
   List.fold_right (extendContextWithRepAsTyVar) b c (*TODO: is the fold in the right direction? check *)

let extendContextAsTyvar (availableInML : bool) (b : either<btvar,bvvar>) (c:context): context =
    match b with
        | (Inl bt) -> extend_ty c bt (Some (if availableInML then (MLTY_Var (btvar_as_mltyvar bt)) else unknownType))
        //if availableInML then (extend_ty c bt (Some ( (MLTY_Var (btvar2mlident bt))))) else (extend_hidden_ty c bt unknownType)
        | (Inr bv) -> extend_bv c bv ([], erasedContent) false false

let extendContext (c:context) (tyVars : list<either<btvar,bvvar>>) : context =
   List.fold_right (extendContextAsTyvar true) (tyVars) c (*TODO: is the fold in the right direction? check *)

(*The thesis defines a type scheme as "something that becomes a type when enough arguments (possibly none?) are applied to it" ,  e.g. vector, list.
    I guess in F*, these include Inductive types and type abbreviations.
    Formal definition is @ Definition 8, Sec. 1.2.3
      *)
let isTypeScheme (i : lident) (c: context) : bool = true  (*TODO: FIX!! really? when would a type constant not be a type scheme? *)


let preProcType  (c:context) (ft:typ) : typ =
    let ft =  (Util.compress_typ ft) in
    Tc.Normalize.norm_typ [Tc.Normalize.Beta] c.tcenv ft

let extractTyVar (c:context) (btv : btvar) = lookup_tyvar c btv


(*the \hat{\epsilon} function in the thesis (Sec. 3.3.5) *)
(* First \beta, \iota and \zeta reduce ft.
    Since F* does not have SN, one has to be more careful for the termination argument.
    Because OCaml does not support computations in Type, unknownType is supposed to be used if they are really unaviodable.
    The classic example is the type : T b \def if b then nat else bool. If we dont compute, T true will extract to unknownType.
    Why not \delta? I guess the reason is that unfolding definitions will make the resultant OCaml code less readable.
    However in the Typ_app case,  \delta reduction is done as the second-last resort, just before giving up and returing unknownType;
        a bloated type is atleast as good as unknownType?
    An an F* specific example, unless we unfold Mem x pre post to StState x wp wlp, we have no idea that it should be translated to x
*)

let rec extractTyp  (c:context) (ft:typ) : mlty =
    let ft =  (preProcType c ft) in
    match ft.n with // assume ft is compressed. is there a compresser for typ'?
      | Typ_btvar btv -> extractTyVar c btv
      (*it is not clear whether description in the thesis covers type applications with 0 args. However, this case is needed to translate types like nnat, and so far seems to work as expected*)

      | Typ_const ftv ->  extractTyConstApp c ftv []

      | Typ_fun (bs, codomain) ->
        let (bts, newC) = extractBindersTypes c bs in
        let codomainML, erase = extractComp  newC codomain in
        curry bts erase codomainML

      | Typ_refine (bv (*var and unrefined type*) , _ (*refinement condition*)) -> extractTyp c bv.sort

      (*can this be a partial type application? , i.e can the result of this application be something like Type -> Type, or nat -> Type? : Yes *)
      (* should we try to apply additional arguments here? if not, where? FIX!! *)
      | Typ_app (ty, arrgs) ->
        let ty = preProcType c ty in
        let res = match ty.n with
            | Typ_btvar btv ->  extractTyVar c btv
                (*the args are thrown away, because in OCaml, type variables have type Type and not something like -> .. -> .. Type *)
            | Typ_const ftv -> extractTyConstApp c ftv arrgs
            | Typ_app (tyin, argsin) -> extractTyp c (Util.mkTypApp tyin (List.append argsin arrgs) ty)
            | _ -> unknownType in
        res

      | Typ_lam  (bs,ty) ->  (* (sch) rule in \hat{\epsilon} *)
        let (bts, c) = extractBindersTypes c bs in
        extractTyp c ty

      | Typ_ascribed (ty,_)  -> extractTyp c ty
      | Typ_meta mt -> extractMeta c mt
      | Typ_uvar _ -> unknownType
      | Typ_delayed _  -> failwith "expected the argument to be compressed"
      |   _ -> failwith "NYI. replace this with unknownType if you know the consequences"

and getTypeFromArg (c:context) (a:arg) : mlty =
    match (fst a) with
      | Inl ty -> extractTyp c ty
      | Inr _ -> erasedContent

and extractMeta (c:context) (mt:meta_t) : mlty = // TODO: check if this is the right way to extract metas
    match mt with
      | Meta_pattern (t,_)
      | Meta_named (t,_)
      | Meta_labeled (t,_,_, _)
      | Meta_refresh_label (t,_,_)
      | Meta_slack_formula (t,_,_) -> extractTyp c t


and extractTyConstApp (c:context) (ftv:ftvar) (ags : args) : mlty =
    if isTypeScheme ftv.v c
    then // when is something not a type scheme? if None, then no need to delta unfold.
         //Perhaps this issue is Coq specific where there is no clear distinction between terms and types, and there is no distinction b/w term and type abbreviations.
         // So, one might need to unfold abbreviations which unfold to types.
        let mlargs = List.map (getTypeFromArg c) ags in
        let k = ftv.sort in
        let ar =  argIsExp k ftv.v.str in
        //assert (List.length ar >= List.length mlargs);
        let (_, missingArgs) = Util.first_N (List.length mlargs) ar in
        let argCompletion =  List.map mlty_of_isExp missingArgs in
        (MLTY_Named (List.append mlargs argCompletion,(mlpath_of_lident ftv.v)))
    else failwith "this case was not anticipated"
            (* match  (deltaUnfold ftv.v c) with
            | Some tyu ->  extractTyp c tyu
            | None -> unknownType
            *)

(* Return the new context, where this binder IS in scope. Because we wish to call the F* normalizer, the context should always be up-to-date*)
and extractBinderType  (c:context) (bn : binder): mlty * context =
    match bn with
    | (Inl btv,_) -> (extractKind c (btv.sort), extendContextAsTyvar false (Inl btv) c)
    | (Inr bvv,_) -> (extractTyp c (bvv.sort), extendContextAsTyvar false (Inr bvv) c)

and extractBindersTypes  (c:context) (bs : list<binder>): list<mlty> * context =
    (fun (x,c) -> (List.rev x,c)) (List.fold_left (fun (lt,cp) b -> let (nt, nc)= extractBinderType cp b in ((nt::lt),nc))  ([],c) bs)

and extractKind (c:context) (ft:knd) : mlty = erasedContent
and extractComp  (c:context) (ft:comp) : mlty * e_tag = extractComp' c (ft.n)
and extractComp'  (c:context) (ft:comp') : mlty * e_tag =
    match ft with
      | Total ty -> (extractTyp c ty, E_PURE)
      | Comp cm -> (extractTyp c (cm.result_typ), translate_eff c cm.effect_name )


let binderPPnames (bn:binder): ident =
    match bn with
      | (Inl btv,_) -> btv.v.ppname
      | (Inr bvv,_) -> bvv.v.ppname

let binderRealnames (bn:binder): ident =
    match bn with
      | (Inl btv,_) -> btv.v.realname
      | (Inr bvv,_) -> bvv.v.realname


let mlsymbolOfLident (id : lident) : mlsymbol =
  id.ident.idText


(*just enough info to generate OCaml code; add more info as needed*)
type inductiveConstructor = {
  cname: lident;
  ctype : typ;
}
type inductiveTypeFam = {
  tyName: lident;
  k : knd;
  tyBinders: binders;
  constructors : list<inductiveConstructor>;
  qualifiers: list<Syntax.qualifier>
}

type typeAbbrev = {
  abTyName: lident; // this name cant just be tyName. make test gets confused with inductiveTypeFam because if the name of fields is same
  abTyBinders: binders;
  abBody : typ
}

let lookupDataConType (c:context) (sigb : sigelts) (l:lident)(*this sigbundle contains the constructors *) : typ =
    let tr =
      Util.find_map sigb (fun s ->
                    match s with
                    | Sig_datacon (l',t,(_, tps, _),quals,lids,_) -> 
                       if l=l' 
                       then let t = Absyn.Util.close_typ (List.map (fun (x, _) -> (x, Some Implicit)) tps) t in
                            Some t 
                       else None
                    | _ -> None
                    )  in must tr

let parseInductiveConstructors (c:context) (cnames: list<lident>) (sigb : sigelts) (*this sigbundle contains the constructors, but we look inside iff Tc.Env.lookpu_datacon fails*)
    : (list<inductiveConstructor>) =
    List.map (fun h -> { cname = h ; ctype = lookupDataConType c sigb h }) cnames

(*the second element of the returned pair is the unconsumed part of sigs*)
let rec parseInductiveTypesFromSigBundle
    (c: context) (sigs : sigelts) : list<inductiveTypeFam> * list<typeAbbrev> * list<inductiveConstructor> (*last item contains only the constructors for exceptions *)
     =
    match sigs with
        | [] -> [],[],[]

        | (Sig_tycon (l,bs,kk,_,constrs,qs,_))::tlsig ->
             //printfn "%A\n" ((List.map (fun (x:lident) -> x.ident.idText) constrs));
            let indConstrs(*list<inductiveConstructor>*) = parseInductiveConstructors c constrs tlsig in
            let inds,abbs,exns=(parseInductiveTypesFromSigBundle c tlsig) in
             ({tyName = l; k = kk; tyBinders=bs; constructors=indConstrs; qualifiers=qs})::inds, abbs,exns

        | Sig_datacon (l,_,tc,quals,lids,_)::tlsig ->
            if List.contains  ExceptionConstructor quals
            then let t = lookup_datacon c.tcenv l in // ignoring the type in the bundle. the typechecker env often has syntactically better types
                 (assert (List.isEmpty tlsig) ;
                  ([],[], [{cname=l; ctype=t}]))
            else [],[],[]      // unless this is an exception constructor, at this point we can stop because Nik said that all type type declarations come before data constructors.

        | (Sig_typ_abbrev (l,bs,_,t,_,_))::tlsig ->
           let inds,abbs, exns=(parseInductiveTypesFromSigBundle c tlsig) in
           inds, ({abTyName=l; abTyBinders=bs; abBody=t})::abbs, exns

        | se::tlsig -> failwith (Util.format1 "unexpected content in a  sig bundle : %s\n" (Print.sigelt_to_string se))

//failwith (Util.format1 "unexpected content in a  sig bundle : %s\n" (Print.sigelt_to_string se))


let rec argTypes  (t: mlty) : list<mlty> =
    match t with
      | MLTY_Fun (a,_,b) -> a::(argTypes b)
      | _ -> []

let lident2mlsymbol (l:lident) : mlsymbol = l.ident.idText

let totalType_of_comp (ft:comp) : typ =
    match ft.n with
      | Total ty -> ty
      | _ -> failwith "expected a total type. constructors of inductive types were assumed to be total"

let allBindersOfFuntype (c: context)  (t:typ) : list<binder> =
    let t = (preProcType c t) in
    match t.n with
        | Typ_fun (lb,cp) -> lb
        | _ -> []

//let allBindersOfInductiveCtor (c: context)  (ctorName: lident) : list<binder> =
    //allBindersOfFuntype ()


let bindersOfFuntype (c: context) (n:int) (t:typ) : list<binder> * (*residual type*) typ =
    let t = (preProcType c t) in
    match t.n with
        | Typ_fun (lb,cp) -> let (ll,lr)= Util.first_N n lb in
            if (List.isEmpty lr)
                then  (ll, totalType_of_comp cp)
                else   (ll, Util.mkTypFun lr cp t)
        // is this risky? perhaps not because we will manually put the removed binders into the context, before typechecking
        // but we are removing the implicit arguments corresponding to the type binders. Is that always safe? In OCaml, is there no way to say (nil @ nat)?
        // Perhaps it is not needed, because OCaml can implicitly put a type lambda (generalize)?
        | _ -> assert (n=0); ([],t)
        //printfn "%A\n" (ctor.ctype);
        //failwith "was expecting a function type"

let rec zipUnequal (la : list<'a>) (lb : list<'b>) : list<('a * 'b)> =
    match (la, lb) with
        | (ha::ta, hb::tb) -> ((ha,hb)::(zipUnequal ta tb))
        | _ -> []

let mlTyIdentOfBinder (b : binder) = prependTick (convIdent (binderPPnames b))

let extractCtor (tyBinders : list<binder>) (c:context) (ctor: inductiveConstructor):  context * (mlsymbol * list<mlty>) =
        (let (lb, tr) = bindersOfFuntype c (List.length tyBinders) ctor.ctype in
        assert (List.length lb = List.length tyBinders);
        let lp = List.zip tyBinders lb in
        //assert (List.length tyBinders = List.length lp);
        let newC = extendContextWithRepAsTyVars (List.map (fun (x,y) -> (fst x, fst y)) lp) c in
        let mlt = Util.eraseTypeDeep c (extractTyp newC tr) in
        let tys = (List.map mlTyIdentOfBinder tyBinders, mlt) in //MayErase, because constructors are always pure
        let fvv = mkFvvar ctor.cname ctor.ctype in
             //fprint1 "(* extracting the type of constructor %s\n" (lident2mlsymbol ctor.cname);
            // fprint1 "%s\n" (typ_to_string ctor.ctype);
             // printfn "%A *)\n" (tys);
        (extend_fv c fvv tys false, (lident2mlsymbol ctor.cname, argTypes mlt)))

(*indices get collapsed to unit, so all we need is the number of index arguments.
  We will use dummy type variables for these in the dectaration of the inductive type.
  On each application, we will replace the argument with unit.

  Currently, no attempt is made to convert an index to a parameter.
  It seems to be good practice for programmers to not use indices when parameters suffice.
   *)

let rec firstNNats (n:int) : list<int> =
    if (0<n)
    then (n::(firstNNats (n-1)))
    else []

let dummyIdent (n:int) : mlident = ("'dummyV"^(Util.string_of_int n), 0)
let dummyIndexIdents (n:int) : list<mlident> = List.map dummyIdent (firstNNats n)

let extractInductive (c:context) (ind: inductiveTypeFam ) :  context* (mlsymbol * mlidents * option<mltybody>) =
        let newContext = c in // (extendContext c (mfst ind.tyBinders)) in
        let nIndices = numIndices ind.k ind.tyName.ident.idText in
        let (nc, tyb) = (Util.fold_map (extractCtor ind.tyBinders) newContext ind.constructors) in
        let mlbs = List.append (List.map mlTyIdentOfBinder ind.tyBinders) (dummyIndexIdents nIndices) in
        let tbody = match Util.find_opt (function RecordType _ -> true | _ -> false) ind.qualifiers with
            | Some (RecordType ids) ->
              assert (List.length tyb = 1);
              let _, c_ty = List.hd tyb in
              assert (List.length ids = List.length c_ty);
              let fields = List.map2 (fun lid ty -> (lid.ident.idText, ty)) ids c_ty in
              MLTD_Record fields
            | _ -> MLTD_DType tyb in
        nc, (lident2mlsymbol ind.tyName,  mlbs , Some tbody)

let mfst x = List.map fst x

(*
  Source: type t (a:Type) = fun (x:a) -> (a -> t' a x)
  ML:     type ('a, 'dummy) t = unit -> 'a -> ('a, 'dummy) t'
*)
let rec headBinders (c:context) (t:typ) : (context * binders * typ (*residual type*)) =
    let t = (preProcType c t) in
        match t.n with
        | Typ_lam (bs,t) -> let c,rb,rresidualType = headBinders (extendContext c (mfst bs)) t in
                             c,(List.append bs rb), rresidualType
        | _ -> (c,[],t)


let extractTypeAbbrev (c:context) (tyab:typeAbbrev) : context * (mlsymbol  * mlidents * option<mltybody>) =
    let bs = tyab.abTyBinders in
    let t = tyab.abBody in
    let l = tyab.abTyName in
    let c = (extendContext c (mfst bs)) in
    (*Unlike in F*, type abbreviations in ML define type, and not, e.g. (n:nat) -> Type.
     So, we move all the binders from the body to the collection of formal parameters.
     However, the additional binders are not added to the context. This makes sense for term binders because in
     ML, types do not depend on terms. One could put type binders in the context. For now, the user should do this movement in F* land.
     *)
    let c, headBinders, residualType = headBinders c t in
    let bs=List.append bs headBinders in
    let t=residualType in
    let mlt = (extractTyp c t) in
    let mlt = Util.eraseTypeDeep c mlt in
    let tyDecBody = MLTD_Abbrev mlt in
            //printfn "type is %A\n" (t);
    let td = (mlsymbolOfLident l, List.map mlTyIdentOfBinder bs , Some tyDecBody) in
    let c = Env.extend_tydef c [td] in
    c, td

let extractExn (c:context) (exnConstr : inductiveConstructor) : (context * mlmodule1) =
    let mlt = extractTyp c exnConstr.ctype in
    let mlt = Util.eraseTypeDeep c mlt in
    let tys = [], mlt in //NS: Why are the arguments always empty?
    let fvv = mkFvvar exnConstr.cname exnConstr.ctype in
    let ex_decl  : mlmodule1 = MLM_Exn (lident2mlsymbol exnConstr.cname, argTypes mlt) in
    extend_fv c fvv tys false, ex_decl //this might need to be translated to OCaml exceptions

(*similar to the definition of the second part of \hat{\epsilon} in page 110*)
(* \pi_1 of returned value is the exported constant*)
let rec extractSigElt (c:context) (s:sigelt) : context * list<mlmodule1> =
    match s with
    | Sig_typ_abbrev (l,bs,_,t,quals,_) ->
        let c, tds = extractTypeAbbrev c ({abTyName=l; abTyBinders=bs; abBody=t}) in
        (c, (if quals |> List.contains Logic then [] else [MLM_Ty [tds]]))

    | Sig_bundle(sigs, [ExceptionConstructor], _, _) ->
        let _, _, exConstrs = parseInductiveTypesFromSigBundle c sigs in
        assert (List.length exConstrs = 1);
        let c, exDecl = extractExn c (List.hd exConstrs) in
        (c, [exDecl])

    | Sig_bundle (sigs, _, _ ,_) ->
        //let xxxx = List.map (fun se -> fprint1 "%s\n" (Util.format1 "sig bundle: : %s\n" (Print.sigelt_to_string se))) sigs in
        let inds, abbs, _ = parseInductiveTypesFromSigBundle c sigs in
        let c, indDecls = Util.fold_map extractInductive c inds in
        let c, tyAbDecls = Util.fold_map extractTypeAbbrev c abbs in
        (c, [MLM_Ty (indDecls@tyAbDecls)])

    | Sig_tycon (l, bs, k, _, _, quals, r) ->
        //Util.print_string ((Print.sigelt_to_string s)^"\n");
         if quals |> List.contains Assumption  &&
         not (quals |> Util.for_some (function Projector _ | Discriminator _ -> true | _ -> false))
         then let kbs, _ = Util.kind_formals k in 
              let se = Sig_typ_abbrev(l, bs@kbs, mk_Kind_type, Tc.Recheck.t_unit, quals, r) in
              extractSigElt c se 
         else c,[]

    | _ -> c, []


