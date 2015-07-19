// Learn more about F# at http://fsharp.net
// See the 'F# Tutorial' project for more help.
#light "off"
module Microsoft.FStar.Backends.ML.ExtractTyp
open Prims
open Microsoft.FStar.Absyn
open Microsoft.FStar.Backends.ML.Syntax
open Microsoft.FStar.Util
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar
open Microsoft.FStar.Tc.Normalize
open Microsoft.FStar.Absyn.Print
open Microsoft.FStar.Backends.ML.Env

let binderIsExp (bn:binder): bool = is_inr (fst bn)

let rec argsIsExp (k:knd') (typeName : string) : list<bool> =
match k with
| Kind_type -> []
| Kind_arrow (bs,r) -> List.append (List.map binderIsExp bs) (argsIsExp r.n typeName)
| Kind_delayed (k, _ ,_) -> failwith "extraction.numIndices : expected a compressed argument"
| _ -> failwith ("unexpected signature of inductive type" ^ typeName) 

let  numIndices (k:knd') (typeName : string) : int = List.length (argsIsExp k typeName)

let mlty_of_isExp (b:bool) : mlty =
    if b then erasedContent else unknownType


(*copied from ocaml-strtrans.fs*)
let prependTick (x,n) = if Util.starts_with x "'" then (x,n) else ("'"^x,n)

let translate_eff g l : e_tag = 
    if lid_equals l Const.effect_PURE_lid //TODO : what about effect abbreviations?
    then MayErase 
    else Keep

(*generates inp_1 -> inp_2 -> ... inp_n -> out *)
let rec curry (inp: (list<mlty>)) (erase : e_tag) (out: mlty) =
  match inp with
  | [] -> out
  | h::tl -> MLTY_Fun (h, erase, curry tl erase out) //TODO: Fix the e_tag

(*
  Below, "the thesis" refers to:
  Letouzey, P. “Programmation Fonctionnelle Certifiée – L’extraction de Programmes Dans L’assistant Coq.” Université Paris-Sud, 2004.
  http://www.pps.univ-paris-diderot.fr/~letouzey/download/these_letouzey_English.ps.gz
*)

(*\box type in the thesis, to be used to denote the result of erasure of logical (computationally irrelevant) content.
  The actual definiton is a bit complicated, because we need for any x, \box x to be convertible to \box.
*)


let convRange (r:Range.range) : int = 0 (*FIX!!*)
let convIdent (id:ident) : mlident = (id.idText ,(convRange id.idRange))
    
type argTransform = arg -> Tot<option<arg>> (*none indicates that this argument should be deleted*)
type nthArgTransform = int -> Tot<argTransform> (* f n is the argtransform for the nth argument (of a type constant)*)
let idArgTransform :argTransform = fun a -> Some a
type nthArgTransforms = lident (*name of a constant*) -> Tot<nthArgTransform>
 

type context = env

(*
let tyVarKind (bv : bvvar) : knd = {n=Kind_type; tk=None; pos= bv.p; fvs =None; uvs = None}
let bvvar2btvar (bv : bvvar) : btvar = {v=bv.v; sort = Kind_type ; p=bv.p} *)


(* vars in tyVars will have type Type, irrespective of that types they had in F*. This is to match the limitations of  OCaml*)


let btvar2mlident (btv: btvar) : mlident =  (prependTick (convIdent btv.v.ppname)) 


let extendContextWithRepAsTyVar (b : either<btvar,bvvar> * either<btvar,bvvar>) (c:context): context = 
match b with
| (Inl bt, Inl btr) -> 
           //printfn "mapping from %A\n" btr.v.realname;
           //printfn "to %A\n" bt.v.realname;
   extend_ty c btr (Some ((MLTY_Var (btvar2mlident bt))))
| (Inr bv, Inr _ ) -> extend_bv c bv ([], erasedContent)
| _ -> failwith "Impossible case"


let extendContextWithRepAsTyVars (b : list< (either<btvar,bvvar> * either<btvar,bvvar>) > ) (c:context): context = 
   List.fold_right (extendContextWithRepAsTyVar) b c (*TODO: is the fold in the right direction? check *)

let extendContextAsTyvar (availableInML : bool) (b : either<btvar,bvvar>) (c:context): context = 
match b with
| (Inl bt) -> extend_ty c bt (Some (if availableInML then (MLTY_Var (btvar2mlident bt)) else unknownType))
//if availableInML then (extend_ty c bt (Some ( (MLTY_Var (btvar2mlident bt))))) else (extend_hidden_ty c bt unknownType)
| (Inr bv) -> extend_bv c bv ([], erasedContent)

let extendContext (c:context) (tyVars : list<either<btvar,bvvar>>) : context = 
   List.fold_right (extendContextAsTyvar true) (tyVars) c (*TODO: is the fold in the right direction? check *)


//let deltaUnfold (i : lident) (c: context) : (option<typ>) = 
//lookup 
//None (*TODO: FIX!!*)

(*The thesis defines a type scheme as "something that becomes a type when enough arguments (possibly none?) are applied to it" ,  e.g. vector, list.
    I guess in F*, these include Inductive types and type abbreviations.
    Formal definition is @ Definition 8, Sec. 1.2.3
      *)
let isTypeScheme (i : lident) (c: context) : bool = true  (*TODO: FIX!! really? when would a type constant not be a type scheme? *)


let lident2mlpath (l:lident) : mlpath =
  ( List.map (fun x -> x.idText) l.ns , l.ident.idText)


let preProcType  (c:context) (ft:typ) : typ =  
    let ft =  (Util.compress_typ ft) in
    Tc.Normalize.norm_typ [Tc.Normalize.Beta] c.tcenv ft

let extractTyVar (c:context) (btv : btvar) = (lookup_ty c (Inl btv))

(* (if (contains c btv) then MLTY_Var (btvar2mlident btv) else unknownType) *)


let rec extractType' (c:context) (ft:typ') : mlty = 
(*the \hat{\epsilon} function in the thesis (Sec. 3.3.5) *)
(* First \beta, \iota and \zeta reduce ft. Do require the caller to do so.
    Since F* does not have SN, one has to be more careful for the termination argument.
    Because OCaml does not support computations in Type, unknownType is supposed to be used if they are really unaviodable.
    The classic example is the type : T b \def if b then nat else bool. If we dont compute, T true will extract to unknownType.
    Why not \delta? I guess the reason is that unfolding definitions will make the resultant OCaml code less readable.
    However in the Typ_app case,  \delta reduction is done as the second-last resort, just before giving up and returing unknownType;
        a bloated type is atleast as good as unknownType?
    An an F* specific example, unless we unfold Mem x pre post to StState x wp wlp, we have no idea that it should be translated to x
*)
match ft with // assume ft is compressed. is there a compresser for typ'?
  | Typ_btvar btv -> extractTyVar c btv
  (*it is not clear whether description in the thesis covers type applications with 0 args. However, this case is needed to translate types like nnat, and so far seems to work as expected*)
  | Typ_const ftv ->  extractTyConstApp c ftv []
  | Typ_fun (bs, codomain) -> 
        let (bts, newC) = extractBindersTypes c bs in
        (let codomainML, erase = (extractComp  newC codomain) in 
        if  (codomainML = erasedContent) 
        then erasedContent (*perhaps this is not needed, or should be done in a later phase*)
        else  (curry bts erase codomainML))

  | Typ_refine (bv (*var and unrefined type*) , _ (*refinement condition*)) -> extractTyp c bv.sort

  (*can this be a partial type application? , i.e can the result of this application be something like Type -> Type, or nat -> Type? : Yes *)
  (* should we try to apply additional arguments here? if not, where? FIX!! *)
  | Typ_app (ty, arrgs) ->
    (match (Util.compress_typ ty).n with
        | Typ_btvar btv ->  extractTyVar c btv
            (*the args are thrown away, because in OCaml, type variables have type Type and not something like -> .. -> .. Type *)
        | Typ_const ftv -> extractTyConstApp c ftv arrgs            
        | Typ_app (tyin, argsin) -> extractType' c (Typ_app (tyin,(List.append argsin arrgs)))
        | _ -> unknownType)

  | Typ_lam  (bs,ty) ->  (* (sch) rule in \hat{\epsilon} *)
         let (bts, c) = extractBindersTypes c bs in
            extractTyp c ty

  | Typ_ascribed (ty,_)  -> extractTyp c ty
  | Typ_meta _ -> failwith "NYI"
  | Typ_uvar _ -> failwith "NYI"
  | Typ_delayed _  -> failwith "expected the argument to be compressed"
  |   _ -> failwith "NYI. replace this with unknownType if you know the consequences"
and getTypeFromArg (c:context) (a:arg) : mlty =
match (fst a) with
| Inl ty -> extractTyp c ty
| Inr _ -> erasedContent 
and extractTyConstApp (c:context) (ftv:ftvar) (ags : args) =
            match  (isTypeScheme ftv.v c)  with // when is something not a type scheme? if None, then no need to delta unfold.
            //Perhaps this issue is Coq specific where there is no clear distinction between terms and types, and there is no distinction b/w term and type abbreviations.
            // So, one might need to unfold abbreviations which unfold to types.
             | true -> 
                 let mlargs = List.map (getTypeFromArg c) ags in
                 let k = ftv.sort in
                 let ar =  argsIsExp k.n ftv.v.str in
                 //assert (List.length ar >= List.length mlargs);
                 let (_, missingArgs) = Util.first_N (List.length mlargs) ar in
                 let argCompletion =  List.map mlty_of_isExp missingArgs in
                    (MLTY_Named (List.append mlargs argCompletion,(lident2mlpath ftv.v)))
             | false -> failwith "this case was not anticipated"
                 (* match  (deltaUnfold ftv.v c) with
                 | Some tyu ->  extractTyp c tyu
                 | None -> unknownType
                 *)

(* Return the new context, where this binder IS in scope. Because we wish to call the F* normalizer, the context should always be up-to-date*)
and extractBinderType  (c:context) (bn : binder): mlty * context = 
match bn with
| (Inl btv,_) -> (extractKind c (btv.sort), (extendContextAsTyvar false (Inl btv) c))
| (Inr bvv,_) -> (extractTyp c (bvv.sort), (extendContextAsTyvar false (Inr bvv) c))

and extractBindersTypes  (c:context) (bs : list<binder>): list<mlty> * context =
    (fun (x,c) -> (List.rev x,c)) (List.fold_left (fun (lt,cp) b -> let (nt, nc)= extractBinderType cp b in ((nt::lt),nc))  ([],c) bs)

and extractTyp  (c:context) (ft:typ) : mlty = 
    let ft =  (preProcType c ft) in extractType' c ft.n

and extractKind (c:context) (ft:knd) : mlty = erasedContent
and extractComp  (c:context) (ft:comp) : mlty * e_tag = extractComp' c (ft.n) 
and extractComp'  (c:context) (ft:comp') : mlty * e_tag =
match  ft with
  | Total ty -> (extractTyp c ty, MayErase)
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
  cargs : binders (*will this list always be empty? it has always been empty so far*)
}
type inductiveTypeFam = {
  tyName: lident;
  k : knd;
  tyBinders: binders;
  constructors : list<inductiveConstructor>
}

(*the second element of the returned pair is the unconsumed part of sigs*)
let parseInductiveConstructor (sigs : list<sigelt>) : (inductiveConstructor * list<sigelt>) =
match sigs with
| (Sig_datacon (l, (*codomain*) t ,(_,cargs(*binders*),_),_,_,_))::tlsig ->
     ({ cname = l ; ctype = t; cargs =[] }, tlsig)
| h::_ -> failwith (Util.format1 "unexpected : %s\n" (Print.sigelt_to_string h)) //"incorrect sigelt provided to parseInductiveConstructor"

let rec parseInductiveConstructors (sigs : list<sigelt>) (n: int) : (list<inductiveConstructor> * list<sigelt>) =
    if (0<n)
    then 
         let (ic, tsigs) = parseInductiveConstructor sigs in 
         let (ics, ttsig) = (parseInductiveConstructors tsigs (n-1)) in 
            (ic::ics, ttsig)
    else
        ([], sigs)

(*the second element of the returned pair is the unconsumed part of sigs*)
let rec parseInductiveTypesFromSigBundle
    (sigs : list<sigelt>)  : list<inductiveTypeFam>  =
match sigs with
| (Sig_tycon (l,bs,kk,_,constrs,_,_))::tlsig -> 
     //printfn "%A\n" ((List.map (fun (x:lident) -> x.ident.idText) constrs));
    let (indConstrs(*list<inductiveConstructor>*), ttlsig) = parseInductiveConstructors tlsig (List.length constrs) in
     ({tyName = l; k = kk; tyBinders=bs; constructors=indConstrs})::(parseInductiveTypesFromSigBundle ttlsig)
| [] -> []
| se::tlsig -> failwith (Util.format1 "unexpected : %s\n" (Print.sigelt_to_string_short se)) //;(parseInductiveTypesFromSigBundle tlsig) //TODO : debug and remove
| _ -> failwith "incorrect input provided to parseInductiveTypeFromSigBundle"


let rec argTypes  (t: mlty) : list<mlty> =
match t with
| MLTY_Fun (a,_,b) -> a::(argTypes b)
| _ -> []
 
let lident2mlsymbol (l:lident) : mlsymbol = l.ident.idText

let bindersOfFuntype (n:int) (t:typ) : list<binder> * (*residual type*) typ' = 
let tc = ((Util.compress_typ t).n) in
match tc with
| Typ_fun (lb,cp) -> let (ll,lr)= Util.first_N n lb in  (ll, Typ_fun (lr,cp)) // is this risky? perhaps not because we will manually put the removed binders into the context, before typechecking
// but we are removing the implicit arguments corresponding to the type binders. Is that always safe? In OCaml, is there no way to say (nil @ nat)? 
// Perhaps it is not needed, because OCaml can implicitly put a type lambda (generalize)?
| _ -> assert (n=0); ([],tc) 
    //printfn "%A\n" (ctor.ctype);
    //failwith "was expecting a function type"

let rec zipUnequal (la : list<'a>) (lb : list<'b>) : list<('a * 'b)> =
match  (la, lb) with
| (ha::ta, hb::tb) -> ((ha,hb)::(zipUnequal ta tb))
| _ -> []

let mlTyIdentOfBinder (b : binder) = prependTick (convIdent (binderPPnames b))

let extractCtor (tyBinders : list<binder>) (c:context) (ctor: inductiveConstructor):  context * (mlsymbol * list<mlty>) =
   if (0< List.length ctor.cargs)
   then (failwith "cargs is unexpectedly non-empty. This is a design-flaw, please report.")
   else 
        (let (lb, tr) = bindersOfFuntype (List.length tyBinders) ctor.ctype in 
        let lp = List.zip tyBinders lb in
        //assert (List.length tyBinders = List.length lp);
        let newC = extendContextWithRepAsTyVars (List.map (fun (x,y) -> (fst x, fst y)) lp) c in
        let mlt = extractType' newC tr in
        let tys = (List.map mlTyIdentOfBinder tyBinders, mlt) in
        let fvv = mkFvvar ctor.cname ctor.ctype in 
            // fprint1 "(* extracting the type of constructor %s\n" (lident2mlsymbol ctor.cname);
           // fprint1 "%s\n" (typ_to_string ctor.ctype);
            // printfn "%A *)\n" (tys);
        (extend_fv c fvv tys, (lident2mlsymbol ctor.cname, argTypes mlt)))

(*indices get collapsed to unit, so all we need is the number of index arguments.
  We will use dummy type variables for these in the dectaration of the inductive type.
  On each application, we will replace the argument with unit.
  
  Currently, no attempt is made to convert an index to a parameter.
  It seems to be good practice for programmers to not use indices when parameters suffice.
   *)
let dummyIdent (n:int) : mlident = ("'dummyV"^(Util.string_of_int n), 0)

let rec firstNNats (n:int) : list<int> =
if (0<n)
  then (n::(firstNNats (n-1)))
  else []

let dummyIndexIdents (n:int) : list<mlident> = List.map dummyIdent (firstNNats n)

let extractInductive (c:context) (ind: inductiveTypeFam ) :  context*mltydecl =
        let newContext = c in // (extendContext c (mfst ind.tyBinders)) in
        let nIndices = numIndices (Util.compress_kind ind.k).n ind.tyName.ident.idText in
        let (nc, tyb) = (Util.fold_map (extractCtor ind.tyBinders) newContext ind.constructors) in
        let mlbs = List.append (List.map mlTyIdentOfBinder ind.tyBinders) (dummyIndexIdents nIndices) in
        nc, [(lident2mlsymbol ind.tyName,  mlbs , Some (MLTD_DType tyb))]

let mfst = List.map fst

let rec headBinders (c:context) (t:typ) : (context * binders * typ (*residual type*)) = 
match (preProcType c t).n with
| Typ_lam (bs,t) -> let c,rb,rresidualType = headBinders (extendContext c (mfst bs)) t in
                     c,(List.append bs rb), rresidualType
| _ -> (c,[],t)



(*similar to the definition of the second part of \hat{\epsilon} in page 110*)
(* \pi_1 of returned value is the exported constant*)
let extractSigElt (c:context) (s:sigelt) : context * list<mltydecl> =
    match s with
    | Sig_typ_abbrev (l,bs,_,t,_,_) -> 
        let c = (extendContext c (mfst bs)) in
        let c, headBinders, residualType = headBinders c (preProcType c t) in
        let bs=List.append bs headBinders in
        let t=residualType in
        let tyDecBody = MLTD_Abbrev (extractTyp c t) in
                //printfn "type is %A\n" (t);
        let td = [(mlsymbolOfLident l, List.map mlTyIdentOfBinder bs , Some tyDecBody)] in
        let c = Env.extend_tydef c td in
        c, [td]
         (*type l idents = tyDecBody*)
         //Util.subst

    | Sig_bundle (sigs, _, _ ,_) -> 
        //let xxxx = List.map (fun se -> fprint1 "%s\n" (Util.format1 "sig bundle: : %s\n" (Print.sigelt_to_string se))) sigs in
        let inds = parseInductiveTypesFromSigBundle sigs in
         (Util.fold_map extractInductive c inds)
        //let k = lookup_typ_lid c ind.tyName in
    | _ -> c, []

let extractTypeDefnsAux (c: context) (sigs:list<sigelt>) : context * list<mltydecl> =
   let c, l = Util.fold_map extractSigElt c sigs in
   c, List.flatten l
 
let mkContext (e:Tc.Env.env) : context =
    { tcenv = e; gamma =[] ; tydefs =[]}

let extractTypeDefns (sigs:list<sigelt>) (e: Tc.Env.env): context * list<mltydecl> =
    extractTypeDefnsAux (mkContext e) sigs 
    
