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


let deltaUnfold (i : lident) (c: context) : (option<typ>) = None (*TODO: FIX!!*)

(*The thesis defines a type scheme as "something that becomes a type when enough arguments (possibly none?) are applied to it" ,  e.g. vector, list.
    I guess in F*, these include Inductive types and type abbreviations.
    Formal definition is @ Definition 8, Sec. 1.2.3
      *)
let isTypeScheme (i : lident) (c: context) : bool = true  (*TODO: FIX!! *)


let lident2mlpath (l:lident) : mlpath =
  ( (* List.map (fun x -> x.idText) l.ns *) [], l.ident.idText)



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

  | Typ_lam  _ -> unknownType
  | Typ_ascribed _  -> unknownType
  | Typ_meta _ -> unknownType
  | Typ_uvar _ -> unknownType
  | Typ_delayed _  -> failwith "expected the argument to be compressed"
  |   _ -> unknownType
and getTypeFromArg (c:context) (a:arg) : mlty =
match (fst a) with
| Inl ty -> extractTyp c ty
| Inr _ -> erasedContent 
and extractTyConstApp (c:context) (ftv:ftvar) (ags : args) =
            match  (isTypeScheme ftv.v c)  with
             | true -> 
                 let mlargs = List.map (getTypeFromArg c) ags in
                 let k = ftv.sort in
                 let ar =  argsIsExp k.n ftv.v.str in
                 //assert (List.length ar >= List.length mlargs);
                 let (_, missingArgs) = Util.first_N (List.length mlargs) ar in
                 let argCompletion =  List.map mlty_of_isExp missingArgs in
                    (MLTY_Named (List.append mlargs argCompletion,(lident2mlpath ftv.v)))
             | false -> 
                 (match  (deltaUnfold ftv.v c) with
                 | Some tyu ->  extractTyp c tyu
                 | None -> unknownType
                 )

(* Return the new context, where this binder IS in scope. Because we wish to call the F* normalizer, the context should always be up-to-date*)
and extractBinderType  (c:context) (bn : binder): mlty * context = 
match bn with
| (Inl btv,_) -> (extractKind c (btv.sort), (extendContextAsTyvar false (Inl btv) c))
| (Inr bvv,_) -> (extractTyp c (bvv.sort), (extendContextAsTyvar false (Inr bvv) c))

and extractBindersTypes  (c:context) (bs : list<binder>): list<mlty> * context =
    (fun (x,c) -> (List.rev x,c)) (List.fold_left (fun (lt,cp) b -> let (nt, nc)= extractBinderType cp b in ((nt::lt),nc))  ([],c) bs)

and extractTyp  (c:context) (ft:typ) : mlty = extractType' c (Util.compress_typ ft).n
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
| _ -> failwith "incorrect sigelt provided to parseInductiveConstructor"

let rec parseInductiveConstructors (sigs : list<sigelt>) (n: int) : (list<inductiveConstructor> * list<sigelt>) =
    if (0<n)
    then 
         let (ic, tsigs) = parseInductiveConstructor sigs in 
         let (ics, ttsig) = (parseInductiveConstructors tsigs (n-1)) in 
            (ic::ics, ttsig)
    else
        ([], sigs)

(*the second element of the returned pair is the unconsumed part of sigs*)
let parseInductiveTypeFromSigBundle
    (sigs : list<sigelt>)  : (inductiveTypeFam * list<sigelt>)  =
match sigs with
| (Sig_tycon (l,bs,kk,_,constrs,_,_))::tlsig -> 
    let (indConstrs(*list<inductiveConstructor>*), ttlsig) = parseInductiveConstructors tlsig (List.length constrs) in
     ({tyName = l; k = kk; tyBinders=bs; constructors=indConstrs}, ttlsig)
| _ -> failwith "incorrect input provided to parseInductiveTypeFromSigBundle"

let parseFirstInductiveType
    (s : sigelt)  : inductiveTypeFam  =
match s with
| Sig_bundle (sigs, _, _, _) -> fst (parseInductiveTypeFromSigBundle sigs)
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

let extractCtor (c:context) (tyBinders : list<binder>) (ctor: inductiveConstructor):  (mlsymbol * list<mlty>) =
   if (0< List.length ctor.cargs)
   then (failwith "cargs is unexpectedly non-empty. This is a design-flaw, please report.")
   else 
        (let (lb, tr) = bindersOfFuntype (List.length tyBinders) ctor.ctype in 
        let lp = List.zip tyBinders lb in
        //assert (List.length tyBinders = List.length lp);
        let newC = extendContextWithRepAsTyVars (List.map (fun (x,y) -> (fst x, fst y)) lp) c in
        let mlt = extractType' newC tr in
            // fprint1 "extracting the type of constructor %s\n" (lident2mlsymbol ctor.cname);
            //fprint1 "%s\n" (typ_to_string ctor.ctype);
            // printfn "%A\n" (ctor.ctype);
        (lident2mlsymbol ctor.cname, argTypes mlt))

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

let mfst = List.map fst
(*similar to the definition of the second part of \hat{\epsilon} in page 110*)
(* \pi_1 of returned value is the exported constant*)
let extractSigElt (c:context) (s:sigelt) : context * list<mltydecl> =
    match s with
    | Sig_typ_abbrev (l,bs,_,t,_,_) -> 
        let identsPP = List.map binderPPnames bs in
        let newContext = (extendContext c (mfst bs)) in
        let tyDecBody = MLTD_Abbrev (extractTyp newContext t) in
                //printfn "type is %A\n" (t);
        let td = [(mlsymbolOfLident l, List.map (fun x -> prependTick (convIdent x)) identsPP , Some tyDecBody)] in
        let c = Env.extend_tydef c td in
        c, [td]
         (*type l idents = tyDecBody*)

    | Sig_bundle _ -> 
        let ind = parseFirstInductiveType s in
        //let k = lookup_typ_lid c ind.tyName in
        let identsPP = List.map binderPPnames ind.tyBinders in
        let newContext = c in // (extendContext c (mfst ind.tyBinders)) in
        let nIndices = numIndices (Util.compress_kind ind.k).n ind.tyName.ident.idText in
        let tyDecBody = MLTD_DType (List.map (extractCtor newContext ind.tyBinders) ind.constructors) in
        c, [[(lident2mlsymbol ind.tyName, List.append (List.map (fun x -> prependTick (convIdent x)) identsPP) (dummyIndexIdents nIndices)  , Some tyDecBody)]]
    | _ -> c, []

let extractTypeDefnsAux (c: context) (sigs:list<sigelt>) : context * list<mltydecl> =
   let c, l = Util.fold_map extractSigElt c sigs in
   c, List.flatten l
 
let mkContext (e:Tc.Env.env) : context =
    { tcenv = e; gamma =[] ; tydefs =[]}

let extractTypeDefns (sigs:list<sigelt>) (e: Tc.Env.env): context * list<mltydecl> =
    extractTypeDefnsAux (mkContext e) sigs 
    
