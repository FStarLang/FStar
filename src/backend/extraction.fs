// Learn more about F# at http://fsharp.net
// See the 'F# Tutorial' project for more help.
#light "off"
module Microsoft.FStar.Backends.OCaml.Extraction
open Microsoft.FStar.Absyn
open Microsoft.FStar.Backends.OCaml.Syntax
open Microsoft.FStar.Util
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar
open Microsoft.FStar.Tc.Normalize
open Microsoft.FStar.Absyn.Print


(*copied from ocaml-strtrans.fs*)
let prependTick (x,n) = if Util.starts_with x "'" then (x,n) else ("'"^x,n)

(*generates inp_1 -> inp_2 -> ... inp_n -> out *)
let rec curry (inp: (list<mlty>)) (out: mlty) =
  match inp with
  | [] -> out
  | h::tl -> (MLTY_Fun (h,(curry tl out)))

(*
  Below, "the thesis" refers to:
  Letouzey, P. “Programmation Fonctionnelle Certifiée – L’extraction de Programmes Dans L’assistant Coq.” Université Paris-Sud, 2004.
  http://www.pps.univ-paris-diderot.fr/~letouzey/download/these_letouzey_English.ps.gz
*)

(*\box type in the thesis, to be used to denote the result of erasure of logical (computationally irrelevant) content.
  The actual definiton is a bit complicated, because we need for any x, \box x to be convertible to \box.
*)

(* MLTY_Tuple [] extracts to (), and is an alternate choice. 
    However, it represets both the unit type and the unit value. Ocaml gets confused sometimes*)
let erasedContent : mlty = MLTY_Named ([],([],"unit"))

(* \mathbb{T} type in the thesis, to be used when OCaml is not expressive enough for the source type *)
let unknownType : mlty = MLTY_Named  ([],([],"Obj.t"))

let convRange (r:Range.range) : int = 0 (*FIX!!*)
let convIdent (id:ident) : mlident = (id.idText ,(convRange id.idRange))
    
(* This is all the context is needed for extracting F* types to OCaml.
   In particular, the definition of a type constant is not needed when translating references to it.
   However, enough info is needed to determine whether a type constant is a type scheme. add that.
*)
type context = {
    tyVars : list<ident>;
    tyConstants : list<lident>;
    allowTypeVars : bool
}

let emptyContext : context = {tyVars=[]; tyConstants =[]; allowTypeVars=true}

(* vars in tyVars will have type Type, irrespective of that types they had in F*. This is to match the limitations of  OCaml*)
let extendContext (c:context) (tyVars : list<ident>) (tyConsts : list<lident>) (alowTypeVars_ : bool ): context = 
    { tyVars = List.append c.tyVars tyVars; tyConstants = List.append c.tyConstants tyConsts; allowTypeVars = alowTypeVars_}

let disallowTypeVars (c:context) : context = extendContext c [] [] false

let contains (c:context) (b:btvar) : bool =     
    List.contains ( b.v.realname.idText)  (List.map (fun x -> x.idText) c.tyVars) (*needed for sh, its ppname is _, and range is 0*)
    || List.contains (b.v.realname.idRange)  (List.map (fun x -> x.idRange) c.tyVars) (*needed for inductive constructors. names often have extra things appended*)

let deltaUnfold (i : lident) (c: context) : (option<typ>) = None (*FIX!!*)

(*The thesis defines a type scheme as "something that becomes a type when enough arguments (possibly none?) are applied to it" ,  e.g. vector, list.
    I guess in F*, these include Inductive types and type abbreviations.
    Formal definition is @ Definition 8, Sec. 1.2.3
      *)
let isTypeScheme (i : lident) (c: context) : bool = true  (* FIX!! *)


let lident2mlpath (l:lident) : mlpath =
  ( (* List.map (fun x -> x.idText) l.ns *) [], l.ident.idText)


(*the \hat{\epsilon} function in the thesis (Sec. 3.3.5) *)
let rec extractType' (c:context) (ft:typ') : mlty = 
(* First \beta, \iota and \zeta reduces ft, or assume they are already reduced.
    Since F* does not have SN, one has to be more careful for the termination argument.
    Because OCaml does not support computations in Type, unknownType is supposed to be used if they are really unaviodable.
    The classic example is the type : T b \def if b then nat else bool. If we dont compute, T true will extract to unknownType.
    Why not \delta? I guess the reason is that unfolding definitions will make the resultant OCaml code less readable.
    However in the Typ_app case,  \delta reduction is done as the second-last resort, just before giving up and returing unknownType;
        a bloated type is atleast as good as unknownType?
    An an F* specific example, unless we unfold Mem x pre post to StState x wp wlp, we have no idea that it should be translated to x
*)
match ft with
(*The next 2 cases duplicate a lot of code in the Type_app case. It will nice to share the common computations.*)
  | Typ_btvar btv -> (if (contains c btv) then MLTY_Var (prependTick (convIdent btv.v.ppname)) else unknownType)
  (*it is not clear whether description in the thesis covers type applications with 0 args. However, this case is needed to translate types like nnat, and so far seems to work as expected*)
  | Typ_const ftv -> 
            (match  (isTypeScheme ftv.v c)  with
             | true -> MLTY_Named ([],(lident2mlpath ftv.v))
             | false -> 
                 (match  (deltaUnfold ftv.v c) with
                 | Some tyu ->  extractTyp c tyu
                 | None -> unknownType
                 )
            )

  | Typ_fun (bs, codomain) -> 
        let (bts, newC) = extractBindersTypes c bs in
        (let codomainML = (extractComp  newC codomain) in 
        if  (codomainML = erasedContent) 
        then erasedContent 
        else  (curry bts codomainML))

  | Typ_refine (bv (*var and unrefined type*) , _ (*refinement condition*)) -> extractTyp c bv.sort

  (*can this be a partial type application? , i.e can the result of this application be something like Type -> Type, or nat -> Type? : Yes *)
  | Typ_app (ty, arrgs) ->
    (match ty.n with
        | Typ_btvar btv -> (if (contains c btv) then MLTY_Var (prependTick (convIdent btv.v.ppname)) else unknownType)
            (*the args are thrown away, because in OCaml, type variables have type Type and not something like -> .. -> .. Type *)
        | Typ_const ftv -> 
            (match  (isTypeScheme ftv.v c)  with
             | true -> 
                 let mlargs = List.map (getTypeFromArg c) arrgs in
                    (MLTY_Named (mlargs,(lident2mlpath ftv.v)))
             | false -> 
                 (match  (deltaUnfold ftv.v c) with
                 | Some tyu ->  extractTyp c tyu
                 | None -> unknownType
                 )
            )
        | _ -> unknownType)

  | Typ_lam  _ -> unknownType
  | Typ_ascribed _  -> unknownType
  | Typ_meta _ -> unknownType
  | Typ_uvar _ -> unknownType
  | Typ_delayed ((Inr f),_) -> extractTyp c (f ())
  |   _ -> unknownType
and getTypeFromArg (c:context) (a:arg) : mlty =
match (fst a) with
| Inl ty -> extractTyp c ty
| Inr _ -> erasedContent 

(* Return the new context, where this binder might be in scope. Actually this code be reverted back to the old, less complicated state
   where c.allowTypeVars was always assumed to be false. *)
and extractBinderType  (c:context) (bn : binder): mlty * context =
match bn with
| (Inl btv,_) ->
      let k = (btv.sort) in 
      let newC = (match k.n with
                 | Kind_type -> (if c.allowTypeVars then (extendContext c [btv.v.realname] [] c.allowTypeVars) else c)
                 | _ ->  c)
       in  (extractKind (disallowTypeVars c) (btv.sort), newC)
| (Inr bvv,_) -> (extractTyp (disallowTypeVars c) (bvv.sort), c)

and extractBindersTypes  (c:context) (bs : list<binder>): list<mlty> * context =
match bs with
| (h::tl) ->  let (t,newC) = extractBinderType c h in
               let (lt, newNewC) = extractBindersTypes newC tl in
               ((t::lt),newNewC)
| [] -> ([], c)

and extractTyp  (c:context) (ft:typ) : mlty = extractType' c (ft.n)
and extractKind (c:context) (ft:knd) : mlty = erasedContent
and extractComp  (c:context) (ft:comp) : mlty = extractComp' c (ft.n) 
and extractComp'  (c:context) (ft:comp') : mlty =
match  ft with
  | Total ty -> extractTyp c ty
  | Comp cm -> extractTyp c (cm.result_typ)


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
  cargs : binders (*will this list always be empty? it has always been empty: tested nat, list, vec*)
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
| MLTY_Fun (a,b) -> a::(argTypes b)
| _ -> []
 
let lident2mlsymbol (l:lident) : mlsymbol = l.ident.idText

let extractCtor (c:context) (ctor: inductiveConstructor):  (mlsymbol * list<mlty>) =
   if (0< List.length ctor.cargs)
   then (failwith "cargs is unexpectedly non-empty. This is a design-flaw, please report.")
   else 
        (let mlt = extractTyp c ctor.ctype in
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

let rec numIndices (k:knd') (typeName : string) : int =
match k with
| Kind_type -> 0
| Kind_arrow (_,r) -> 1 + numIndices r.n typeName
| Kind_delayed (k, _ ,_) -> numIndices k.n typeName
| _ -> failwith ("unexpected signature of inductive type" ^ typeName) 

let dummyIdent (n:int) : mlident = ("'dummyV"^(Util.string_of_int n), 0)

let rec firstNNats (n:int) : list<int> =
if (0<n)
  then (n::(firstNNats (n-1)))
  else []

let dummyIndexIdents (n:int) : list<mlident> = List.map dummyIdent (firstNNats n)


(*similar to the definition of the second part of \hat{\epsilon} in page 110*)
(* \pi_1 of returned value is the exported constant*)
let extractSigElt (c:context) (s:sigelt) :  option<(lident * mlsig1)> =
match s with
| Sig_typ_abbrev (l,bs,_,t,_,_) -> 
    let identsPP = List.map binderPPnames bs in
    let identsReal = List.map binderRealnames bs in
            //printfn "binders are %A\n" (identsReal);
    let newContext = (extendContext c identsReal [l] true) in
    let tyDecBody = MLTD_Abbrev (extractTyp newContext t) in
            //printfn "type is %A\n" (t);
     Some (l, MLS_Ty [(mlsymbolOfLident l, List.map (fun x -> prependTick (convIdent x)) identsPP , Some tyDecBody)])
     (*type l idents = tyDecBody*)

| Sig_bundle _ -> 
    let ind = parseFirstInductiveType s in
    let identsPP = List.map binderPPnames ind.tyBinders in
    let identsReal = List.map binderRealnames ind.tyBinders in
            // printfn "binders are %A\n" (identsReal);
    let newContext = (extendContext c identsReal [ind.tyName] false) in
    let nIndices = numIndices ind.k.n ind.tyName.ident.idText in
    let tyDecBody = MLTD_DType (List.map (extractCtor newContext) ind.constructors) in
          Some (ind.tyName, MLS_Ty [(lident2mlsymbol ind.tyName, List.append (List.map (fun x -> prependTick (convIdent x)) identsPP) (dummyIndexIdents nIndices)  , Some tyDecBody)])
| _ -> None

let rec extractTypeDefnsAux (c: context) (sigs:list<sigelt>) : list<mlsig1> =
    match sigs with
    | hsig::tlsigs ->
        (match extractSigElt c hsig with
        | Some (exportedConst, mls) ->  
                let nc = extendContext c [] [exportedConst] true in
                mls::(extractTypeDefnsAux nc tlsigs)
        | None -> (extractTypeDefnsAux c tlsigs)
        )
    | _ -> []

let extractTypeDefns (sigs:list<sigelt>) (e: env): list<mlsig1> =
   extractTypeDefnsAux emptyContext sigs

