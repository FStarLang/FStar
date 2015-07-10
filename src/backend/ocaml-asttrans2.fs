// Learn more about F# at http://fsharp.net
// See the 'F# Tutorial' project for more help.
#light "off"
module Microsoft.FStar.Backends.OCaml.NewExtaction
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.OCaml.Syntax
open Microsoft.FStar.Util
open Microsoft.FStar.Tc.Env
open Microsoft.FStar
open Microsoft.FStar.Tc.Normalize
open Microsoft.FStar.Absyn.Print

let rec curry (inp: (list<mlty>)) (out: mlty) =
  match inp with
  | [] -> out
  | h::tl -> (MLTY_Fun (h,(curry tl out)))

(*
  Below, "the thesis" refers to:
  Letouzey, P. “Programmation Fonctionnelle Certifiée – L’extraction de Programmes Dans L’assistant Coq.” Université Paris-Sud, 2004.
  http://www.pps.univ-paris-diderot.fr/~letouzey/download/these_letouzey_English.ps.gz
*)

(*\box type in the thesis, to be used to denote the result of erasure of logical (computationally irrelevant) content*)
let erasedContent : mlty = MLTY_Tuple []

(* \mathbb{T} type in the thesis, to be used when OCaml is not expressive enough for the source type *)
let unknownType : mlty = MLTY_Var  ("Obj.t", 0)

let convRange (r:Range.range) : int = 0 (*FIX!!*)
let convIdent (id:ident) : mlident = (id.idText (*FIX!! these names are of the form _n_m*) ,(convRange id.idRange))
    
(* This is all the context is needed for extracting F* types to OCaml.
   In particular, the definition of a type constant is not needed when translating references to it.
   However, enough info is needed to determine whether a type constant is a type scheme. add that.
*)
type context = {
    tyVars : list<ident>;
    tyConstants : list<lident>
}

let emptyContext : context = {tyVars=[]; tyConstants =[]}

(*is there an F# library of associative lists?*)
let contains (c:context) (b:btvar) = List.contains b.v.realname (*why not ppname?*) c.tyVars

let deltaUnfold (i : lident) (c: context) : (option<typ>) = None (*FIX!!*)

(*The thesis defines a type scheme as "something that becomes a type when enough arguments (possibly none?) are applied to it" ,  e.g. vector, list.
    I guess in F*, these include Inductive types and type abbreviations.
    Formal definition is @ Definition 8, Sec. 1.2.3
      *)
let isTypeScheme (i : lident) (c: context) : bool = true  (* FIX!! *)

(* let liftType' (t:typ') : typ = failwith "liftType is undefined" *)

let lident2mlpath (l:lident) : mlpath =
  (List.map (fun x -> x.idText) l.ns, l.ident.idText)
(*the \hat{\epsilon} function in the thesis (Sec. 3.3.5) *)
let rec extractType' (c:context) (ft:typ') : mlty = 
(* first \beta, \iota and \zeta reduces ft. Since F* does not have SN, one has to be more careful for the termination argument.
    Why not \delta? I guess the reason is that unfolding definitions will make the resultant OCaml code less readable.
    However in the Typ_app case,  \delta reduction is done as the second-last resort, just before giving up and returing unknownType;
        a bloated type is atleast as good as unknownType?
*)
match ft with
(*The next 2 cases duplicate a lot of code in the Type_app case. It will nice to share the common computations.*)
  | Typ_btvar btv -> (if (contains c btv) then MLTY_Var (convIdent btv.v.realname) else unknownType)
  | Typ_const ftv -> 
            (match  (isTypeScheme ftv.v c)  with
             | true -> MLTY_Named ([ (* FIX!! *)],(lident2mlpath ftv.v))
             | false -> 
                 (match  (deltaUnfold ftv.v c) with
                 | Some tyu ->  extractTyp c tyu
                 | None -> unknownType
                 )
            )
  | Typ_fun (bs, codomain) -> 
        (let codomainML = (extractComp  c codomain) in 
        if  (codomainML = erasedContent) 
        then erasedContent 
        else  (curry (List.map (extractBinder c) bs) codomainML))
  | Typ_refine (bv,ty) -> extractTyp c ty
  | Typ_app (ty, arrgs) ->
    (match ty.n with
        | Typ_btvar btv -> (if (contains c btv) then MLTY_Var (convIdent btv.v.realname) else unknownType)
            (*the args are thrown away, because in OCaml, type variables have type Type and not something like -> .. -> .. Type *)
        | Typ_const ftv -> 
            (match  (isTypeScheme ftv.v c)  with
             | true -> 
                 let mlargs = List.map (getTypeFromArg c) arrgs in
                    (MLTY_App ( MLTY_Named ([ (* FIX!! *)],(lident2mlpath ftv.v)) , MLTY_Tuple mlargs))
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
(* In OCaml, there are no expressions in type applications.
   Need to make similar changes when extracting the definitions of type schemes
   In Coq, the Inr arguments are just removed in a later phase.
*)
and extractBinder  (c:context) (bn : binder ): mlty =
match bn with
| (Inl btv,_) -> extractKind (btv.sort)
| (Inr bvv,_) -> extractTyp c (bvv.sort)
and extractTyp  (c:context) (ft:typ) : mlty = extractType' c (ft.n)
and extractKind (ft:knd) : mlty = erasedContent
and extractComp  (c:context) (ft:comp) : mlty = extractComp' c (ft.n) 
and extractComp'  (c:context) (ft:comp') : mlty =
match  ft with
  | Total ty -> extractTyp c ty
  | Comp cm -> extractTyp c (cm.result_typ)


let binderIdent (bn:binder): ident =
match bn with
| (Inl btv,_) -> btv.v.realname
| (Inr bvv,_) -> bvv.v.realname

(* these vars will have type Type, irrespective of that types they had in F*. This is to match the limitations of  OCaml*)
let extendContext (c:context) (tyVars : list<ident>) (tyConsts : list<lident>) : context = 
    { tyVars = List.append c.tyVars tyVars; tyConstants = List.append c.tyConstants tyConsts}

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
| (Sig_datacon (l, (*codomain*) t ,(_,cargs:binders,_),_,_,_))::tlsig ->
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
    let (indConstrs:list<inductiveConstructor>, ttlsig) = parseInductiveConstructors tlsig (List.length constrs) in
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
            fprint1 "extracting the type of constructor %s\n" (lident2mlsymbol ctor.cname);
            fprint1 "%s\n" (typ_to_string ctor.ctype);
            printfn "%A\n" (ctor.ctype);
        (lident2mlsymbol ctor.cname, argTypes mlt))
 
(*similar to the definition of the second part of \hat{\epsilon} in page 110*)
(* \pi_1 of returned value is the exported constant*)
let extractSigElt (c:context) (s:sigelt) :  option<lident * mlsig1> =
match s with
| Sig_typ_abbrev (l,bs,_,t,_,_) -> 
    let idents = List.map binderIdent bs in
    let newContext = (extendContext c idents [l] ) in
    let tyDecBody = MLTD_Abbrev (extractTyp newContext t) in
     Some (l, MLS_Ty [(mlsymbolOfLident l, List.map convIdent idents , Some tyDecBody)])
     (*type l idents = tyDecBody*)

| Sig_bundle _ -> 
    let ind = parseFirstInductiveType s in
    let idents = List.map binderIdent ind.tyBinders in
    let newContext = (extendContext c idents [ind.tyName]) in
    let tyDecBody = MLTD_DType (List.map (extractCtor newContext) ind.constructors) in
          Some (ind.tyName, MLS_Ty [(lident2mlsymbol ind.tyName, List.map convIdent idents , Some tyDecBody)])
     (*type l idents = tyDecBody*)
| _ -> None

(*
[<EntryPoint>]
let main argv = 
    Util.print_string "hello, what can I extract for you?";
    0
    *)