// Learn more about F# at http://fsharp.net
// See the 'F# Tutorial' project for more help.
#light "off"
module Microsoft.FStar.Extraction
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.OCaml.Syntax
open Microsoft.FStar.Util
open Microsoft.FStar.Tc.Env

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
let convIdent (id:ident) : mlident = (id.idText,(convRange id.idRange))
    
(*assuming that btvar includes the name of the variable*)
type context = env
(*is there an F# library of associative lists?*)
let contains (c:context) (b:btvar) = true (*  FIX!! *)


let deltaUnfold (i : lident) (c: context) : (option<typ>) = None (*Fix*)

(*The thesis defines a type scheme as "something that becomes a type when enough arguments (possibly none?) are applied to it" ,  e.g. vector, list.
    I guess in F*, these include Inductive types and type definitions *)
let isTypeScheme (i : lident) (c: context) : (option<typ>) = None (*Fix*)


let liftType' (t:typ') :typ =
(*How to admit/assume a function in F#?*)

(*the \hat{\epsilon} function in the thesis (Sec. 3.3.5) *)
let rec extractType' (c:context) (ft:typ') : mlty = 
(* first \beta, \iota and \zeta reduces ft. Since F* does not have SN, one has to be more careful for the termination argument.
    Why not \delta? I guess the reason is that unfolding definitions will make the resultant OCaml code less readable.
    However in the Typ_app case,  \delta reduction is done as the second-last resort, just before giving up and returing unknownType
*)
match ft with
  | Typ_btvar _ -> extractType' c (Typ_app (liftType' ft, []))
  | Typ_const _ -> extractType' c (Typ_app (liftType' ft, []))
  | Typ_fun (bb, cm) -> 
        let codomain = (extractComp  c cm) in 
        if  (codomain = erasedContent) then erasedContent else  (curry (List.map (extractBinder c) bb) codomain)
  | Typ_refine (bv,ty) -> extractType ty
  | Typ_app (ty, arrgs) ->
    (match ty.n with
        | Typ_btvar btv -> (if (contains c btv) then MLTY_Var (convIdent btv.v.realname) else unknownType)
            (*the args are thrown away, because in OCaml, type variables have type Type and not something like -> .. -> .. Type *)
        | Typ_const ftv -> 
            (match  (isTypeScheme  ftv)  with
             | Some tys -> 
                 let mlargs = map getTypeFromArg args in
                    (MLTY_App (extractType tys) (MLTY_Tuple mlargs))
             | None -> 
                 (match  (deltaUnfold ftv ) with
                 | Some tyu ->  extracType tyu
                 | None -> unknownType
                 )
            )
        | _ -> unknownType)

  | Typ_lam  _ -> unknownType
  | Typ_ascribed _  -> unknownType
  | Typ_meta _ -> unknownType
  | Typ_uvar _ -> unknownType
  | Typ_delayed _ -> unknownType
  | Typ_unknown  _ -> unknownType
and getTypeFromArg (a:arg) : mlty =
match (fst a) with
| Inl ty -> extractTyp ty
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
 

[<EntryPoint>]
let main argv = 
    Util.print_string "hello, what can I extract for you?";
    0
