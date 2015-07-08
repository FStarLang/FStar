// Learn more about F# at http://fsharp.net
// See the 'F# Tutorial' project for more help.
#light "off"
module Microsoft.FStar.Extraction
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.OCaml.Syntax
open Microsoft.FStar.Util

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
type context = list<btvar>

(*is there an F# library of associative lists?*)
let contains (c:context) (b:btvar) = true (*  FIX!! *)

(*the \hat{\epsilon} function in the thesis (Sec. 3.3.5) *)
let rec extractType' (c:context) (ft:typ') : mlty = 
(*first \beta, \iota and \zeta reduces ft. Since F* does not have SN, one has to be more careful for the termination argument*)
match ft with
  | Typ_btvar _ -> unknownType (* what does Typ_btvar denote? *)
  | Typ_const _ -> unknownType (* what does Typ_const denote? *)
  | Typ_fun (bb, cm) -> 
        let codomain = (extractComp  c cm) in 
        if  (codomain = erasedContent) then erasedContent else  (curry (List.map (extractBinder c) bb) codomain)
  | Typ_refine _ -> unknownType
  | Typ_app (ty, arrgs) ->
    (match ty.n with
        | Typ_btvar btv -> (if (contains c btv) then MLTY_Var (convIdent btv.v.realname) else unknownType)
            (*the args are thrown away, because in OCaml, type variables have type Type and not something like -> .. -> .. Type *)
        | Typ_const ftv -> unknownType
        (*are there designated constants for inductive types, there are 3 cases for this in the thesis.
            1) If ftv is a type scheme (possibly inductively defined (the thesis seems to unnecessarily makes a separate case for inductive types))
            2) otherwise if ftv can be delta unfolded, then call recursively on the result of the unfolding (termination argument?)
            3) if it is non reducible, then unknownType
        *)
        | _ -> unknownType)

  | Typ_lam  _ -> unknownType
  | Typ_ascribed _  -> unknownType
  | Typ_meta _ -> unknownType
  | Typ_uvar _ -> unknownType
  | Typ_delayed _ -> unknownType
  | Typ_unknown  _ -> unknownType
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
