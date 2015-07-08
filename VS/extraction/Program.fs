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

(*the \hat{\epsilon} function in the thesis (Sec. 3.3.5) *)
let rec extractType' (ft:typ') : mlty = 
match ft with
  | Typ_btvar _ -> unknownType (* what does Typ_btvar denote? *)
  | Typ_const _ -> unknownType (* what does Typ_const denote? *)
  | Typ_fun (bb, cm) -> curry (List.map extractBinder bb) (extractComp cm)
  | Typ_refine _ -> unknownType
  | Typ_app _ -> unknownType
  | Typ_lam  _ -> unknownType
  | Typ_ascribed _  -> unknownType
  | Typ_meta _ -> unknownType
  | Typ_uvar _ -> unknownType
  | Typ_delayed _ -> unknownType
  | Typ_unknown  _ -> unknownType
and extractBinder (bn : binder ): mlty =
match bn with
| (Inl btv,_) -> extractKind (btv.sort)
| (Inr bvv,_) -> extractTyp (bvv.sort)
and extractTyp (ft:typ) : mlty = MLTY_Tuple []
and extractKind (ft:knd) : mlty = erasedContent
and extractComp (ft:comp) : mlty = extractComp' (ft.n) 
and extractComp' (ft:comp') : mlty =
match  ft with
  | Total ty -> extractTyp ty
  | Comp cm -> extractTyp (cm.result_typ)
 

[<EntryPoint>]
let main argv = 
    Util.print_string "hello, what can I extract for you?";
    0
