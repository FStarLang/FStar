(* -------------------------------------------------------------------- *)
module Microsoft.FStar.Backends.OCaml

open System
open System.Text

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util

open FSharp.OCaml.Format

(* -------------------------------------------------------------------- *)
let ocaml_u8_codepoint (i : byte) =
  sprintf "\\x%x" i

(* -------------------------------------------------------------------- *)
let encode_char c =
  if (int)c > 127 then // Use UTF-8 encoding
    let bytes = System.String (c, 1)
    let bytes = (new UTF8Encoding (true, true)).GetBytes(bytes)
    bytes
      |> Array.map ocaml_u8_codepoint
      |> String.concat ""
  else
    match c with
    | c when Char.IsLetterOrDigit(c) -> System.String (c, 1)
    | c when Char.IsPunctuation(c)   -> System.String (c, 1)
    | c when c = ' '                 -> " "
    | c when c = '\t'                -> "\\t"
    | c when c = '\r'                -> "\\r"
    | c when c = '\n'                -> "\\n"
    | _                              -> ocaml_u8_codepoint ((byte)c)

(* -------------------------------------------------------------------- *)
let pp_sconst fmt sctt =
  match sctt with
  | Const_unit         -> fmt << String "()"
  | Const_char   c     -> fmt << String (sprintf "'%s'" (encode_char c))
  | Const_uint8  c     -> fmt << String (sprintf "'%s'" (ocaml_u8_codepoint c))
  | Const_int32  i     -> fmt << Int ((int) i) // FIXME
  | Const_int64  i     -> fmt << Int ((int) i) // FIXME
  | Const_bool   true  -> fmt << String "true"
  | Const_bool   false -> fmt << String "false"
  | Const_float  d     -> fmt << Float d

  | Const_bytearray (bytes, _) ->
      let bytes = bytes |> Array.map ocaml_u8_codepoint
      fmt << String (sprintf "\"%s\"" (bytes |> String.concat ""))

  | Const_string (bytes, _) ->
      let chars = (new UTF8Encoding (true, true)).GetString(bytes)
      let chars = chars |> String.collect encode_char
      fmt << String (sprintf "\"%s\"" chars)

(*
(* -------------------------------------------------------------------- *)
let norm_ty_r k ty =
  match ty with
  | Typ_btvar    of bvar<typ,kind>
  | Typ_const    of var<kind> 

  | Typ_fun      of option<bvvdef> * typ * typ          (* x:t -> t'  or  t -> t' *)
  | Typ_univ     of btvdef * kind  * typ                (* 'a:k -> t *)

  | Typ_refine   of bvvdef * typ * typ                  (* x:t{phi} *)
  | Typ_app      of typ * typ                           (* t t' *) 
  | Typ_dep      of typ * exp                           (* t e *) 
  | Typ_lam      of bvvdef * typ * typ                  (* fun (x:t) => T *)
  | Typ_tlam     of btvdef* kind * typ                  (* fun ('a:k) => T *) 

  | Typ_unknown _ -> error "ocaml-bk-typ-unknown"
  | Typ_meta    _ -> error "ocaml-bk-type-meta"
  | Type_uvar   _ -> error "ocaml-bk-type-uvar"

(* -------------------------------------------------------------------- *)
let pp_typ fmt ty =
  match ty with
  | Typ_refine     (ty, _) -> pp_typ fmt ty
  | Type_abscribed (ty, _) -> pp_typ fmt ty

  | Typ_unknown _ -> error "ocaml-bk-typ-unknown"
  | Typ_meta    _ -> error "ocaml-bk-type-meta"
  | Type_uvar   _ -> error "ocaml-bk-type-uvar"

type typ =
  | Typ_btvar    of bvar<typ,kind>
  | Typ_const    of var<kind> 
  | Typ_fun      of option<bvvdef> * typ * typ          (* x:t -> t'  or  t -> t' *)
  | Typ_univ     of btvdef * kind  * typ                (* 'a:k -> t *)
  | Typ_refine   of bvvdef * typ * typ                  (* x:t{phi} *)
  | Typ_app      of typ * typ                           (* t t' *) 
  | Typ_dep      of typ * exp                           (* t e *) 
  | Typ_lam      of bvvdef * typ * typ                  (* fun (x:t) => T *)
  | Typ_tlam     of btvdef* kind * typ                  (* fun ('a:k) => T *) 
  | Typ_ascribed of typ * kind                          (* t <: k *)
  | Typ_uvar     of uvar * kind                         (* Only needed for unification *)
  | Typ_meta     of meta                                (* Not really in the type language; a way to stash convenient metadata with types *)
  | Typ_unknown                                         (* Initially, every AST node has type unknown *)

and exp' =
  | Exp_bvar       of bvar<exp,typ>
  | Exp_fvar       of var<typ> 
  | Exp_constant   of sconst
  | Exp_constr_app of var<typ> * list<either<typ,exp>>
  | Exp_abs        of bvvdef * typ * exp 
  | Exp_tabs       of btvdef * kind * exp            
  | Exp_app        of exp * exp
  | Exp_tapp       of exp * typ             
  | Exp_match      of exp * list<(pat * option<exp> * exp)>      (* optional when clause in each equation *)
  | Exp_ascribed   of exp * typ 
  | Exp_let        of bool * list<(bvvdef * typ * exp)> * exp    (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
  | Exp_primop     of ident * list<exp>

and pat = 
  | Pat_cons     of lident * list<pat>
  | Pat_var      of bvvdef
  | Pat_tvar     of bvdef<typ>
  | Pat_constant of sconst
  | Pat_disj     of list<pat>
  | Pat_wild
  | Pat_twild


(* -------------------------------------------------------------------- *)
let pp_modelt (fmt : formatter) (modx : sigelt)=
  match modx with
  | _ -> assert false

(*
type sigelt =
  | Sig_tycon          of lident * list<tparam> * kind * list<lident> * list<lident> * list<logic_tag> (* bool is for a prop, list<lident> identifies mutuals *)
  | Sig_typ_abbrev     of lident * list<tparam> * kind * typ
  | Sig_datacon        of lident * typ
  | Sig_val_decl       of lident * typ 
  | Sig_assume         of lident * formula * aqual * atag
  | Sig_logic_function of lident * typ * list<logic_tag>
  | Sig_let            of letbinding * bool
  | Sig_main           of exp
  | Sig_bundle         of list<sigelt>  (* an inductive type is a bundle of all mutually defined Sig_tycons and Sig_datacons *)
type sigelts = list<sigelt>

type modul = {
  name: lident;
  declarations: sigelts;
  exports: sigelts;
}
*)
*)
