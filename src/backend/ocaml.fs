(* -------------------------------------------------------------------- *)
module Microsoft.FStar.Backends.OCaml

open System
open System.Text

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util

(* -------------------------------------------------------------------- *)
let unexpected () =
    failwith "ocaml-backend-unexpected-construct"

(* -------------------------------------------------------------------- *)
let unsupported () =
    failwith "ocaml-backend-unsupported-construct"

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
let pp_sconst sctt =
  match sctt with
  | Const_unit         -> "()"
  | Const_char   c     -> sprintf "'%s'" (encode_char c)
  | Const_uint8  c     -> sprintf "'%s'" (ocaml_u8_codepoint c)
  | Const_int32  i     -> sprintf "%d" i // FIXME
  | Const_int64  i     -> sprintf "%d" i // FIXME
  | Const_bool   true  -> "true"
  | Const_bool   false -> "false"
  | Const_float  d     -> sprintf "%f" d

  | Const_bytearray (bytes, _) ->
      let bytes = bytes |> Array.map ocaml_u8_codepoint
      sprintf "\"%s\"" (bytes |> String.concat "")

  | Const_string (bytes, _) ->
      let chars = (new UTF8Encoding (true, true)).GetString(bytes)
      let chars = chars |> String.collect encode_char
      sprintf "\"%s\"" chars

(* -------------------------------------------------------------------- *)
let is_prim_ns (ns : list<ident>) =
    match ns with
    | [{ idText = "Prims" }] -> true
    | _ -> false

(* -------------------------------------------------------------------- *)
let is_op_equality (x : lident) =
    is_prim_ns x.ns && x.ident.idText = "op_Equality"

(* -------------------------------------------------------------------- *)
let name_of_let_ident (x : either<bvvdef,lident>) =
    match x with
    | Inl x -> x.realname.idText
    | Inr x -> x.ident.idText

(* -------------------------------------------------------------------- *)
let rec pp_let_binding ((rec_, lb) : letbindings) =
    match lb with
    | [x, _, body] ->
        sprintf "let %s %s = %s"
            (if rec_ then "rec" else "")
            (name_of_let_ident x)
            (pp_exp body)

    | _ -> unsupported ()

(* -------------------------------------------------------------------- *)
and pp_exp (e : exp) =
    match Absyn.Util.destruct_app e with
    | ({ v = Exp_fvar (x, _) }, [(e1, _); (e2, _)]) when is_op_equality x.v ->
        sprintf "(%s) = (%s)" (pp_exp e1) (pp_exp e2)

    | _ ->
        match e.v with
        | Exp_bvar x ->
            x.v.realname.idText

        | Exp_fvar (x, _) ->
            x.v.ident.idText

        | Exp_constant c ->
            pp_sconst c

        | Exp_abs (x, _, e) ->
            sprintf "fun %s => %s" x.realname.idText (pp_exp e)

        | Exp_app (e1, e2, _) ->
            sprintf "(%s) (%s)" (pp_exp e1) (pp_exp e2)

        | Exp_match (e, bs) ->
            sprintf "match %s with %s"
                (pp_exp e)
                (bs |> List.map pp_match_branch |> String.concat " ")

        | Exp_let (lb, body) ->
            sprintf "%s in %s" (pp_let_binding lb) (pp_exp body)

        | Exp_primop (x, es) ->
            sprintf "%s %s"
                x.idText
                (es |> List.map (fun e -> sprintf "(%s)" (pp_exp e))
                    |> String.concat ", ")

        | Exp_ascribed (e, _) ->
            pp_exp e

        | Exp_uvar      _ -> unexpected  ()
        | Exp_tabs      _ -> unsupported ()
        | Exp_tapp      _ -> unsupported ()

(* -------------------------------------------------------------------- *)
and pp_pattern (p : pat) =
    match p with
    | Pat_cons (x, ps) ->
        match ps with
        | [] -> x.ident.idText
        | _  ->
            sprintf "%s (%s)"
                x.ident.idText
                (ps |> List.map pp_pattern |> String.concat ", ")

    | Pat_var x ->
        x.realname.idText

    | Pat_constant c ->
        pp_sconst c

    | Pat_disj ps ->
        sprintf "(%s)" (ps |> List.map pp_pattern |> String.concat " | ")

    | Pat_wild ->
        "_"

    | Pat_tvar   _ -> unsupported ()
    | Pat_twild  _ -> unsupported ()
    

(* -------------------------------------------------------------------- *)
and pp_match_branch ((p, cl, body) : pat * exp option * exp) =
    sprintf "| %s %s -> (%s)"
        (pp_pattern p)
        (match cl with
         | None   -> ""
         | Some e -> sprintf "when %s" (pp_exp e))
         (pp_exp body)

(* -------------------------------------------------------------------- *)
let pp_modelt (modx : sigelt)=
    match modx with
    | Sig_let lb ->
        Some (pp_let_binding lb)

    | Sig_main e ->
        Some (sprintf "let _ = %s" (pp_exp e))

    | Sig_tycon _ ->
        Some "tycon"

    | Sig_typ_abbrev _ ->
        Some "abbrev"

    | Sig_datacon _ ->
        Some "datacon"

    | Sig_bundle _ ->
        Some "bundle"

    | Sig_assume         _ -> None
    | Sig_val_decl       _ -> None
    | Sig_logic_function _ -> None

(* -------------------------------------------------------------------- *)
let pp_module (mod_ : modul) =
    let parts = mod_.declarations |> List.choose pp_modelt in
    sprintf "module %s = struct\n%s\nend"
        mod_.name.ident.idText
        (parts |> String.concat "\n\n")
