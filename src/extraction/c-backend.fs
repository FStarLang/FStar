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
(* -------------------------------------------------------------------- *)
#light "off"

module FStar.Extraction.ML.CBackend

open System
open System.Text
open FStar
open FStar.Util
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Format

(* String formatting functions *)
let new_line = "\n"

let rec concat li = 
    match li with
    | [] -> ""
    | hd::tl -> hd ^ concat tl
    
let rec concat1 li = 
    match li with
    | [] -> ""
    | hd::tl -> hd ^ " " ^ concat1 tl

let rec concat2 s li =
    match li with
    | [] -> ""
    | [e] -> e
    | hd::tl -> hd ^ s ^ concat2 s tl

let paren s = "(" ^ s ^ ")"
let bracket s = "[" ^ s ^ "]"
let cbracket s = "{" ^ s ^ "}"

(* -------------------------------------------------------------------- *)
type assoc  = | ILeft | IRight | Left | Right | NonAssoc
type fixity = | Prefix | Postfix | Infix of assoc
type opprec = int * fixity
type level  = opprec * assoc

let t_prio_fun  = (10, Infix Right)
let t_prio_tpl  = (20, Infix NonAssoc)
let t_prio_name = (30, Postfix)

let e_bin_prio_lambda = ( 5, Prefix)
let e_bin_prio_if     = (15, Prefix)
let e_bin_prio_letin  = (19, Prefix)
let e_bin_prio_or     = (20, Infix Left)
let e_bin_prio_and    = (25, Infix Left)
let e_bin_prio_eq     = (27, Infix NonAssoc)
let e_bin_prio_order  = (29, Infix NonAssoc)
let e_bin_prio_op1    = (30, Infix Left)
let e_bin_prio_op2    = (40, Infix Left)
let e_bin_prio_op3    = (50, Infix Left)
let e_bin_prio_op4    = (60, Infix Left)
let e_bin_prio_comb   = (70, Infix Left)
let e_bin_prio_seq    = (100, Infix Left)
let e_app_prio        = (10000, Infix Left)

let min_op_prec = (-1, Infix NonAssoc)
let max_op_prec = (max_int, Infix NonAssoc)


(*copied from ocaml-asttrans.fs*)

(* -------------------------------------------------------------------- *)
let rec in_ns (x: (list<'a> * list<'a>)) : bool = match x with
    | [], _ -> true
    | x1::t1, x2::t2 when (x1 = x2) -> in_ns (t1, t2)
    | _, _ -> false

(* -------------------------------------------------------------------- *)
let path_of_ns (currentModule : mlsymbol) ns =
    let ns' = Util.flatten_ns ns in
    if ns' = currentModule
    then []
    else let cg_libs = !Options.codegen_libs in
         let ns_len = List.length ns in
         let found = Util.find_map cg_libs (fun cg_path ->
            let cg_len = List.length cg_path in
            if List.length cg_path < ns_len
            then let pfx, sfx = Util.first_N cg_len ns in
                 if pfx = cg_path
                 then Some (pfx@[Util.flatten_ns sfx])
                 else None
            else None) in
         match found with 
            | None -> [ns']
            | Some x -> x

let mlpath_of_mlpath (currentModule : mlsymbol) (x : mlpath) : mlpath =
    match string_of_mlpath x with
    | "Prims.Some" -> ([], "Some")
    | "Prims.None" -> ([], "None")
    | _ ->
     let ns, x = x in
     (path_of_ns currentModule ns, x)

let ptsym_of_symbol (s : mlsymbol) : mlsymbol =
    if Char.lowercase (String.get s 0) <> String.get s 0
    then "l__" ^ s
    else s

let ptsym (currentModule : mlsymbol) (mlp : mlpath) : mlsymbol =
    if (List.isEmpty (fst mlp))
    then ptsym_of_symbol (snd  mlp)
    else
        let (p, s) = mlpath_of_mlpath currentModule mlp in
        String.concat "." (p @ [ptsym_of_symbol s])


let ptctor (currentModule : mlsymbol) (mlp : mlpath) : mlsymbol =
    let (p, s) = mlpath_of_mlpath currentModule mlp in
    let s = if Char.uppercase (String.get s 0) <> String.get s 0 then "U__" ^ s else s in
    String.concat "." (p @ [s])

(* -------------------------------------------------------------------- *)
let infix_prim_ops = [
    ("op_Addition"       , e_bin_prio_op1   , "+" );
    ("op_Subtraction"    , e_bin_prio_op1   , "-" );
    ("op_Multiply"       , e_bin_prio_op1   , "*" );
    ("op_Division"       , e_bin_prio_op1   , "/" );
    ("op_Equality"       , e_bin_prio_eq    , "==" );
    ("op_ColonEquals"    , e_bin_prio_eq    , "=");
    ("op_disEquality"    , e_bin_prio_eq    , "!=");
    ("op_AmpAmp"         , e_bin_prio_and   , "&&");
    ("op_BarBar"         , e_bin_prio_or    , "||");
    ("op_LessThanOrEqual"   , e_bin_prio_order , "<=");
    ("op_GreaterThanOrEqual", e_bin_prio_order , ">=");
    ("op_LessThan"          , e_bin_prio_order , "<" );
    ("op_GreaterThan"       , e_bin_prio_order , ">" );
    ("op_Modulus"           , e_bin_prio_order , "%" );
]

(* -------------------------------------------------------------------- *)
let prim_uni_ops = [
    ("op_Negation", "~");
    ("op_Minus", "-");
    ("op_Bang","*")
]

(* -------------------------------------------------------------------- *)
let prim_types = []

(* -------------------------------------------------------------------- *)
let prim_constructors = [
    ("Some", "Some");
    ("None", "None");
    ("Nil",  "[]");
    ("Cons", "::");
]

(* -------------------------------------------------------------------- *)
let is_prims_ns (ns : list<mlsymbol>) =
    ns = ["Prims"]

let infix_low_ops = [
    ("op_Hat_Plus"       , e_bin_prio_op1   , "+" );
    ("op_Hat_Subtraction"    , e_bin_prio_op1   , "-" );
    ("op_Hat_Star"       , e_bin_prio_op1   , "*" );
    ("op_Hat_Slash"       , e_bin_prio_op1   , "/" );
    ("op_Hat_Amp"         , e_bin_prio_op1   , "&");
    ("op_Hat_Bar"         , e_bin_prio_op1   , "|");
    ("op_Hat_Hat"        , e_bin_prio_op1    , "^");
    ("op_Hat_Modulus"           , e_bin_prio_order , "%" );
]

(* -------------------------------------------------------------------- *)
let low_uni_ops = [
    ("op_Hat_Subtraction_Subtraction", "-")
    ]

(* -------------------------------------------------------------------- *)
let low_types = []

let low_ns = [["FStar"; "UInt8"]; ["FStar"; "UInt32"]; ["FStar";"UInt63"]; ["FStar";"UInt64"]]
(* -------------------------------------------------------------------- *)
let low_constructors = []

(* -------------------------------------------------------------------- *)
let is_low_ns (ns : list<mlsymbol>) =
    List.contains ns low_ns

(* -------------------------------------------------------------------- *)
let as_bin_op ((ns, x) : mlpath) =
    if is_prims_ns ns then
        List.tryFind (fun (y, _, _) -> x = y) infix_prim_ops
    else if is_low_ns ns then
        List.tryFind (fun (y, _, _) -> x = y) infix_low_ops
    else
        None

(* -------------------------------------------------------------------- *)
let is_bin_op (p : mlpath) =
    as_bin_op p <> None

(* -------------------------------------------------------------------- *)
let as_uni_op ((ns, x) : mlpath) =
    if is_prims_ns ns then
        List.tryFind (fun (y, _) -> x = y) prim_uni_ops
    else
        None

(* -------------------------------------------------------------------- *)
let is_uni_op (p : mlpath) =
    as_uni_op p <> None

(* -------------------------------------------------------------------- *)
let as_standard_type ((ns, x) : mlpath) =
    if is_prims_ns ns then
        List.tryFind (fun (y, _) -> x = y) prim_types
    else
        None

(* -------------------------------------------------------------------- *)
let is_standard_type (p : mlpath) =
  as_standard_type p <> None

(* -------------------------------------------------------------------- *)
let as_standard_constructor ((ns, x) : mlpath) =
    if is_prims_ns ns then
        List.tryFind (fun (y, _) -> x = y) prim_constructors
    else
        None

(* -------------------------------------------------------------------- *)
let is_standard_constructor (p : mlpath) =
  as_standard_constructor p <> None

(* -------------------------------------------------------------------- *)
let maybe_paren (outer, side) inner doc =
  let noparens _inner _outer side =
    let (pi, fi) = _inner in
    let (po, fo) = _outer in
    (pi > po) ||
     (match (fi, side) with
      | Postfix    , Left     -> true
      | Prefix     , Right    -> true
      | Infix Left , Left     -> (pi = po) && (fo = Infix Left )
      | Infix Right, Right    -> (pi = po) && (fo = Infix Right)
      | Infix Left , ILeft    -> (pi = po) && (fo = Infix Left )
      | Infix Right, IRight   -> (pi = po) && (fo = Infix Right)
      | _          , NonAssoc -> (pi = po) && (fi = fo)
      | _          , _        -> false)
  in

  if noparens inner outer side then doc else parens doc

(* -------------------------------------------------------------------- *)
let ocaml_u8_codepoint (i : byte) =
  if (int_of_byte i) = 0 then "\\x00" else "\\x"^(hex_string_of_byte i)

(* -------------------------------------------------------------------- *)
let encode_char c =
  if (int_of_char c) > 127 then // Use UTF-8 encoding
    let bytes = string_of_char c in
    let bytes = unicode_of_string bytes in
    FStar.Bytes.f_encode ocaml_u8_codepoint bytes
  else
   (match c with
    | c when (c = '\\')              -> "\\\\"
    | c when (c = ' ')               -> " "
    | c when (c = '\b')              -> "\\b"
    | c when (c = '\t')              -> "\\t"
    | c when (c = '\r')              -> "\\r"
    | c when (c = '\n')              -> "\\n"
    | c when (c = '\'')              -> "\\'"
    | c when (c = '\"')              -> "\\\""
    | c when is_letter_or_digit(c) -> string_of_char c
    | c when is_punctuation(c)   -> string_of_char c
    | c when is_symbol(c)        -> string_of_char c
    | _                          -> ocaml_u8_codepoint (byte_of_char c))

(* -------------------------------------------------------------------- *)
let string_of_mlconstant (sctt : mlconstant) =
  match sctt with
  | MLC_Unit           -> ""
  | MLC_Bool     true  -> "1"
  | MLC_Bool     false -> "0"
  | MLC_Char     c     -> "'"^(encode_char c)^"'"
  | MLC_Byte     c     -> "'"^(ocaml_u8_codepoint c)^"'"
  | MLC_Int32    i     -> string_of_int32  i
  | MLC_Int64    i     -> (string_of_int64 i)^"L"
  | MLC_Int      s     -> if !Options.use_native_int  
                          then s
                          else "(Prims.parse_int \"" ^s^ "\")"
  | MLC_Float    d     -> string_of_float d

  | MLC_Bytes bytes ->
      let bytes = FStar.Bytes.f_encode ocaml_u8_codepoint bytes in
      "\""^bytes^"\""

  | MLC_String chars ->
      let chars = String.collect encode_char chars in
      "\""^chars^"\""

(* -------------------------------------------------------------------- *)
// Debug functions
let tag_of_expr e =
    match e.expr with
    | MLE_Const _ -> "MLE_Const"
    | MLE_Var _ -> "MLE_Var"
    | MLE_Name _ -> "MLE_Name"
    | MLE_Let _ -> "MLE_Let"
    | MLE_App _ -> "MLE_App"
    | MLE_Fun _ -> "MLE_Fun"
    | MLE_Match _ -> "MLE_Match"
    | MLE_Coerce _ -> "MLE_Coerce"
    | MLE_CTor _ -> "MLE_CTor"
    | MLE_Seq _ -> "MLE_Seq"
    | MLE_Tuple _ -> "MLE_Tuple"
    | MLE_Record _ -> "MLE_Record"
    | MLE_Proj _ -> "MLE_Proj"
    | MLE_If _ -> "MLE_If"
    | MLE_Raise _ -> "MLE_Raise"
    | MLE_Try _ -> "MLE_Try"


(* -------------------------------------------------------------------- *)
// Flags & state
type flag = | Yes | No | Unknown

let return_flag = ref Unknown // true if return statement is to be printed
let statement_printed_flag = ref Unknown // If statement has already been printed (e.g. with SBuffer.create)
let end_of_block_flag = ref Unknown // true if the last statement of a block e.g. 'if' or 'switch' block is reached
let application_flag = ref Unknown  // true if the next var to be printed is a function (and thus the module name has to 
                                    // be prepended to it

let current_type = ref MLTY_Top // if a cast is required
let current_module = ref "" // name of the current module (to append to function names, datacons etc.)
let current_match = ref "" // String of the inner most match being processed
let last_bound = ref "" // var name to which a 'match' of a 'if' is bound : let v = match ...


let map_datacon_to_field_num : Map<string, int> ref = ref (Map.empty)
let unions : List<string> ref = ref (List.empty)

(* -------------------------------------------------------------------- *)
// Regular expressions 
let parse_int_regex  = new System.Text.RegularExpressions.Regex "\(Prims\.parse_int \"([0-9a-fA-FxX]+)\"\)"
let parse_int_regex2 = new System.Text.RegularExpressions.Regex "\([\w\s_]+->[\s]+\(Prims\.parse_int \"([0-9a-fA-FxX]+)\"\)\)"
let implicit_regex   = new System.Text.RegularExpressions.Regex "\([\w\s_]+->[\s]+([0-9a-fA-FxX]+)\)"
let projector_regex1 = new System.Text.RegularExpressions.Regex "___([\w_]+)____([0-9]+)"
let projector_regex2 = new System.Text.RegularExpressions.Regex "([\w_\.]+)____([\w_]+)____([0-9]+)[\s]+(\([\w\s_]+\)|[\w]+)"
let projector_regex3 = new System.Text.RegularExpressions.Regex "____([\w_]+)____([0-9]+)[\s]+(\([\w\s_]+\))"

(* -------------------------------------------------------------------- *)
// Printing functions
let is_lib_fun e =
    List.contains e ["Prims_parse_int"; 
                     "SBuffer_create"; "SBuffer_index"; "SBuffer_upd"; "SBuffer_offset"; "SBuffer_blit"; "SBuffer_sub"; 
                     "FStar_UInt32_of_string"; "FStar_UInt32_of_int";
                     "FStar_SBytes_uint32_of_sbytes"]

let string_of_mlident (ident:mlident) : string =
    let sym, _ = ident in
    let sym = sym.Replace("'", "_prime") in
    sym

let rec string_of_ml_type (t:mlty) : string =
    match t with
    | MLTY_Var v -> string_of_mlident v
    | MLTY_Named (typs, path) -> 
        let typ = string_of_mlpath path in
        begin
        let typ = match typ with
                | "Prims.unit" -> "void"
                | "Prims.int" -> "int"
                | "Prims.nat" -> "int"
                | "Prims.pos" -> "int"
                | "Prims.char" -> "char"
                | "Prims.string" -> "char*"
                | "Prims.Tuple2" -> "_tuple2"
                | "FStar.ST.ref" -> "*"
                | "UInt.uint_std" -> "limb"  // TODO: remove
                | "UInt.uint_wide" -> "wide" // TODO: remove
                | "FStar.UInt8.uint8" -> "char"
                | "FStar.SBytes.uint32" -> "uint32"
                | "FStar.SBytes.sbytes" -> "uint8*"
                | "FStar.UInt32.uint32" -> "uint32"
                | "FStar.UInt63.uint63" -> "uint64"
                | "FStar.UInt64.uint64" -> "uint64"
                | "FStar.UInt64.uint128" -> "uint128"
                | "SBuffer.buffer" -> "*" // Should not appears, only the type bellow should appear in non library code
                | "SBuffer.uint8s" -> "uint8*"
                | "SBuffer.uint32s" -> "uint32*"
                | "SBuffer.uint63s" -> "uint64*"
                | "SBuffer.uint64s" -> "uint64*"
                | "SBuffer.uint128s" -> "uint128*"
                | _ -> typ.Replace('.', '_') in
        let other_types = List.map string_of_ml_type typs in
        let s = List.fold (fun s x -> s ^ x) "" (other_types@[typ]) in
        if s = "voidSint_usint" then "uint" else s
        end
    | MLTY_Fun (t1, tag, t2) -> 
        string_of_ml_type t2 // prints the returned type only
         //"Backend error : print of mlty_fun not implemented\n"
    | MLTY_Tuple _ ->  "Backend error : print of mlty_tuple not implemented\n"
    | MLTY_Top -> "Backend error : print of mlty_top not implemented\n"

let string_of_record (r:list<(mlsymbol * mlty)>) : string =
    let print_field (f:mlsymbol * mlty) = string_of_ml_type (snd f) ^ " " ^ (fst f) ^ ";\n" in
    "{\n" ^ (List.fold (fun s x -> s + print_field x) "" r) ^ "}"

let string_of_datacon dc = 
    let s = "{\n" in
    let ctr = ref 0 in
    let print_field f = (ctr := !ctr + 1; string_of_ml_type f ^ " field_" ^ (string !ctr) ^ ";\n") in
    let s = List.fold (fun s x -> s ^ (print_field x)) s (snd dc) in
    s ^ "}"

let string_of_union name u = 
    let s = "{\nunsigned char tag;\nunion {\n" in
    let print_field f = (name ^ "_" ^ (fst f)) ^ " " ^ (((fst f).ToLower())) ^ ";\n" in
    let s = List.fold (fun s x -> s ^ (print_field x)) s u in
    s ^ "} content;\n}"

let string_of_string (x:string) : string =
    let s = 
        match x with
        | _ -> x in
    // Prepend the module name to a function is necessary
    let s = if !application_flag = Yes && not(s.Contains(".")) then !current_module ^ "_" ^ s else s in
    // Replace the "Prims.parse_int" calls
    let s = parse_int_regex.Replace(s, "$1") in
    // Replace ocaml namespaces with flag names
    let s = s.Replace(".", "_") in
    let s = s.Replace("'", "_prime") in
    let s = s.Replace("FStar_ST_read", "*") in
    s

let replace_projectors s =
    if projector_regex2.IsMatch(s) then 
        projector_regex2.Replace(s, "$1_$2_get_field_$3($4)")
        //projector_regex2.Replace(s, "($4).content.$2.field_$3" )
    else if projector_regex3.IsMatch(s) then 
        projector_regex3.Replace(s, !current_module ^ "_$1_get_field_$2($3)")
        //projector_regex3.Replace(s, "($3).content.$1.field_$2" )
    else s

let replace_constant s =
    if parse_int_regex2.IsMatch(s) then parse_int_regex2.Replace(s, "$1") else s

let strip_from_paren (s:string) =
    let len = s.Length in
    let start = s.[0] in let stop = s.[len-1] in
    if (start = '(' && stop = ')') || (start = '[' && stop = ']') || (start = '{' && stop = '}')
    then s.Substring(1, len-2)
    else s

(* -------------------------------------------------------------------- *)
// Environment maintaining functions 


(* -------------------------------------------------------------------- *)
// Utility functions, not optimized
let is_unit (t:mlty) : bool = 
    match t with
    | MLTY_Named (_, (["Prims"],"unit")) -> true
    | _ -> false

let is_deepest_let (e:mlexpr) =
    match e.expr with
    | MLE_Const _ 
    | MLE_Var _
    | MLE_CTor _
    | MLE_App _
    | MLE_Record _
    | MLE_Tuple _
    | MLE_Raise _
    | MLE_Coerce _
    | MLE_Proj _
    | MLE_Name _ -> if !return_flag = Unknown || !return_flag = Yes then Yes else No
    | MLE_Seq([]) -> if !return_flag = Unknown || !return_flag = Yes then Yes else No
    | MLE_Seq(e::[]) -> if !return_flag = Unknown || !return_flag = Yes then Yes else No
    | MLE_Seq _
    | MLE_Try _
    | MLE_If _
    | MLE_Match _
    | MLE_Fun _
    | MLE_Let _ -> if !return_flag = No then No else Unknown

let is_last_in_block (e:mlexpr) =
    match e.expr with
    | MLE_Const _ 
    | MLE_Var _
    | MLE_CTor _
    | MLE_App _
    | MLE_Record _
    | MLE_Tuple _
    | MLE_Raise _
    | MLE_Coerce _
    | MLE_Proj _
    | MLE_Name _ -> if !end_of_block_flag = Unknown || !end_of_block_flag = Yes then Yes else No
    | MLE_Seq([]) -> if !end_of_block_flag = Unknown || !end_of_block_flag = Yes then Yes else No
    | MLE_Seq(e::[]) -> if !end_of_block_flag = Unknown || !end_of_block_flag = Yes then Yes else No
    | MLE_Seq _
    | MLE_Try _
    | MLE_If _
    | MLE_Match _
    | MLE_Fun _
    | MLE_Let _ -> Unknown    

let is_projector (m:mlmodule1) : bool =
    match m with
    // Test based on the name of the projector (supposedly of the form __DCTOR___X)
    | MLM_Let(false,[lb]) -> if projector_regex1.IsMatch(string_of_mlident lb.mllb_name) then true else false
    | _ -> false
        
let is_instance_of (m:mlmodule1) : bool =
    match m with
    | MLM_Let(false,[lb]) -> 
        ( match lb.mllb_def.expr with
        | MLE_Fun([(id, ty)], e) -> if string_of_mlident id = "_discr_" then true else false
        | _ -> false )
    | _ -> false

let is_mk_record (m:mlmodule1) : bool =
    match m with
    | MLM_Let(false, [lb]) -> (
        match lb.mllb_def.expr with
        | MLE_Coerce _ -> if (string_of_mlident lb.mllb_name).Contains("is_Mk") then true else false
        | _ -> false )
    | _ -> false

let rec is_if_or_match (m:mlexpr) =
    match m.expr with
    | MLE_If _ 
    | MLE_Match _ -> true
    | MLE_Coerce (e, t1, t2) -> is_if_or_match e
    | MLE_Seq(li) -> is_if_or_match (List.hd (List.rev li))
    | _ -> false

(* -------------------------------------------------------------------- *)
let rec doc_of_mltype' (currentModule : mlsymbol) (outer : level) (ty : mlty) =
    match ty with
    | MLTY_Var x ->
        let escape_tyvar s =
            if Util.starts_with s "'_" //this denotes a weak type variable in OCaml; it cannot be written in source programs
            then Util.replace_char s '_' 'u'
            else s in
        text (escape_tyvar <| idsym x)

    | MLTY_Tuple tys ->
        let doc = List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys in
        let doc = parens (hbox (combine (text " * ") doc)) in
        doc

    | MLTY_Named (args, name) -> begin
        let args =
            match args with
            | []    -> empty
            | [arg] -> doc_of_mltype currentModule (t_prio_name, Left) arg
            | _     ->
                let args = List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
                parens (hbox (combine (text ", ") args))

        in

        let name =
          if is_standard_type name then
            snd (Option.get (as_standard_type name))
          else
            ptsym currentModule name

        in hbox (reduce1 [args; text name])
    end

    | MLTY_Fun (t1, _, t2) ->
        let d1 = doc_of_mltype currentModule (t_prio_fun, Left ) t1 in
        let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
        maybe_paren outer t_prio_fun (hbox (reduce1 [d1; text " -> "; d2]))

    | MLTY_Top ->
      if Util.codegen_fsharp()
      then text "obj"
      else text "Obj.t"

and doc_of_mltype (currentModule : mlsymbol) (outer : level) (ty : mlty) =
    doc_of_mltype' currentModule outer (Util.resugar_mlty ty)

(* -------------------------------------------------------------------- *)
let rec string_of_expr (currentModule : mlsymbol) (outer : level) (e : mlexpr) : string =
    let mk_last_statement (d:string) = 
        //Console.WriteLine(d ^ " -> " ^ !last_bound ^ " | " ^ (if !end_of_block_flag = Unknown then "Unknown" else if !end_of_block_flag = Yes then "Yes" else "No"));
        if !return_flag = Yes then (
            //print_string (tag_of_expr e ^ "\n");
            concat1 ["return "; d; ";"] )
        else if !statement_printed_flag = Yes then
            begin
                statement_printed_flag := No;
                d
            end
        else if !end_of_block_flag = Yes then 
            begin
                let s = if !last_bound = "" then concat1 [d; ";"] else concat1 [!last_bound; "="; d; ";"] in
                last_bound := "";
                end_of_block_flag := Unknown;
                s
            end
        else d in
    match e.expr with
    | MLE_Coerce (e, t, t') ->
        "\nBackend error in doc_of_expr : MLE_Coerce not handled \n"
//      let doc = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
//      if Util.codegen_fsharp()
//      then parens (reduce [text "Prims.checked_cast"; doc])
//      else parens (reduce [text "Obj.magic "; doc])

    | MLE_Seq es ->
        let end_of_block_init = !end_of_block_flag in
        let seq = List.map (string_of_expr currentModule (min_op_prec, NonAssoc)) es in
        let seq = List.map (fun d -> concat [d; ";"; new_line]) seq in
        let seq_length = List.length seq in
        let seq = List.mapi (fun i e -> if i = seq_length - 1 then mk_last_statement e else e) seq in
        concat seq

    | MLE_Const c ->
        let constant = string_of_mlconstant c in
//        Console.WriteLine("Const : " ^ constant);
        let constant = string_of_string constant in
        mk_last_statement (constant)

    | MLE_Var (x, _) ->
//        Console.WriteLine("Var : " ^ x);
        let var = string_of_string x in
        mk_last_statement (var)

    | MLE_Name path ->
        let name = ptsym currentModule path in
        let name = string_of_string name in
//        Console.WriteLine(name);
        mk_last_statement (name)

    | MLE_Record (path, fields) ->
        let for1 (name, e) =
            let doc = string_of_expr currentModule (min_op_prec, NonAssoc) e in
//            reduce1 [text (ptsym currentModule (path, name)); text "="; doc] in
            concat1 [doc] in
        let record = cbracket (concat2 (", ") (List.map for1 fields)) in
        let cast = concat1 [paren ((string_of_ml_type !current_type)); record] in
        mk_last_statement (cast)

    | MLE_CTor (ctor, []) ->
        // TODO
       let name =
         if is_standard_constructor ctor then
           snd (Option.get (as_standard_constructor ctor))
         else
           ptctor currentModule  ctor in
        mk_last_statement (name)

    | MLE_CTor (ctor, args) ->
       let name = snd ctor in
//         if is_standard_constructor ctor then
//           snd (Option.get (as_standard_constructor ctor))
//         else
//           ptctor currentModule  ctor in
        let args = List.map (string_of_expr currentModule (min_op_prec, NonAssoc)) args in
        let doc =
          match name, args with
            (* Special case for Cons *)
            | "::", [x;xs] -> "\nBackend error in doc_of_expr : lists not handled \n" //reduce [parens x; text "::"; xs]
            | _, _ -> concat1 [concat2 (", ") args] in
//        maybe_paren outer e_app_prio doc
        let full_name = string_of_ml_type (!current_type) ^ "_" ^ name in
        let field_num = match Map.tryFind full_name !map_datacon_to_field_num with | Some n -> n | _ -> 0 in
        let obj = if field_num = 0 then cbracket doc else cbracket (concat1 [string field_num; ","; cbracket doc]) in
        let cast = concat1 [paren ((string_of_ml_type !current_type (* ^ "_" ^ name *))); obj] in
        mk_last_statement (cast)
    | MLE_Tuple es ->
        let docs = List.map (string_of_expr currentModule (min_op_prec, NonAssoc)) es in
        let docs = cbracket (concat2 (", ") docs) in
        let cast = concat1 [paren ((string_of_ml_type !current_type)); docs] in
        mk_last_statement cast

    | MLE_Let ((rec_, lets), body) ->

        // no return necessary for 'e1' in let x = e1 in e2 so set flag to 'No'
        let return_flag_init = !return_flag in
        return_flag := No;
        let end_of_block_flag_init = !end_of_block_flag in
        end_of_block_flag := Unknown;

        // Different ways to handle it depending on the nature of the enclosed expression
        let doc  = string_of_lets currentModule (rec_, false, lets) in

       // Check nature of the body
        return_flag := return_flag_init;
        return_flag := is_deepest_let body;
        end_of_block_flag := is_last_in_block body;
        
        let body' = string_of_expr  currentModule (min_op_prec, NonAssoc) body in

        // Restore flags
        return_flag := return_flag_init;
        end_of_block_flag := end_of_block_flag_init;
        cbracket (concat2 new_line [" "; doc; concat1 [body']; " "])

    | MLE_App (e, args) -> begin
        let return_flag_init = !return_flag in
        return_flag := No;
        let end_of_block_flag_init = !end_of_block_flag in
        end_of_block_flag := No;
//        return_flag := Unknown;
        let doc = 
//            Console.WriteLine (" " ^ tag_of_expr e);

            match e.expr, args with
            | (MLE_Name p, [e1; e2]) when is_bin_op p -> (
                let return_flag_init = !return_flag in
                let end_of_block_init = !end_of_block_flag in
                return_flag := No;
                end_of_block_flag := No;
                let s = string_of_binop currentModule p e1 e2 in
                return_flag := return_flag_init;
                end_of_block_flag := end_of_block_init;
                s)
            | (MLE_App ({expr=MLE_Name p},[unitVal]), [e1; e2]) when (is_bin_op p && unitVal=ml_unit) -> (
                let return_flag_init = !return_flag in
                let end_of_block_init = !end_of_block_flag in
                return_flag := No;
                end_of_block_flag := No;
                let s = string_of_binop currentModule p e1 e2 in
                return_flag := return_flag_init;
                end_of_block_flag := end_of_block_init;
                s )
            | (MLE_Name p, [e1]) when is_uni_op p -> (
                let return_flag_init = !return_flag in
                let end_of_block_init = !end_of_block_flag in
                return_flag := No;
                end_of_block_flag := No;
                let s = string_of_uniop currentModule p e1 in
                return_flag := return_flag_init;
                end_of_block_flag := end_of_block_init;
                s )
            | (MLE_App ({expr=MLE_Name p},[unitVal]), [e1]) when (is_uni_op p  && unitVal=ml_unit) -> (
                let return_flag_init = !return_flag in
                let end_of_block_init = !end_of_block_flag in
                return_flag := No;
                end_of_block_flag := No;
                let s = string_of_uniop currentModule p e1 in
                return_flag := return_flag_init;
                end_of_block_flag := end_of_block_init;
                s )
            | _ ->
                // Handle library functions 
                application_flag := Yes;
                let return_flag_init = !return_flag in
                let end_of_block_init = !end_of_block_flag in
                return_flag := No;
                end_of_block_flag := No;
                let e' = e in
                let e    = string_of_expr  currentModule (e_app_prio, ILeft) e in
                return_flag := return_flag_init;
                end_of_block_flag := end_of_block_init;
                //Console.WriteLine e;
                //Console.WriteLine (tag_of_expr e');
                application_flag := No;
                if is_lib_fun e then string_of_lib_functions currentModule e args
                else                     
                    let args = List.map (string_of_expr currentModule  (e_app_prio, IRight)) args in
                    let args = paren (concat2 (", ") args) in
                    concat1 [e; args] 
                in
        let doc = replace_projectors doc in
        end_of_block_flag := end_of_block_flag_init;
        return_flag := return_flag_init;
        mk_last_statement doc
    end

    | MLE_Proj (e, f) ->
       let e = string_of_expr  currentModule  (min_op_prec, NonAssoc) e in
       let doc =
        if Util.codegen_fsharp() //field names are not qualified in F#
        then concat [e; "."; (snd f)]
        else concat [e; "."; (ptsym currentModule f)] in
       doc

    | MLE_Fun (ids, body) ->
        //Console.WriteLine (concat1 (List.map (fun (x,y) -> string_of_mlident x) ids));
        let bvar_annot x xt =
            match xt with 
            | Some xxt when (string_of_ml_type xxt = "void") -> None
            | Some xxt -> Some (concat1 [string_of_ml_type xxt; x])
            | _ -> Some "void*" in
                
//            if Util.codegen_fsharp() //type inference in F# is not complete, particularly for field projections; so these annotations are needed
//            then concat1 ["("; x ;
//                          (match xt with | Some xxt -> concat1 [" : "; doc_of_mltype currentModule outer xxt] | _ -> "");
//                          ")"]
//            else x in
        let ids  = List.fold (fun l ((x, _),xt) -> match bvar_annot (string_of_string x) (Some xt) with | Some v -> l@[v] | _ -> l) [] ids in
        let vars = paren (concat2 (", ") ids) in

        // Handle returns
        let return_flag_init = !return_flag in
        return_flag := is_deepest_let body;

        let body' = string_of_expr currentModule (min_op_prec, NonAssoc) body in
        return_flag := return_flag_init;
        let doc  = concat1 [vars; "{\n"; body'; "\n}\n"] in
        
//        Console.WriteLine(tag_of_expr body ^ "\n");
        
        doc

    | MLE_If (cond, e1, None) ->
        let cond = string_of_expr currentModule  (min_op_prec, NonAssoc) cond in
        let doc  =
            concat2 new_line [
                concat1 ["if("; cond; ")"; "{"];
                string_of_expr currentModule  (min_op_prec, NonAssoc) e1;
                "}"
            ]

        in doc

    | MLE_If (cond, e1, Some e2) ->
        let cond = string_of_expr currentModule  (min_op_prec, NonAssoc) cond in

        // Set the 'end_of_block' flag and print the blocks
        let end_of_block_init = !end_of_block_flag in
        end_of_block_flag := is_last_in_block e1;
        let e1_block = string_of_expr currentModule (min_op_prec, NonAssoc) e1 in
        end_of_block_flag := is_last_in_block e2;
        let e2_block = string_of_expr currentModule (min_op_prec, NonAssoc) e2 in
        end_of_block_flag := end_of_block_init;

        let if_statement  =
            concat2 new_line [
                concat1 ["if("; cond; ")"; "{"];
                e1_block;
                concat1 ["}"; "else"; "{"];
                e2_block;
                "}"
            ] in
        if_statement

    | MLE_Match (cond, pats) ->
        let cond' = string_of_expr currentModule  (min_op_prec, NonAssoc) cond in
        let cond_type = string_of_ml_type (cond.ty) in

        // Current type being matched on
        let current_match_init = !current_match in
        current_match := cond_type;

        let cond' = if List.contains cond_type !unions then (paren cond' ^ ".tag") else cond' in
        let pats = List.map (string_of_branch currentModule (string_of_ml_type cond.ty)) pats in
        let doc  = concat1 ["switch"; paren cond'; "{"] :: pats @ ["}"] in
        let doc  = concat2 new_line doc in

        // Reset
        current_match := current_match_init;

        paren doc

    | MLE_Raise (exn, []) ->
        // TODO
        mk_last_statement (concat1 ["raise"; (ptctor currentModule  exn)])

    | MLE_Raise (exn, args) ->
        // TODO 
        let args = List.map (string_of_expr currentModule  (min_op_prec, NonAssoc)) args in
        mk_last_statement (concat1 ["raise"; (ptctor currentModule  exn); paren (concat2 (", ") args)])

    | MLE_Try (e, pats) ->
        // TODO
        concat2 new_line [
            concat1 ["try"; "begin"];
            string_of_expr currentModule  (min_op_prec, NonAssoc) e;
            concat1 ["end"; "with"];
            (concat2 new_line (List.map (string_of_branch currentModule (string_of_ml_type e.ty)) pats))
        ]
and  string_of_binop currentModule p e1 e2 : string =
        let (_, prio, txt) = Option.get (as_bin_op p) in
        let e1  = string_of_expr  currentModule (prio, Left ) e1 in
        let e2  = string_of_expr  currentModule (prio, Right) e2 in
        let doc = concat1 [e1; txt; e2] in
        paren doc

and  string_of_uniop currentModule p e1  : string =
        let (_, txt) = Option.get (as_uni_op p) in
        let e1  = string_of_expr  currentModule  (min_op_prec, NonAssoc ) e1 in
        let doc = concat1 [txt; paren e1] in
        paren doc

and  string_of_lib_functions currentModule f args : string =
    
    // Returns a string corresponding to the size of the integer (either variable or constant). In non-library code 
    // should always be a constant
    let get_int_size v =
        let size = match v with
            | {expr = MLE_App ({expr = MLE_Fun(_, e')},_)} -> (
                string_of_expr currentModule (e_app_prio, IRight) e' )
            | {expr = MLE_Const _} -> (
                string_of_expr currentModule (e_app_prio, IRight) v )
            | _ -> (
                let s = string_of_expr currentModule (e_app_prio, IRight) v in            
                Console.WriteLine ("Warning: took default branch, size should be constant for non-lib files: " ^ s);
                s ) in
        size in

    match f with        
    // Remove the "Prims.parse_int" introduced calls
    | "Prims_parse_int" 
    // Current ways to introduce constants
    | "FStar_UInt32_of_string" ->
        let x = List.hd args in
        let (s:string) = string_of_expr currentModule (min_op_prec, NonAssoc) x in
        String.sub s 1 (String.length s - 2)
    | "FStar_UInt32_of_int" -> 
        let x = List.hd args in
        string_of_expr currentModule (min_op_prec, NonAssoc) x 
    // Should use casts between buffers instead
    | "FStar_SBytes_uint32_of_sbytes" ->
        begin
            let x = List.hd args in
            let s = string_of_expr currentModule (min_op_prec, NonAssoc) x in
            concat ["*(uint32*)"; s; ""]
        end
    | "SBuffer_create" -> 
        begin
            // TODO: FIXME, for now I will assume that the semantics of create always initializes with 0s
            let size = List.hd args in
            let size = get_int_size size in
            let args = List.map (string_of_expr currentModule  (e_app_prio, IRight)) (List.tl args) in
            match args with
            | [init; len] ->             
                begin
                    let s = concat ["uint"; size; " "; !last_bound; "["; len; "] = { 0 };"] in
                    statement_printed_flag := Yes;
                    s
                end
            | _ -> "Error with SBuffer.create"
        end
    | "SBuffer_index" -> 
        begin
        let args = List.map (string_of_expr currentModule (e_app_prio, IRight)) (List.tl args) in
        match args with
        | [b; idx] ->
            let idx = replace_constant idx in
            concat [b; "["; idx; "]"]
        | _ -> "Error with SBuffer.index"
        end
    | "SBuffer_upd" -> 
        begin
            let args = List.map (string_of_expr currentModule (e_app_prio, IRight)) (List.tl args) in
            match args with
            | [b; idx; v] ->
                let idx = replace_constant idx in
                concat1 [b; "["; idx; "] = "; v]
            | _ -> "Error with SBuffer.upd"
        end   
    | "SBuffer_offset"
    | "SBuffer_sub" -> 
        begin
            let size = List.hd args in
            let size = get_int_size size in
            let args = List.map (string_of_expr currentModule (e_app_prio, IRight)) (List.tl args) in
            let s = match args with
                | [b; idx] -> concat ["uint"; size; "* "; !last_bound; "=  ("; b; " + "; idx; ");"]
                | [b; idx; len] -> concat ["uint"; size; "* "; !last_bound; "=  ("; b; " + "; idx; ");"]
                | _ -> "Error with SBuffer.sub" in
            statement_printed_flag := Yes;
            s
        end
    | "SBuffer_split" -> "split(TODO)" // TODO: remove from the library functions
    | "SBuffer_blit" -> 
        begin
            let size = List.hd args in
            let args = List.map (string_of_expr currentModule (e_app_prio, IRight)) (List.tl args) in
            let end_of_block_flag_init = !end_of_block_flag in
            let return_flag_init = !return_flag in
            let size = get_int_size size in
            let size = concat ["(("; size; "+1)/8)"] in
            match args with
            | [src; src_idx; dest; dest_idx; len] -> (
                concat1 ["memcpy(("; dest; "+"; dest_idx; "), ("; src; "+"; src_idx; "), "; size;  "*"; len; ")"] )
            | _ -> "Error with blit" 
        end
//    | "FStar_SBytes_sbytes_of_uint32s" -> 
//        begin
//            let args = List.map (string_of_expr currentModule (e_app_prio, IRight)) args in
//            match args with
//            | 
//            ""
//        end 
    | _ -> "Error: unhandled lib function"

(* -------------------------------------------------------------------- *)
and string_of_pattern (currentModule : mlsymbol) (pattern : mlpattern) : string =
    match pattern with
    | MLP_Wild     -> "default:"
    | MLP_Const  c -> concat1 ["case "; (string_of_mlconstant c); ":"]
    | MLP_Var    x -> concat1 ["case "; (fst x); ":"]

    | MLP_Record (path, fields) -> "Backend error : pattern matching on records not supported"
//        let for1 (name, p) = concat1 [(ptsym currentModule  (path, name)); "="; string_of_pattern currentModule p] in
//        cbracket (concat2 ("; ") (List.map for1 fields))

    | MLP_CTor (ctor, []) ->
       let name =
         if is_standard_constructor ctor then
           snd (Option.get (as_standard_constructor ctor))
         else
           ptctor currentModule  ctor in
        name

    | MLP_CTor (ctor, pats) ->
       let name = !current_match ^ "_" ^ snd ctor in
       //let name = if name.Contains(".") then name.Replace(".", "_") else !current_module ^ "_" ^ name in
       let doc =
            match name, pats with
            (* Special case for Cons *)
            | "::", [x;xs] -> concat [string_of_pattern currentModule x; "::"; string_of_pattern currentModule xs]
            | _, [MLP_Tuple _] -> concat1 [name; string_of_pattern currentModule (List.hd pats)] //no redundant parens; particularly if we have (T of a * b), we must generate T (x, y) not T ((x, y))
            | _ -> 
                let field_num = Map.tryFind name !map_datacon_to_field_num in
                match field_num with
                | None -> "Backend error : did not find datacon matching " ^ name ^ "\n"
                | Some f -> "case " ^ (f.ToString()) ^ ":" in
       doc

    | MLP_Tuple ps ->
        "Backend error : string_of_pattern does not support tuples"

    | MLP_Branch ps ->
        "Backend error : string_of_pattern does not support branches"

(* -------------------------------------------------------------------- *)
and string_of_branch (currentModule : mlsymbol) (ty:string) ((p, cond, e) : mlbranch) : string =
    let case =
        match cond with
        | None   -> string_of_pattern currentModule p
        | Some c ->
            begin
                match c.expr with
                | MLE_App(f, args) -> begin
                    match f.expr with
                    | MLE_Name (path) -> 
                        let s = if string_of_mlpath path = "Prims.op_Equality" then string_of_expr currentModule (min_op_prec, NonAssoc) (List.nth args 1)
                                else "Backend error : 'when' clause expected '=' but got " ^ (string_of_mlpath path) in
                        concat1 ["case"; s; ":"]
                    | _ -> "Backend error : 'when' clause expected '=' but got " ^ (string_of_expr currentModule (min_op_prec, NonAssoc) c) ^" " ^ tag_of_expr f end
                | _ -> "Backend error : 'when' clause expected app eq but got " ^ (string_of_expr currentModule (min_op_prec, NonAssoc) c) ^" " ^ tag_of_expr c end
        in

    // Entering a new block so trying out the end of block flag
    let end_of_block_init = !end_of_block_flag in
    end_of_block_flag := is_last_in_block e;

    let branch = concat2 new_line [
        case;
        concat1 [string_of_expr currentModule  (min_op_prec, NonAssoc) e; ";"];
        "break;";
    ] in

    // Restore old flag
    end_of_block_flag := end_of_block_init;

    branch

(* -------------------------------------------------------------------- *)
and string_of_lets (currentModule : mlsymbol) (rec_, top_level, lets) =

    let ignored_types = ["FStar_Heap_heap"] in
    let custom_statement_types = [(["SBuffer"], "create");
                                  (["SBuffer"], "sub");
                                  (["SBuffer"], "offset")] in

    let print_decl (lb:mllb) = 
        match lb.mllb_def with
        | {expr=MLE_App({expr=MLE_Name p},_)} when List.contains p custom_statement_types-> ""
        | _ -> 
            begin
                match lb.mllb_tysc with
                | Some(_, MLTY_Fun (ty, tag, ty2)) -> "" //((string_of_ml_type ty) ^ " | " ^ (string_of_ml_type ty2)
                                                //^ " | " ^ (string_of_mlident lb.mllb_name))
                | Some(_,ty) when List.contains (string_of_ml_type ty) (ignored_types@[""]) -> ""
                | Some (ids, ty) -> 
                    if not(top_level) && not(is_unit ty) then ((string_of_ml_type (ty)) ^ " " ^ (string_of_mlident lb.mllb_name) ^ ";") 
                    else "" 
                | _ -> ""   // TODO: FIXME
            end in

    // Print declarations
    let decls = concat2 new_line (List.map print_decl lets) in

    let print_expr (lb:mllb) = 
        match lb.mllb_tysc with
        // Case of top level functions
        | Some(_, MLTY_Fun (ty, tag, ty2)) -> concat [(string_of_ml_type ty2); " ";
                                                currentModule; "_"; (string_of_mlident lb.mllb_name);
                                                string_of_expr currentModule (min_op_prec, NonAssoc) lb.mllb_def] 
        | Some(_,ty) when List.contains (string_of_ml_type ty) ignored_types -> ""
        | Some (tysc) -> 
            // Variable to bind to
            let last_bound_init = !last_bound in
            last_bound := if is_unit (snd tysc) then "" else string_of_mlident lb.mllb_name;

            let s =
            // Top level constants
            if top_level then concat1 ["const"; string_of_ml_type (snd tysc); string_of_mlident lb.mllb_name;  "="; 
                                        string_of_expr currentModule (min_op_prec, NonAssoc) lb.mllb_def; ";"]

            // If the expression is a 'match' of a 'if'
            else if is_if_or_match lb.mllb_def then
                // Name of the identifier to which to bind the result of the if of the match
                let last_bound_init = !last_bound in
                last_bound := string_of_mlident lb.mllb_name;
                // Type of the expression being printed 
                let current_type_init = !current_type in
                current_type := snd tysc;
                // Print body
                let body = concat [string_of_expr currentModule (min_op_prec, NonAssoc) lb.mllb_def] in
                let body = strip_from_paren body in
                // Restore flags
                last_bound := last_bound_init;
                current_type := current_type_init;
                body

            else
            
                let current_type_init = !current_type in
                current_type := snd tysc;
                let end_of_block_init = !end_of_block_flag in
                end_of_block_flag := is_last_in_block lb.mllb_def;
                let body = string_of_expr currentModule (min_op_prec, NonAssoc) lb.mllb_def in
//                    if is_unit (snd tysc) then  concat [string_of_expr currentModule (min_op_prec, NonAssoc) lb.mllb_def;";"]
//                    else concat   [(string_of_mlident lb.mllb_name ^ " = "); 
//                                  string_of_expr currentModule (min_op_prec, NonAssoc) lb.mllb_def; ";"] in
                current_type := current_type_init;
                end_of_block_flag := end_of_block_init;
                body 

            in
            last_bound := last_bound_init;
            s
        | _ -> "Error, unhandled pattern in string_of_lets" // TODO: FIXME
            in
    let exprs = concat2 new_line (List.map print_expr lets) in
    concat2 new_line (decls::exprs::[])
//    let for1 {mllb_name=name; mllb_tysc=tys; mllb_def=e} =
//        let e   = doc_of_expr currentModule  (min_op_prec, NonAssoc) e in
//        let ids = [] in //TODO: maybe extract the top-level binders from e and print it alongside name
//        //let f x = x
//        //let f = fun x -> x
//        //i.e., print the latter as the former
//        let ids = List.map (fun (x, _) -> text x) ids in
//        let ty_annot =
//            if Util.codegen_fsharp () && (rec_ || top_level) //needed for polymorphic recursion and to overcome incompleteness of type inference in F#
//            then match tys with
//                    | (_::_, _) -> //except, emitting binders for type variables in F# sometimes also requires emitting type constraints; which is not yet supported
//                      text ""
//                    | ([], ty) ->
//                      let ty = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty in
//                      reduce1 [text ":"; ty]
////                      let ids = List.map (fun (x, _) -> text x) ids in
////                      begin match ids with
////                        | [] -> reduce1 [text ":"; ty]
////                        | _ ->  reduce1 [text "<"; combine (text ", ") ids; text ">"; text ":"; ty]
////                      end
//            else text "" in
//        reduce1 [text (idsym name); reduce1 ids; ty_annot; text "="; e] in
//
//    let letdoc = if rec_ then reduce1 [text "let"; text "rec"] else text "let" in
//
//    let lets = List.map for1 lets in
//    let lets = List.mapi (fun i doc ->
//        reduce1 [(if i = 0 then letdoc else text "and"); doc])
//        lets in
//
//    combine hardline lets

(* -------------------------------------------------------------------- *)
let doc_of_mltydecl (currentModule : mlsymbol) (decls : mltydecl) =
    let for1 (x, tparams, body) =
        let tparams =
            match tparams with
            | []  -> empty
            | [x] -> text (idsym x)
            | _   ->
                let doc = List.map (fun x -> (text (idsym x))) tparams in
                parens (combine (text ", ") doc) in

        let forbody (body : mltybody) =
            match body with
            | MLTD_Abbrev ty ->
                doc_of_mltype currentModule  (min_op_prec, NonAssoc) ty

            | MLTD_Record fields -> begin
                let forfield (name, ty) =
                    let name = text name in
                    let ty   = doc_of_mltype currentModule  (min_op_prec, NonAssoc) ty in
                    reduce1 [name; text ":"; ty]

                in cbrackets (combine (text "; ") (List.map forfield fields))
            end

            | MLTD_DType ctors ->
                let forctor (name, tys) =
                    match tys with
                    | [] -> text name
                    | _  ->
                        let tys = List.map (doc_of_mltype currentModule  (t_prio_tpl, Left)) tys in
                        let tys = combine (text " * ") tys in
                        reduce1 [text name; text "of"; tys]
                in

                let ctors = List.map forctor ctors in
                let ctors = List.map (fun d -> reduce1 [text "|"; d]) ctors in
                combine hardline ctors

        in

        let doc = reduce1 [tparams; text (ptsym currentModule  ([], x))] in

        match body with
        | None      -> doc
        | Some body ->
            let body = forbody body in
            combine hardline [reduce1 [doc; text "="]; body]

    in

    let doc = List.map for1 decls in
    let doc = if (List.length doc >0) then reduce1 [text "type"; combine (text " \n and ") doc] else text "" in
    doc

(* -------------------------------------------------------------------- *)
let rec doc_of_sig1 currentModule s =
    match s with
    | MLS_Mod (x, subsig) ->
        combine hardline
            [reduce1 [text "module"; text x; text "="];
             doc_of_sig currentModule subsig;
             reduce1 [text "end"]]

    | MLS_Exn (x, []) ->
        reduce1 [text "exception"; text x]

    | MLS_Exn (x, args) ->
        let args = List.map (doc_of_mltype currentModule  (min_op_prec, NonAssoc)) args in
        let args = parens (combine (text " * ") args) in
        reduce1 [text "exception"; text x; text "of"; args]

    | MLS_Val (x, (_, ty)) ->
        let ty = doc_of_mltype currentModule  (min_op_prec, NonAssoc) ty in
        reduce1 [text "val"; text x; text ": "; ty]

    | MLS_Ty decls ->
        doc_of_mltydecl currentModule decls

(* -------------------------------------------------------------------- *)
and doc_of_sig (currentModule : mlsymbol) (s : mlsig)  =
    let docs = List.map (doc_of_sig1 currentModule) s in
    let docs = List.map (fun x -> reduce [x; hardline; hardline]) docs in
    reduce docs

(* -------------------------------------------------------------------- *)
let doc_of_mod1 (currentModule : mlsymbol) (m : mlmodule1) =
    match m with
    | MLM_Loc(_) -> text ""
    | MLM_Exn (x, []) ->
        text "Backend error : exceptions are not handled"
        //reduce1 [text "exception"; text x]

    | MLM_Exn (x, args) ->
        text "Backend error : exceptions are not handled"
//        let args = List.map (doc_of_mltype currentModule  (min_op_prec, NonAssoc)) args in
//        let args = parens (combine (text " * ") args) in
//        reduce1 [text "exception"; text x; text "of"; args]

    | MLM_Ty decls ->
        let print_decl (decl:mlsymbol * mlidents * option<mltybody>) =
            let name, ids, body = decl in
            let dtype_name = currentModule ^ "_" ^ ptsym_of_symbol name in
            let s = match body with
            | Some (MLTD_Abbrev ty) -> "typedef " ^ (string_of_ml_type ty) ^ " " ^ (dtype_name)
            | Some (MLTD_Record r) -> 
                let declaration = "typedef struct " ^ (dtype_name) ^ " " ^ (dtype_name) in
                let body = "struct " ^ (dtype_name) ^ (string_of_record r) in
                declaration ^ ";\n" ^ body ^ ";\n"
            | Some (MLTD_DType dt) ->
                begin
                    match dt with
                    | [] -> failwith "Backend error : emtpy dataconstructor\n"
                    | [(ctor_id, ctor_typ)] -> 

                        // Add the datacon to map :
                        map_datacon_to_field_num := Map.add (dtype_name ^ "_" ^ ctor_id) 0 !map_datacon_to_field_num;

                        // Two declarations so that it can be used with or without the datacon appended to the type 
                        let declaration = "typedef struct " ^ (dtype_name) ^ " " ^ (currentModule) ^ "_" ^ ctor_id in
                        let declaration2 = "typedef struct " ^ (dtype_name) ^ " " ^ (dtype_name)  in
                        let body = "struct " ^ (dtype_name) ^ (string_of_datacon (ctor_id, ctor_typ)) in
                        declaration ^ ";\n" ^ declaration2 ^ ";\n" ^ body ^ ";\n"
                    | _ ->
                        let ctr = ref 0 in
                        let full_name ctor_name = (dtype_name) ^ "_" ^ ctor_name in
                        let short_name ctor_name = currentModule ^ "_" ^ ctor_name in

                        // Printing functions
                        let print_declaration = fun d ->
                            // Add the datacon to map :
                            ctr := !ctr+1;
                            map_datacon_to_field_num := Map.add (full_name (fst d)) !ctr !map_datacon_to_field_num;

                            "typedef struct " ^  full_name (fst d) ^ " " ^ short_name (fst d) ^ ";\n" in
                        let print_body = fun d ->
                            "struct " ^ full_name (fst d) ^ (string_of_datacon d) ^ ";\n" in

                        let declarations = List.fold (fun s x -> s ^ (print_declaration x)) "" dt in
                        let bodies = List.fold (fun s x -> s ^ (print_body x)) "" dt in
                        let union = "struct " ^ dtype_name ^ string_of_union currentModule dt ^ ";\n" in
                        (declarations ^ bodies ^ union)
                end
                            
            | None -> "" in
            text s in
        let print_union_decl (decl:mlsymbol * mlidents * option<mltybody>) =
            let name, _, body = decl in
            let dtype_name = currentModule ^ "_" ^ ptsym_of_symbol name in

             // Add union to state union list
            unions := dtype_name::!unions;
            
            match body with 
            | Some (MLTD_DType (e1::e2::tl)) -> 
                let s = "typedef struct " ^ dtype_name ^ " " ^ dtype_name ^";" in
                text s
            | _ -> text "" in

        let print_discriminators (decl:mlsymbol * mlidents * option<mltybody>) =
            let name, _, body = decl in
            let dtype_name = currentModule ^ "_" ^ ptsym_of_symbol name in
            
            match body with 
            | Some(MLTD_DType ([(ctor_id, typs)])) -> 
                text (concat ["int "; currentModule; "_is_"; ctor_id; "("; dtype_name; " blah){\n return 1;\n}\n"])
            | Some (MLTD_DType (l)) -> 
                let ctr = ref 0 in
                let print_discr (ctor_id,li) =
                    let head = concat ["int "; currentModule; "_is_"; ctor_id; "("; dtype_name; " blah){\n"] in
                    ctr := !ctr + 1;
                    let body = concat ["return ((blah.tag == "; string !ctr; ") ? (1) : (0));\n}\n"] in
                    concat [head; body] in
                text (concat (List.map print_discr l))
            | _ -> text "" in

        let print_projectors (decl:mlsymbol * mlidents * option<mltybody>) =
            let name, ids, body = decl in
            let dtype_name = currentModule ^ "_" ^ ptsym_of_symbol name in
            let s = 
            match body with 
            | Some(MLTD_DType ([(ctor_id, typs)])) -> 
                let ctr = ref 0 in
                let print_proj typ = 
                    ctr := !ctr + 1;
                    let head = concat [string_of_ml_type typ; " "; currentModule; "_"; ctor_id; "_get_field_"; string !ctr;
                                    "("; dtype_name; " x){\n"] in
                    let body = concat ["return x.field_"; string !ctr; ";\n}\n"] in
                    concat [head; body] in
                let projectors = List.map print_proj typs in
                concat2 new_line projectors
            | Some (MLTD_DType (l)) -> 
                let print_project (ctor_id, typs) =
                    let ctr = ref 0 in
                    let print_proj typ = 
                        ctr := !ctr + 1;
                        let head = concat [string_of_ml_type typ; " "; currentModule; "_"; ctor_id; "_get_field_"; string !ctr;
                                        "("; dtype_name; " x){\n"] in
                        let body = concat ["return x.content."; ctor_id.ToLower(); ".field_"; string !ctr; ";\n}\n"] in
                        concat [head; body] in
                    let projectors = List.map print_proj typs in
                    concat2 new_line projectors in
                let all_projectors = List.map print_project l in
                concat2 new_line all_projectors
            | _ -> "" in
            text s in

            
        let declarations = (List.map print_union_decl decls) @ (List.map (print_decl) decls) @ (List.map print_discriminators decls) @ (List.map print_projectors decls) in

        combine hardline declarations

        //doc_of_mltydecl currentModule decls

    | MLM_Let (rec_, lets) ->
        if (is_projector m || is_instance_of m || is_mk_record m) then text ""
        else text (string_of_lets currentModule (rec_, true, lets))

    | MLM_Top e ->
        reduce [text "int main(){\n"; text (string_of_expr currentModule (min_op_prec, NonAssoc) e); text "\n}"]
//        reduce1 [
//            text "let"; text "_"; text "=";
//            doc_of_expr currentModule  (min_op_prec, NonAssoc) e
//        ]

(* -------------------------------------------------------------------- *)
let doc_of_mod (currentModule : mlsymbol) (m : mlmodule) =
    // Add current module to state variables
    current_module := currentModule;

    let docs = List.map (doc_of_mod1 currentModule) m in
    let docs = List.map (fun x -> reduce [x; hardline; hardline]) docs in
    reduce docs

(* -------------------------------------------------------------------- *)
let rec doc_of_mllib_r (MLLib mllib) =
    let rec for1_sig (x, sigmod, MLLib sub) =
        let head = reduce1 [text "module"; text x; text ":"; text "sig"] in
        let tail = reduce1 [text "end"] in
        let doc  = Option.map (fun (s, _) -> doc_of_sig x s) sigmod in
        let sub  = List.map for1_sig sub in
        let sub  = List.map (fun x -> reduce [x; hardline; hardline]) sub in

        reduce [
            cat head hardline;
            (match doc with
             | None   -> empty
             | Some s -> cat s hardline);
            reduce sub;
            cat tail hardline;
        ]
    and for1_mod istop (x, sigmod, MLLib sub) =
        (*
        let head = reduce1 (if Util.codegen_fsharp()
                            then [text "module";  text x]
                            else if not istop
                            then [text "module";  text x; text "="; text "struct"]
                            else []) in
        let tail = if not istop
                   then reduce1 [text "end"]
                   else reduce1 [] in
                   *)
        let head = text "" in let tail = reduce1 [] in
        let doc  = Option.map (fun (_, m) -> doc_of_mod x m) sigmod in
        let sub  = List.map (for1_mod false)  sub in
        let sub  = List.map (fun x -> reduce [x; hardline; hardline]) sub in
        let prefix = if Util.codegen_fsharp () then [cat (text "#light \"off\"") hardline] else [] in

        reduce <| (prefix @ [
            head;
            hardline;
            text "#include <stdint.h>";
            hardline;
            text "#include <string.h>";
            hardline;
            text "#include <stdio.h>";
            hardline;
            text "#include \"fstarlib.h\"";
            (match doc with
             | None   -> empty
             | Some s -> cat s hardline);
            reduce sub;
            cat tail hardline;
        ])

    in

    let docs = List.map (fun (x,s,m) -> (x,for1_mod true (x,s,m))) mllib in
    docs

(* -------------------------------------------------------------------- *)
let doc_of_mllib mllib =
    doc_of_mllib_r mllib

open FStar.Extraction.ML.Env
let string_of_mlexpr (env:env) (e:mlexpr) =
    current_module := Util.flatten_mlpath env.currentModule;
    let doc = text (string_of_expr (Util.flatten_mlpath env.currentModule) (min_op_prec, NonAssoc) e) in
    pretty 0 doc

let string_of_mlty (env:env) (e:mlty) =
    current_module := Util.flatten_mlpath env.currentModule;
    let doc = doc_of_mltype (Util.flatten_mlpath env.currentModule) (min_op_prec, NonAssoc) e in
    pretty 0 doc
