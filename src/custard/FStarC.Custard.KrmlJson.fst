(*
   Copyright 2008-2025 Microsoft Research

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
module FStarC.Custard.KrmlJson

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
open FStarC.Json
open FStarC.Custard.KrmlAst

module K  = FStarC.Custard.KrmlAst
module SB = FStarC.StringBuffer
module S  = FStarC.String
module SI = FStarC.SmallInt
module BU = FStarC.Util

(* ppx_deriving_yojson's encoding: a constant constructor [C] is [["C"]], a
   constructor [C of t] is [["C", t]], and every multi-argument constructor
   in karamel's [InputAst] is declared [C of (a * b)], a single tuple, so it
   is [["C", [a, b]]].  Tuples and lists are arrays, [None] is [null] and
   [Some x] is [x], records are objects. *)

(*** Writing *)

type w = SB.t

let raw (b:w) (s:string) : ML unit = let _ = SB.add s b in ()

let hex = "0123456789abcdef"

let escape_byte (c:SI.t) : ML string =
  if c = SI.of_int 34 then "\\\""
  else if c = SI.of_int 92 then "\\\\"
  else if c = SI.of_int 10 then "\\n"
  else if c = SI.of_int 9 then "\\t"
  else if c = SI.of_int 13 then "\\r"
  else
    let n = SI.to_int c in
    "\\u00" ^ S.substring hex (n / 16) 1 ^ S.substring hex (n % 16) 1

let needs_escape (c:SI.t) : bool =
  SI.(c < of_int 32) || c = SI.of_int 34 || c = SI.of_int 92

(* Copies the runs of bytes that need no escaping in one piece. *)
let str (b:w) (s:string) : ML unit =
  let n = S.byte_length s in
  let rec go (start i : SI.t) : ML unit =
    if SI.(i >= n) then raw b (S.byte_substring s start i)
    else
      let c = S.byte_at s i in
      if needs_escape c then begin
        raw b (S.byte_substring s start i);
        raw b (escape_byte c);
        go SI.(i + one) SI.(i + one)
      end else go start SI.(i + one)
  in
  raw b "\"";
  go SI.zero SI.zero;
  raw b "\""

let int_ (b:w) (i:int) : ML unit = raw b (show i)
let bool_ (b:w) (x:bool) : ML unit = raw b (if x then "true" else "false")
let comma (b:w) : ML unit = raw b ","

let list_ (#a:Type) (b:w) (f: a -> ML unit) (xs: list a) : ML unit =
  raw b "[";
  let rec go (first:bool) (xs:list a) : ML unit =
    match xs with
    | [] -> ()
    | x :: xs -> (if not first then comma b); f x; go false xs
  in
  go true xs;
  raw b "]"

let c0 (b:w) (n:string) : ML unit = raw b "[\""; raw b n; raw b "\"]"
(* Opens [["C", ] and [["C", [], for one argument and for a tuple. *)
let c1 (b:w) (n:string) : ML unit = raw b "[\""; raw b n; raw b "\","
let cn (b:w) (n:string) : ML unit = raw b "[\""; raw b n; raw b "\",["
let e1 (b:w) : ML unit = raw b "]"
let en (b:w) : ML unit = raw b "]]"

let lident_ (b:w) (l:lident) : ML unit =
  let (ns, n) = l in
  raw b "["; list_ b (str b) ns; comma b; str b n; raw b "]"

let width_ (b:w) (x:width) : ML unit =
  c0 b (match x with
    | UInt8 -> "UInt8" | UInt16 -> "UInt16" | UInt32 -> "UInt32" | UInt64 -> "UInt64"
    | Int8 -> "Int8" | Int16 -> "Int16" | Int32 -> "Int32" | Int64 -> "Int64"
    | Bool -> "Bool" | CInt -> "CInt" | SizeT -> "SizeT" | PtrdiffT -> "PtrdiffT"
    | Float32 -> "Float32" | Float64 -> "Float64")

let constant_ (b:w) (c:constant) : ML unit =
  let (wd, s) = c in
  raw b "["; width_ b wd; comma b; str b s; raw b "]"

let oper_ (b:w) (x:op) : ML unit =
  c0 b (match x with
    | Add -> "Add" | AddW -> "AddW" | Sub -> "Sub" | SubW -> "SubW"
    | Div -> "Div" | DivW -> "DivW" | Mult -> "Mult" | MultW -> "MultW" | Mod -> "Mod"
    | BOr -> "BOr" | BAnd -> "BAnd" | BXor -> "BXor"
    | BShiftL -> "BShiftL" | BShiftR -> "BShiftR" | BNot -> "BNot"
    | Eq -> "Eq" | Neq -> "Neq" | Lt -> "Lt" | Lte -> "Lte" | Gt -> "Gt" | Gte -> "Gte"
    | And -> "And" | Or -> "Or" | Xor -> "Xor" | Not -> "Not")

let flag_ (b:w) (f:flag) : ML unit =
  let s1 (n s:string) : ML unit = (c1 b n; str b s; e1 b) in
  match f with
  | Private -> c0 b "Private"
  | WipeBody -> c0 b "WipeBody"
  | CInline -> c0 b "Inline"
  | Substitute -> c0 b "Substitute"
  | GCType -> c0 b "GcType"
  | Comment s -> s1 "Comment" s
  | MustDisappear -> c0 b "MustDisappear"
  | Const s -> s1 "Const" s
  | Prologue s -> s1 "Prologue" s
  | Epilogue s -> s1 "Epilogue" s
  | Abstract -> c0 b "AbstractStruct"
  | IfDef -> c0 b "IfDef"
  | Macro -> c0 b "Macro"
  | Deprecated s -> s1 "Deprecated" s
  | CNoInline -> c0 b "NoInline"

let flags_ (b:w) (fs:list flag) : ML unit = list_ b (flag_ b) fs

let lifetime_ (b:w) (l:lifetime) : ML unit =
  c0 b (match l with Eternal -> "Eternal" | Stack -> "Stack" | ManuallyManaged -> "Heap")

let cc_ (b:w) (c:option cc) : ML unit =
  match c with
  | None -> raw b "null"
  | Some StdCall -> c0 b "StdCall"
  | Some CDecl -> c0 b "CDecl"
  | Some FastCall -> c0 b "FastCall"

let rec typ_ (b:w) (t:typ) : ML unit =
  match t with
  | TInt wd -> c1 b "TInt"; width_ b wd; e1 b
  | TBuf t -> c1 b "TBuf"; typ_ b t; e1 b
  | TUnit -> c0 b "TUnit"
  | TQualified l -> c1 b "TQualified"; lident_ b l; e1 b
  | TBool -> c0 b "TBool"
  | TAny -> c0 b "TAny"
  | TArrow (t1, t2) -> cn b "TArrow"; typ_ b t1; comma b; typ_ b t2; en b
  | TBound i -> c1 b "TBound"; int_ b i; e1 b
  | TApp (l, ts) -> cn b "TApp"; lident_ b l; comma b; list_ b (typ_ b) ts; en b
  | TTuple ts -> c1 b "TTuple"; list_ b (typ_ b) ts; e1 b
  | TConstBuf t -> c1 b "TConstBuf"; typ_ b t; e1 b
  | TArray (t, c) -> cn b "TArray"; typ_ b t; comma b; constant_ b c; en b

let binder_ (b:w) (x:binder) : ML unit =
  raw b "{\"name\":"; str b x.name;
  raw b ",\"typ\":"; typ_ b x.typ;
  raw b ",\"mut\":"; bool_ b x.mut;
  raw b ",\"meta\":"; flags_ b x.meta;
  raw b "}"

let rec pattern_ (b:w) (p:pattern) : ML unit =
  match p with
  | PUnit -> c0 b "PUnit"
  | PBool x -> c1 b "PBool"; bool_ b x; e1 b
  | PVar x -> c1 b "PVar"; binder_ b x; e1 b
  | PCons (n, ps) -> cn b "PCons"; str b n; comma b; list_ b (pattern_ b) ps; en b
  | PTuple ps -> c1 b "PTuple"; list_ b (pattern_ b) ps; e1 b
  | PRecord fs ->
    c1 b "PRecord";
    list_ b (fun (n, p) -> raw b "["; str b n; comma b; pattern_ b p; raw b "]") fs;
    e1 b
  | PConstant c -> c1 b "PConstant"; constant_ b c; e1 b

let rec expr_ (b:w) (e:expr) : ML unit =
  let ex = expr_ b in
  let exs = list_ b (expr_ b) in
  match e with
  | EBound i -> c1 b "EBound"; int_ b i; e1 b
  | EQualified l -> c1 b "EQualified"; lident_ b l; e1 b
  | EConstant c -> c1 b "EConstant"; constant_ b c; e1 b
  | EUnit -> c0 b "EUnit"
  | EApp (f, es) -> cn b "EApp"; ex f; comma b; exs es; en b
  | ETypApp (f, ts) -> cn b "ETApp"; ex f; comma b; list_ b (typ_ b) ts; en b
  | ELet (x, e1', e2) -> cn b "ELet"; binder_ b x; comma b; ex e1'; comma b; ex e2; en b
  | EIfThenElse (c, t, f) -> cn b "EIfThenElse"; ex c; comma b; ex t; comma b; ex f; en b
  | ESequence es -> c1 b "ESequence"; exs es; e1 b
  | EAssign (x, y) -> cn b "EAssign"; ex x; comma b; ex y; en b
  | EBufCreate (l, x, y) -> cn b "EBufCreate"; lifetime_ b l; comma b; ex x; comma b; ex y; en b
  | EBufRead (x, y) -> cn b "EBufRead"; ex x; comma b; ex y; en b
  | EBufWrite (x, y, z) -> cn b "EBufWrite"; ex x; comma b; ex y; comma b; ex z; en b
  | EBufSub (x, y) -> cn b "EBufSub"; ex x; comma b; ex y; en b
  | EBufBlit (x1, x2, x3, x4, x5) ->
    cn b "EBufBlit"; ex x1; comma b; ex x2; comma b; ex x3; comma b; ex x4; comma b; ex x5; en b
  | EMatch (x, brs) ->
    cn b "EMatch"; ex x; comma b;
    list_ b (fun (p, e) -> raw b "["; pattern_ b p; comma b; ex e; raw b "]") brs;
    en b
  | EOp (o, wd) -> cn b "EOp"; oper_ b o; comma b; width_ b wd; en b
  | ECast (x, t) -> cn b "ECast"; ex x; comma b; typ_ b t; en b
  | EPushFrame -> c0 b "EPushFrame"
  | EPopFrame -> c0 b "EPopFrame"
  | EBool x -> c1 b "EBool"; bool_ b x; e1 b
  | EAny -> c0 b "EAny"
  | EAbort -> c0 b "EAbort"
  | EReturn x -> c1 b "EReturn"; ex x; e1 b
  | EFlat (t, fs) ->
    cn b "EFlat"; typ_ b t; comma b;
    list_ b (fun (n, e) -> raw b "["; str b n; comma b; ex e; raw b "]") fs;
    en b
  | EField (t, x, n) -> cn b "EField"; typ_ b t; comma b; ex x; comma b; str b n; en b
  | EWhile (x, y) -> cn b "EWhile"; ex x; comma b; ex y; en b
  | EBufCreateL (l, es) -> cn b "EBufCreateL"; lifetime_ b l; comma b; exs es; en b
  | ETuple es -> c1 b "ETuple"; exs es; e1 b
  | ECons (t, n, es) -> cn b "ECons"; typ_ b t; comma b; str b n; comma b; exs es; en b
  | EBufFill (x, y, z) -> cn b "EBufFill"; ex x; comma b; ex y; comma b; ex z; en b
  | EString s -> c1 b "EString"; str b s; e1 b
  | EFun (xs, x, t) ->
    cn b "EFun"; list_ b (binder_ b) xs; comma b; ex x; comma b; typ_ b t; en b
  | EAbortS s -> c1 b "EAbortS"; str b s; e1 b
  | EBufFree x -> c1 b "EBufFree"; ex x; e1 b
  | EBufCreateNoInit (l, x) -> cn b "EBufCreateNoInit"; lifetime_ b l; comma b; ex x; en b
  | EAbortT (s, t) -> cn b "EAbortT"; str b s; comma b; typ_ b t; en b
  | EComment (s1, x, s2) -> cn b "EComment"; str b s1; comma b; ex x; comma b; str b s2; en b
  | EStandaloneComment s -> c1 b "EStandaloneComment"; str b s; e1 b
  | EAddrOf x -> c1 b "EAddrOf"; ex x; e1 b
  | EBufNull t -> c1 b "EBufNull"; typ_ b t; e1 b
  | EBufDiff (x, y) -> cn b "EBufDiff"; ex x; comma b; ex y; en b
  | ESizeof t -> c1 b "ESizeof"; typ_ b t; e1 b
  | EZeroForDeref wd -> c1 b "EZeroForDeref"; width_ b wd; e1 b

let fields_ (b:w) (fs:fields_t) : ML unit =
  list_ b (fun (n, (t, m)) ->
    raw b "["; str b n; raw b ",["; typ_ b t; comma b; bool_ b m; raw b "]]") fs

let decl_ (b:w) (d:decl) : ML unit =
  match d with
  | DGlobal (fl, l, i, t, e) ->
    cn b "DGlobal"; flags_ b fl; comma b; lident_ b l; comma b; int_ b i; comma b;
    typ_ b t; comma b; expr_ b e; en b
  | DFunction (c, fl, i, t, l, xs, e) ->
    cn b "DFunction"; cc_ b c; comma b; flags_ b fl; comma b; int_ b i; comma b;
    typ_ b t; comma b; lident_ b l; comma b; list_ b (binder_ b) xs; comma b;
    expr_ b e; en b
  | DTypeAlias (l, fl, i, t) ->
    cn b "DTypeAlias"; lident_ b l; comma b; flags_ b fl; comma b; int_ b i; comma b;
    typ_ b t; en b
  | DTypeFlat (l, fl, i, fs) ->
    cn b "DTypeFlat"; lident_ b l; comma b; flags_ b fl; comma b; int_ b i; comma b;
    fields_ b fs; en b
  | DUnusedRetainedForBackwardsCompat (c, fl, l, t) ->
    cn b "DExternal"; cc_ b c; comma b; flags_ b fl; comma b; lident_ b l; comma b;
    typ_ b t; en b
  | DTypeVariant (l, fl, i, brs) ->
    cn b "DTypeVariant"; lident_ b l; comma b; flags_ b fl; comma b; int_ b i; comma b;
    list_ b (fun (n, fs) -> raw b "["; str b n; comma b; fields_ b fs; raw b "]") brs;
    en b
  | DTypeAbstractStruct l -> c1 b "DTypeAbstractStruct"; lident_ b l; e1 b
  | DExternal (c, fl, l, t, ns) ->
    cn b "DExternal2"; cc_ b c; comma b; flags_ b fl; comma b; lident_ b l; comma b;
    typ_ b t; comma b; list_ b (str b) ns; en b
  | DUntaggedUnion (l, fl, i, fs) ->
    cn b "DUntaggedUnion"; lident_ b l; comma b; flags_ b fl; comma b; int_ b i; comma b;
    list_ b (fun (n, t) -> raw b "["; str b n; comma b; typ_ b t; raw b "]") fs;
    en b

let file_ (b:w) (f:K.file) : ML unit =
  let (n, p) = f in
  raw b "["; str b n; raw b ",";
  (* One declaration per line keeps the file diffable. *)
  raw b "[";
  let rec go (first:bool) (ds:list decl) : ML unit =
    match ds with
    | [] -> ()
    | d :: ds -> raw b (if first then "\n" else ",\n"); decl_ b d; go false ds
  in
  go true p;
  raw b "]]"

let write_file (fn:string) (bf:K.binary_format) : ML unit =
  let (v, fs) = bf in
  let b = SB.create 65536 in
  raw b "["; int_ b v; raw b ",[";
  let rec go (first:bool) (fs:list K.file) : ML unit =
    match fs with
    | [] -> ()
    | f :: fs -> raw b (if first then "\n" else ",\n"); file_ b f; go false fs
  in
  go true fs;
  raw b "]]\n";
  BU.maybe_create_parent fn;
  let ch = BU.open_file_for_writing fn in
  SB.output_channel ch b;
  BU.close_out_channel ch

(*** Reading *)

exception Malformed of string

let bad (#a:Type) (what:string) : ML a = raise (Malformed what)

let as_list (j:json) : ML (list json) =
  match j with JsonList l -> l | _ -> bad "expected an array"

let as_str (j:json) : ML string =
  match j with JsonStr s -> s | _ -> bad "expected a string"

let as_int (j:json) : ML int =
  match j with JsonInt i -> i | _ -> bad "expected an integer"

let as_bool (j:json) : ML bool =
  match j with JsonBool x -> x | _ -> bad "expected a boolean"

(* A constructor and its arguments: [[]] for a constant constructor, [[x]]
   for a single one, and the elements of the tuple for the [C of (a * b)]
   ones, which callers match with [targs]. *)
let as_ctor (j:json) : ML (string & list json) =
  match j with
  | JsonList (JsonStr n :: args) -> (n, args)
  | _ -> bad "expected a constructor"

let targs (args:list json) : ML (list json) =
  match args with [JsonList xs] -> xs | _ -> bad "expected a tuple argument"

let as_pair (j:json) : ML (json & json) =
  match as_list j with [x; y] -> (x, y) | _ -> bad "expected a pair"

let lident_of (j:json) : ML lident =
  let (ns, n) = as_pair j in (List.map as_str (as_list ns), as_str n)

let ctor_name (j:json) : ML string =
  match as_ctor j with (n, []) -> n | _ -> bad "expected a constant constructor"

let width_of (j:json) : ML width =
  match ctor_name j with
  | "UInt8" -> UInt8 | "UInt16" -> UInt16 | "UInt32" -> UInt32 | "UInt64" -> UInt64
  | "Int8" -> Int8 | "Int16" -> Int16 | "Int32" -> Int32 | "Int64" -> Int64
  | "Bool" -> Bool | "CInt" -> CInt | "SizeT" -> SizeT | "PtrdiffT" -> PtrdiffT
  | "Float32" -> Float32 | "Float64" -> Float64
  | n -> bad ("unknown width " ^ n)

let constant_of (j:json) : ML constant =
  let (wd, s) = as_pair j in (width_of wd, as_str s)

let op_of (j:json) : ML op =
  match ctor_name j with
  | "Add" -> Add | "AddW" -> AddW | "Sub" -> Sub | "SubW" -> SubW
  | "Div" -> Div | "DivW" -> DivW | "Mult" -> Mult | "MultW" -> MultW | "Mod" -> Mod
  | "BOr" -> BOr | "BAnd" -> BAnd | "BXor" -> BXor
  | "BShiftL" -> BShiftL | "BShiftR" -> BShiftR | "BNot" -> BNot
  | "Eq" -> Eq | "Neq" -> Neq | "Lt" -> Lt | "Lte" -> Lte | "Gt" -> Gt | "Gte" -> Gte
  | "And" -> And | "Or" -> Or | "Xor" -> Xor | "Not" -> Not
  | n -> bad ("unknown operator " ^ n)

let flag_of (j:json) : ML flag =
  match as_ctor j with
  | "Private", [] -> Private
  | "WipeBody", [] -> WipeBody
  | "Inline", [] -> CInline
  | "Substitute", [] -> Substitute
  | "GcType", [] -> GCType
  | "Comment", [s] -> Comment (as_str s)
  | "MustDisappear", [] -> MustDisappear
  | "Const", [s] -> Const (as_str s)
  | "Prologue", [s] -> Prologue (as_str s)
  | "Epilogue", [s] -> Epilogue (as_str s)
  | "AbstractStruct", [] -> Abstract
  | "IfDef", [] -> IfDef
  | "Macro", [] -> Macro
  | "Deprecated", [s] -> Deprecated (as_str s)
  | "NoInline", [] -> CNoInline
  | n, _ -> bad ("unknown flag " ^ n)

let flags_of (j:json) : ML (list flag) = List.map flag_of (as_list j)

let lifetime_of (j:json) : ML lifetime =
  match ctor_name j with
  | "Eternal" -> Eternal | "Stack" -> Stack | "Heap" -> ManuallyManaged
  | n -> bad ("unknown lifetime " ^ n)

let cc_of (j:json) : ML (option cc) =
  match j with
  | JsonNull -> None
  | _ ->
    match ctor_name j with
    | "StdCall" -> Some StdCall | "CDecl" -> Some CDecl | "FastCall" -> Some FastCall
    | n -> bad ("unknown calling convention " ^ n)

let rec typ_of (j:json) : ML typ =
  match as_ctor j with
  | "TInt", [x] -> TInt (width_of x)
  | "TBuf", [x] -> TBuf (typ_of x)
  | "TUnit", [] -> TUnit
  | "TQualified", [x] -> TQualified (lident_of x)
  | "TBool", [] -> TBool
  | "TAny", [] -> TAny
  | "TArrow", a -> (match targs a with [x; y] -> TArrow (typ_of x, typ_of y) | _ -> bad "TArrow")
  | "TBound", [x] -> TBound (as_int x)
  | "TApp", a -> (match targs a with [l; ts] -> TApp (lident_of l, List.map typ_of (as_list ts)) | _ -> bad "TApp")
  | "TTuple", [x] -> TTuple (List.map typ_of (as_list x))
  | "TConstBuf", [x] -> TConstBuf (typ_of x)
  | "TArray", a -> (match targs a with [t; c] -> TArray (typ_of t, constant_of c) | _ -> bad "TArray")
  | n, _ -> bad ("unknown type " ^ n)

let binder_of (j:json) : ML binder =
  match j with
  | JsonAssoc fs ->
    let get (k:string) : ML json =
      match List.tryFind (fun (k', _) -> k = k') fs with
      | Some (_, v) -> v
      | None -> bad ("binder without " ^ k)
    in
    { name = as_str (get "name"); typ = typ_of (get "typ");
      mut = as_bool (get "mut"); meta = flags_of (get "meta") }
  | _ -> bad "expected a binder"

let rec pattern_of (j:json) : ML pattern =
  match as_ctor j with
  | "PUnit", [] -> PUnit
  | "PBool", [x] -> PBool (as_bool x)
  | "PVar", [x] -> PVar (binder_of x)
  | "PCons", a -> (match targs a with [n; ps] -> PCons (as_str n, List.map pattern_of (as_list ps)) | _ -> bad "PCons")
  | "PTuple", [x] -> PTuple (List.map pattern_of (as_list x))
  | "PRecord", [x] ->
    PRecord (as_list x |> List.map (fun f -> let (n, p) = as_pair f in (as_str n, pattern_of p)))
  | "PConstant", [x] -> PConstant (constant_of x)
  | n, _ -> bad ("unknown pattern " ^ n)

let rec expr_of (j:json) : ML expr =
  let exs (j:json) : ML (list expr) = List.map expr_of (as_list j) in
  match as_ctor j with
  | "EBound", [x] -> EBound (as_int x)
  | "EQualified", [x] -> EQualified (lident_of x)
  | "EConstant", [x] -> EConstant (constant_of x)
  | "EUnit", [] -> EUnit
  | "ESequence", [x] -> ESequence (exs x)
  | "EPushFrame", [] -> EPushFrame
  | "EPopFrame", [] -> EPopFrame
  | "EBool", [x] -> EBool (as_bool x)
  | "EAny", [] -> EAny
  | "EAbort", [] -> EAbort
  | "EReturn", [x] -> EReturn (expr_of x)
  | "ETuple", [x] -> ETuple (exs x)
  | "EString", [x] -> EString (as_str x)
  | "EAbortS", [x] -> EAbortS (as_str x)
  | "EBufFree", [x] -> EBufFree (expr_of x)
  | "EStandaloneComment", [x] -> EStandaloneComment (as_str x)
  | "EAddrOf", [x] -> EAddrOf (expr_of x)
  | "EBufNull", [x] -> EBufNull (typ_of x)
  | "ESizeof", [x] -> ESizeof (typ_of x)
  | "EZeroForDeref", [x] -> EZeroForDeref (width_of x)
  | n, a ->
    match n, targs a with
    | "EApp", [f; es] -> EApp (expr_of f, exs es)
    | "ETApp", [f; ts] -> ETypApp (expr_of f, List.map typ_of (as_list ts))
    | "ELet", [x; e1; e2] -> ELet (binder_of x, expr_of e1, expr_of e2)
    | "EIfThenElse", [c; t; f] -> EIfThenElse (expr_of c, expr_of t, expr_of f)
    | "EAssign", [x; y] -> EAssign (expr_of x, expr_of y)
    | "EBufCreate", [l; x; y] -> EBufCreate (lifetime_of l, expr_of x, expr_of y)
    | "EBufRead", [x; y] -> EBufRead (expr_of x, expr_of y)
    | "EBufWrite", [x; y; z] -> EBufWrite (expr_of x, expr_of y, expr_of z)
    | "EBufSub", [x; y] -> EBufSub (expr_of x, expr_of y)
    | "EBufBlit", [x1; x2; x3; x4; x5] ->
      EBufBlit (expr_of x1, expr_of x2, expr_of x3, expr_of x4, expr_of x5)
    | "EMatch", [x; brs] ->
      EMatch (expr_of x, as_list brs |> List.map (fun br ->
        let (p, e) = as_pair br in (pattern_of p, expr_of e)))
    | "EOp", [o; wd] -> EOp (op_of o, width_of wd)
    | "ECast", [x; t] -> ECast (expr_of x, typ_of t)
    | "EFlat", [t; fs] ->
      EFlat (typ_of t, as_list fs |> List.map (fun f ->
        let (n, e) = as_pair f in (as_str n, expr_of e)))
    | "EField", [t; x; n] -> EField (typ_of t, expr_of x, as_str n)
    | "EWhile", [x; y] -> EWhile (expr_of x, expr_of y)
    | "EBufCreateL", [l; es] -> EBufCreateL (lifetime_of l, exs es)
    | "ECons", [t; n; es] -> ECons (typ_of t, as_str n, exs es)
    | "EBufFill", [x; y; z] -> EBufFill (expr_of x, expr_of y, expr_of z)
    | "EFun", [xs; x; t] -> EFun (List.map binder_of (as_list xs), expr_of x, typ_of t)
    | "EBufCreateNoInit", [l; x] -> EBufCreateNoInit (lifetime_of l, expr_of x)
    | "EAbortT", [s; t] -> EAbortT (as_str s, typ_of t)
    | "EComment", [s1; x; s2] -> EComment (as_str s1, expr_of x, as_str s2)
    | "EBufDiff", [x; y] -> EBufDiff (expr_of x, expr_of y)
    | _ -> bad ("unknown expression " ^ n)

let fields_of (j:json) : ML fields_t =
  as_list j |> List.map (fun f ->
    let (n, tm) = as_pair f in
    let (t, m) = as_pair tm in
    (as_str n, (typ_of t, as_bool m)))

let decl_of (j:json) : ML decl =
  let (n, a) = as_ctor j in
  match n, a with
  | "DTypeAbstractStruct", [l] -> DTypeAbstractStruct (lident_of l)
  | _ ->
    match n, targs a with
    | "DGlobal", [fl; l; i; t; e] ->
      DGlobal (flags_of fl, lident_of l, as_int i, typ_of t, expr_of e)
    | "DFunction", [c; fl; i; t; l; xs; e] ->
      DFunction (cc_of c, flags_of fl, as_int i, typ_of t, lident_of l,
                 List.map binder_of (as_list xs), expr_of e)
    | "DTypeAlias", [l; fl; i; t] -> DTypeAlias (lident_of l, flags_of fl, as_int i, typ_of t)
    | "DTypeFlat", [l; fl; i; fs] -> DTypeFlat (lident_of l, flags_of fl, as_int i, fields_of fs)
    | "DExternal", [c; fl; l; t] ->
      DUnusedRetainedForBackwardsCompat (cc_of c, flags_of fl, lident_of l, typ_of t)
    | "DTypeVariant", [l; fl; i; brs] ->
      DTypeVariant (lident_of l, flags_of fl, as_int i, as_list brs |> List.map (fun br ->
        let (n, fs) = as_pair br in (as_str n, fields_of fs)))
    | "DExternal2", [c; fl; l; t; ns] ->
      DExternal (cc_of c, flags_of fl, lident_of l, typ_of t, List.map as_str (as_list ns))
    | "DUntaggedUnion", [l; fl; i; fs] ->
      DUntaggedUnion (lident_of l, flags_of fl, as_int i, as_list fs |> List.map (fun f ->
        let (n, t) = as_pair f in (as_str n, typ_of t)))
    | _ -> bad ("unknown declaration " ^ n)

let binary_format_of (j:json) : ML K.binary_format =
  let (v, fs) = as_pair j in
  (as_int v, as_list fs |> List.map (fun f ->
    let (n, p) = as_pair f in (as_str n, List.map decl_of (as_list p))))

let read_file (fn:string) : ML (option K.binary_format) =
  let s = BU.file_get_contents fn in
  if S.byte_at s SI.zero <> SI.of_int 91 (* '[' *) then None
  else
    match json_of_string s with
    | None -> None
    | Some j -> try Some (binary_format_of j) with | Malformed _ -> None
