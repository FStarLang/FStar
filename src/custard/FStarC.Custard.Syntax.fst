(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Custard.Syntax

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Ident
open FStarC.Const
open FStarC.BaseTypes

open FStarC.Class.Show
open FStarC.Class.PP
open FStarC.Pprint

module BU = FStarC.Util

(* -------------------------------------------------------------------- *)
(* Names                                                                *)
(* -------------------------------------------------------------------- *)

(* The mangled name is the only debugging aid Custard offers, so we keep it as
   readable as we can: use the specialization hint when there is one, and fall
   back to the numeric index otherwise. *)
let mangled_name (n:name) : ML string =
  let base = String.concat "_" (n.ns @ [n.id]) in
  match n.spec with
  | None -> base
  | Some s -> base ^ "__" ^ s

let string_of_name (n:name) : ML string =
  let base = String.concat "." (n.ns @ [n.id]) in
  match n.spec with
  | None -> base
  | Some s -> base ^ "@" ^ s

(* '#' is not legal in an F* identifier, so [base_name] is exact; the printers
   sanitize it away in the rare event that a name escapes the renaming pass. *)
let uniq (base:string) (i:int) : ML string = base ^ "#" ^ show i

let base_name (s:string) : ML string =
  match String.split ['#'] s with
  | b :: _ :: _ -> b
  | _ -> s

(* -------------------------------------------------------------------- *)
(* Effects                                                              *)
(* -------------------------------------------------------------------- *)

let eff_rank (e:eff) : int =
  match e with
  | E_Ghost -> 0
  | E_Pure -> 1
  | E_Impure -> 2

let join_eff (e1 e2 : eff) : eff =
  if eff_rank e1 >= eff_rank e2 then e1 else e2

let is_pure (e:eff) : bool =
  match e with
  | E_Ghost | E_Pure -> true
  | E_Impure -> false

(* -------------------------------------------------------------------- *)
(* Helpers                                                              *)
(* -------------------------------------------------------------------- *)

let rec subst_cty (s:list (string & cty)) (c:cty) : ML cty =
  match c with
  | TVar v -> (match s |> List.tryFind (fun (p, _) -> p = v) with
               | Some (_, c') -> c'
               | None -> c)
  | TArrow (a, e, b) -> TArrow (subst_cty s a, e, subst_cty s b)
  | TTuple cs -> TTuple (cs |> List.map (subst_cty s))
  | TBuf c -> TBuf (subst_cty s c)
  | TRef c -> TRef (subst_cty s c)
  | TApp (n, args) -> TApp (n, args |> List.map (subst_cty s))
  | c -> c

let mk (e:expr') (ty:cty) (eff:eff) : expr = { e; ty; eff }

let unit_expr : expr = mk (EConst CUnit) TUnit E_Pure

let name_of_decl (d:decl) : name =
  match d with
  | DType t -> t.dt_name
  | DLet l -> l.dl_name
  | DExternal e -> e.dx_name
  | DExn e -> e.de_name

let decl_flags (d:decl) : list flag =
  match d with
  | DType t -> t.dt_flags
  | DLet l -> l.dl_flags
  | DExternal e -> e.dx_flags
  | DExn _ -> []

let has_flag (fs : list flag) (f : flag) : ML bool =
  List.existsb (fun f' -> f' = f) fs

(* -------------------------------------------------------------------- *)
(* Printing                                                             *)
(*                                                                      *)
(* The IR dump is meant to be read by humans debugging the pipeline, so  *)
(* we print something that looks like source rather than a constructor   *)
(* dump.                                                                *)
(* -------------------------------------------------------------------- *)

let text (s:string) : document = doc_of_string s

let parens_if (b:bool) (d:document) : document =
  if b then parens d else d

let sep_by (s:document) (ds : list document) : document =
  separate s ds

let name_to_doc (n:name) : ML document = text (string_of_name n)

let eff_to_string (e:eff) : string =
  match e with
  | E_Ghost -> "Ghost"
  | E_Pure -> "Pure"
  | E_Impure -> "Impure"

let eff_to_doc (e:eff) : ML document = text (eff_to_string e)

let width_to_string (sw:signedness & width) : string =
  let s, w = sw in
  (match s with Unsigned -> "u" | Signed -> "i") ^
  (match w with
   | Int8 -> "8" | Int16 -> "16" | Int32 -> "32" | Int64 -> "64"
   | Sizet -> "size")

let op_to_string (o:prim_op) : string =
  (match o.po_op with
   | Add -> "+" | AddW -> "+." | Sub -> "-" | SubW -> "-."
   | Mult -> "*" | MultW -> "*." | Div -> "/" | DivW -> "/." | Mod -> "%"
   | BOr -> "|" | BAnd -> "&" | BXor -> "^" | BShiftL -> "<<"
   | BShiftR -> ">>" | BNot -> "~"
   | Eq -> "=" | Neq -> "<>" | Lt -> "<" | Lte -> "<=" | Gt -> ">" | Gte -> ">="
   | And -> "&&" | Or -> "||" | Not -> "not"
   | BufCreate LStack -> "alloca" | BufCreate LHeap -> "malloc"
   | BufRead -> "read" | BufWrite -> "write" | BufSub -> "sub"
   | BufFree -> "free" | BufNull -> "null" | BufIsNull -> "is_null"
   | BufBlit -> "blit") ^
  (match o.po_int with None -> "" | Some sw -> width_to_string sw)

(* [prec] is the precedence of the enclosing context: 0 at the top, 1 under an
   arrow's domain, 2 as the argument of a type application. *)
let rec cty_to_doc' (prec:int) (t:cty) : ML document =
  match t with
  | TVar x -> text ("'" ^ x)
  | TInt sw -> text (width_to_string sw)
  | TUnit -> text "unit"
  | TAny -> text "any"
  | TArrow (t1, e, t2) ->
    let arrow =
      match e with
      | E_Pure -> text "->"
      | E_Ghost -> text "-[G]->"
      | E_Impure -> text "-[I]->"
    in
    parens_if (prec >= 1) <|
      group (cty_to_doc' 1 t1 ^/^ arrow ^/^ cty_to_doc' 0 t2)
  | TApp (n, []) -> name_to_doc n
  | TApp (n, args) ->
    parens_if (prec >= 2) <|
      group (name_to_doc n ^^ langle ^^
             sep_by (comma ^^ space) (List.map (cty_to_doc' 0) args) ^^ rangle)
  | TBuf t ->
    parens_if (prec >= 2) <| group (text "buf" ^/^ cty_to_doc' 2 t)
  | TRef t ->
    parens_if (prec >= 2) <| group (text "ref" ^/^ cty_to_doc' 2 t)
  | TTuple ts ->
    parens (sep_by (space ^^ text "*" ^^ space) (List.map (cty_to_doc' 1) ts))

let cty_to_doc (t:cty) : ML document = cty_to_doc' 0 t
let cty_to_string (t:cty) : ML string = render (cty_to_doc t)

(* The dump is meant to be re-readable by eye, so escape rather than emit raw
   control characters. *)
let escape_char (c:char) : string =
  match c with
  | '\n' -> "\\n"
  | '\t' -> "\\t"
  | '\r' -> "\\r"
  | '"'  -> "\\\""
  | '\\' -> "\\\\"
  | c -> BU.string_of_char c

let escape_string (s:string) : ML string =
  String.concat "" (List.map escape_char (String.list_of_string s))

let constant_to_doc (c:constant) : ML document =
  match c with
  | CUnit -> text "()"
  | CBool b -> text (if b then "true" else "false")
  | CInt (s, None) -> text s
  | CInt (s, Some (sg, w)) ->
    text (s ^ "<" ^ (match sg with Unsigned -> "u" | Signed -> "i") ^
          (match w with
           | Int8 -> "8" | Int16 -> "16" | Int32 -> "32"
           | Int64 -> "64" | Sizet -> "size") ^ ">")
  | CChar c -> text ("'" ^ escape_char c ^ "'")
  | CString s -> dquotes (text (escape_string s))

let constant_to_string (c:constant) : ML string = render (constant_to_doc c)

let rec pat_to_doc (p:pat) : ML document =
  match p with
  | PWild -> underscore
  | PVar x -> text x
  | PConst c -> constant_to_doc c
  | PCtor (n, []) -> name_to_doc n
  | PCtor (n, ps) ->
    group (name_to_doc n ^^ parens (sep_by (comma ^^ space) (List.map pat_to_doc ps)))
  | PTuple ps -> parens (sep_by (comma ^^ space) (List.map pat_to_doc ps))
  | POr ps -> group (sep_by (space ^^ bar ^^ space) (List.map pat_to_doc ps))

let pat_to_string (p:pat) : ML string = render (pat_to_doc p)

let binder_to_doc (b:binder) : ML document =
  parens (group (text b.b_name ^^ colon ^/^ cty_to_doc b.b_ty))

(* [prec]: 0 = statement position, 1 = operand position (needs parens if
   compound). *)
let rec expr_to_doc' (prec:int) (e:expr) : ML document =
  match e.e with
  | EConst c -> constant_to_doc c
  | EVar x -> text x
  | EQual (n, []) -> name_to_doc n
  | EQual (n, tys) ->
    group (name_to_doc n ^^ langle ^^
           sep_by (comma ^^ space) (List.map cty_to_doc tys) ^^ rangle)

  | ELet (x, t, e1, e2) ->
    parens_if (prec >= 1) <|
      group (
        group (nest 2 (
          text "let" ^/^ text x ^^ colon ^/^ cty_to_doc t ^/^ equals ^/^
          expr_to_doc' 0 e1)) ^/^ text "in") ^^ hardline ^^
        expr_to_doc' 0 e2

  | EApp (h, args) ->
    parens_if (prec >= 1) <|
      group (nest 2 (expr_to_doc' 1 h ^/^
                     sep_by (break_ 1) (List.map (expr_to_doc' 1) args)))

  | EFun (bs, body) ->
    parens_if (prec >= 1) <|
      group (nest 2 (
        text "fun" ^/^ sep_by (break_ 1) (List.map binder_to_doc bs) ^/^
        text "->" ^/^ expr_to_doc' 0 body))

  | EMatch (scrut, brs) ->
    parens_if (prec >= 1) <|
      group (
        group (text "match" ^/^ expr_to_doc' 0 scrut ^/^ text "with") ^^
        concat (List.map branch_to_doc brs))

  | EIf (c, t, e2) ->
    parens_if (prec >= 1) <|
      group (
        group (nest 2 (text "if" ^/^ expr_to_doc' 0 c)) ^/^
        group (nest 2 (text "then" ^/^ expr_to_doc' 1 t)) ^/^
        group (nest 2 (text "else" ^/^ expr_to_doc' 1 e2)))

  | ESeq (e1, e2) ->
    parens_if (prec >= 1) <|
      (expr_to_doc' 1 e1 ^^ semi ^^ hardline ^^ expr_to_doc' 0 e2)

  | ECtor (n, []) -> name_to_doc n
  | ECtor (n, args) ->
    group (name_to_doc n ^^ parens (sep_by (comma ^^ space)
                                      (List.map (expr_to_doc' 0) args)))

  | ETuple es -> parens (sep_by (comma ^^ space) (List.map (expr_to_doc' 0) es))

  | ERecord (n, fs) ->
    group (name_to_doc n ^/^ braces (sep_by (semi ^^ space)
      (List.map (fun (f, e) -> group (text f ^/^ equals ^/^ expr_to_doc' 0 e)) fs)))

  | EProj (e1, n, f) ->
    expr_to_doc' 1 e1 ^^ dot ^^ name_to_doc n ^^ dot ^^ text f

  | EDiscrim (e1, n) ->
    name_to_doc n ^^ text "?" ^^ parens (expr_to_doc' 0 e1)

  | ECast (e1, t) ->
    group (parens (nest 2 (expr_to_doc' 0 e1 ^/^ text "<:" ^/^ cty_to_doc t)))

  | EOp (op, args) ->
    group (text ("`" ^ op_to_string op ^ "`") ^^
           parens (sep_by (comma ^^ space) (List.map (expr_to_doc' 0) args)))

  | EWhile (c, body) ->
    parens_if (prec >= 1) <|
      group (
        group (nest 2 (text "while" ^/^ expr_to_doc' 1 c)) ^/^
        group (nest 2 (text "{" ^^ hardline ^^ expr_to_doc' 0 body)) ^^
        hardline ^^ text "}")

  | EAny -> text "any"
  | EAbort s -> group (text "abort" ^/^ dquotes (text s))

  | ERaise (n, []) -> group (text "raise" ^/^ name_to_doc n)
  | ERaise (n, args) ->
    group (text "raise" ^/^ name_to_doc n ^^
           parens (sep_by (comma ^^ space) (List.map (expr_to_doc' 0) args)))

  | ETry (e1, brs) ->
    parens_if (prec >= 1) <|
      group (
        group (nest 2 (text "try" ^/^ expr_to_doc' 0 e1)) ^/^ text "with" ^^
        concat (List.map branch_to_doc brs))

and branch_to_doc (br : branch) : ML document =
  let p, guard, body = br in
  let g =
    match guard with
    | None -> empty
    | Some g -> space ^^ text "when" ^^ space ^^ expr_to_doc' 1 g
  in
  hardline ^^ group (nest 2 (
    bar ^^ space ^^ pat_to_doc p ^^ g ^/^ text "->" ^/^ expr_to_doc' 0 body))

let expr_to_doc (e:expr) : ML document = expr_to_doc' 0 e
let expr_to_string (e:expr) : ML string = render (expr_to_doc e)

let flag_to_doc (f:flag) : ML document =
  match f with
  | Rec ns -> text ("rec[" ^ String.concat "," (List.map string_of_name ns) ^ "]")
  | Private -> text "private"
  | Root -> text "root"
  | Entrypoint -> text "entrypoint"
  | NoNewtype -> text "no_newtype"
  | Inline -> text "inline"
  | Erased -> text "erased"
  | Comment s -> text ("(* " ^ s ^ " *)")

let flags_to_doc (fs : list flag) : ML document =
  match fs with
  | [] -> empty
  | _ -> text "[@@" ^^ sep_by (comma ^^ space) (List.map flag_to_doc fs)
         ^^ text "]" ^^ hardline

let params_to_doc (ps : list string) : ML document =
  match ps with
  | [] -> empty
  | _ -> space ^^ langle ^^
         separate (comma ^^ space) (List.map (fun p -> text ("'" ^ p)) ps) ^^ rangle

(* Starts with its own leading break, so the caller writes [... ^^ equals ^^
   tydef_to_doc], which keeps variants from getting a blank line. *)
let tydef_to_doc (d:tydef) : ML document =
  match d with
  | TAbstract -> space ^^ text "<abstract>"
  | TAbbrev t -> break_ 1 ^^ cty_to_doc t
  | TRecord fs -> break_ 1 ^^
    group (nest 2 (lbrace ^^ break_ 1 ^^
      sep_by (semi ^^ break_ 1)
        (List.map (fun (f, t) -> group (text f ^^ colon ^/^ cty_to_doc t)) fs))
      ^^ break_ 1 ^^ rbrace)
  | TVariant cs ->
    let ctor_to_doc (cf : name & list (string & cty)) : ML document =
      let c, fs = cf in
      match fs with
      | [] -> name_to_doc c
      | _ ->
        group (name_to_doc c ^/^ text "of" ^/^
          sep_by (space ^^ text "&" ^^ space)
            (List.map (fun (f, t) -> group (text f ^^ colon ^/^ cty_to_doc t)) fs))
    in
    concat (List.map (fun c -> hardline ^^ bar ^^ space ^^ ctor_to_doc c) cs)

let decl_to_doc (d:decl) : ML document =
  match d with
  | DType t ->
    flags_to_doc t.dt_flags ^^
    group (nest 2 (
      text "type" ^^ space ^^ name_to_doc t.dt_name ^^ params_to_doc t.dt_params ^^
      space ^^ equals ^^ tydef_to_doc t.dt_body))

  | DLet l ->
    flags_to_doc l.dl_flags ^^
    group (
      group (nest 2 (
        text "let" ^^ space ^^ name_to_doc l.dl_name ^^ params_to_doc l.dl_typars ^^
        (match l.dl_binders with
         | [] -> empty
         | bs -> break_ 1 ^^ sep_by (break_ 1) (List.map binder_to_doc bs)) ^/^
        colon ^/^ cty_to_doc l.dl_ret ^^ space ^^ brackets (eff_to_doc l.dl_eff) ^/^
        equals)) ^^ hardline ^^
      nest 2 (expr_to_doc l.dl_body))

  | DExternal e ->
    flags_to_doc e.dx_flags ^^
    group (nest 2 (
      text "external" ^^ space ^^ name_to_doc e.dx_name ^/^ colon ^/^ cty_to_doc e.dx_ty ^^
      (match e.dx_target with
       | None -> empty
       | Some t -> space ^^ equals ^/^ dquotes (text t))))

  | DExn e ->
    group (nest 2 (
      text "exception" ^^ space ^^ name_to_doc e.de_name ^^
      (match e.de_args with
       | [] -> empty
       | args -> space ^^ text "of" ^/^
                 sep_by (space ^^ text "&" ^^ space) (List.map cty_to_doc args))))

let decl_to_string (d:decl) : ML string = render (decl_to_doc d)

let program_to_doc (p:program) : ML document =
  separate_map (hardline ^^ hardline) decl_to_doc p

let program_to_string (p:program) : ML string = render (program_to_doc p)

(* -------------------------------------------------------------------- *)
(* Instances                                                            *)
(* -------------------------------------------------------------------- *)

instance showable_name     : showable name     = { show = string_of_name }
instance showable_eff      : showable eff      = { show = eff_to_string }
instance showable_cty      : showable cty      = { show = cty_to_string }
instance showable_constant : showable constant = { show = constant_to_string }
instance showable_pat      : showable pat      = { show = pat_to_string }
instance showable_expr     : showable expr     = { show = expr_to_string }
instance showable_decl     : showable decl     = { show = decl_to_string }

instance pp_cty  : pretty cty  = { pp = cty_to_doc }
instance pp_expr : pretty expr = { pp = expr_to_doc }
instance pp_decl : pretty decl = { pp = decl_to_doc }
