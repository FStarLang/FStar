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
module String = FStarC.String

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

(* Section 39.2.  [Real.to_string] writes a literal out in full, which is the
   right answer for "0.5" and 301 characters of it for 1e300: [Real.mk]
   normalizes a non-negative exponent away by multiplying it into the
   mantissa, so the zeros are all there.  Dividing them back out costs a loop
   and buys an exponent, and both spellings denote the same rational exactly.
   The threshold is a matter of taste and this one is nobody's literal. *)
let rec strip_zeros (m:int) (e:int) : int & int =
  if m <> 0 && m % 10 = 0 then strip_zeros (m / 10) (e + 1) else (m, e)

let iwidth_of_width (w:width) : iwidth =
  match w with
  | Int8 -> W8 | Int16 -> W16 | Int32 -> W32 | Int64 -> W64 | Sizet -> WSizet

(* Section 125.4.  Shared rather than copied: [PrintOCaml], [PrintFSharp] and
   [Builtins] all want it, and a fourth copy would have been the one that
   disagreed.  [WSizet] answers 64 because that is the default; a caller that
   cannot tolerate --custard_sizet_width 32 making it false has to say so. *)
let width_bits (w:iwidth) : int =
  match w with
  | W8 -> 8 | W16 -> 16 | W32 -> 32 | W64 -> 64 | W128 -> 128 | WSizet -> 64

(* Section 69.  Hand-rolled rather than a regexp: the grammar is three
   productions and the module has no regexp dependency. *)
let template_of_string (s:string) : ML (list tmpl_piece) =
  let cs = String.list_of_string s in
  let flush (acc : list char) (out : list tmpl_piece) : list tmpl_piece =
    match acc with
    | [] -> out
    | _ -> TP_lit (String.string_of_list (List.rev acc)) :: out in
  (* [acc] is the literal text seen since the last piece, reversed. *)
  let rec go (cs : list char) (acc : list char) (out : list tmpl_piece)
    : ML (list tmpl_piece) =
    match cs with
    | [] -> List.rev (flush acc out)
    | '{' :: '{' :: rest -> go rest ('{' :: acc) out
    | '{' :: rest ->
      (* [{] followed by digits followed by [}], or nothing special. *)
      let rec digits (cs : list char) (ds : list char)
        : ML (option (int & list char)) =
        match cs with
        | '}' :: rest ->
          (match ds with
           | [] -> None
           | _ ->
             let n = List.fold_left
                       (fun acc (d:char) -> acc * 10 + (BU.int_of_char d - 48))
                       0 (List.rev ds) in
             Some (n, rest))
        | c :: rest when BU.int_of_char c >= 48 && BU.int_of_char c <= 57 ->
          digits rest (c :: ds)
        | _ -> None in
      (match digits rest [] with
       | Some (n, rest') -> go rest' [] (TP_arg n :: flush acc out)
       | None -> go rest ('{' :: acc) out)
    | c :: rest -> go rest (c :: acc) out in
  go cs [] []

let is_template (ps : list tmpl_piece) : ML bool = List.existsb TP_arg? ps

let fwidth_to_string (fw:fwidth) : string =
  match fw with
  | Float32 -> "f32"
  | Float64 -> "f64"
  | Float16 -> "f16"
  | BFloat16 -> "bf16"

let float_lit_to_string (f:float_lit) : string =
  let sign = if f.fl_neg then "-" else "" in
  let m = Real.mantissa f.fl_mag in
  let e = Real.exponent f.fl_mag in
  let plain = Real.to_string f.fl_mag in
  if e = 0 && String.length plain > 24
  then
    let (m, e) = strip_zeros m e in
    sign ^ string_of_int m ^ (if e = 0 then ".0" else "e" ^ string_of_int e)
  else sign ^ plain

(* Section 39.2.  The grammar is FStarC.Extraction.Krml.valid_float_literal's,
   which is deliberately narrower than C's: no hex float, no infinity, no NaN,
   because those are what an [of_literal] argument that reached C by accident
   would look like. *)
let float_lit_of_string (s:string) : option float_lit =
  let cs = String.list_of_string s in
  let is_digit (c : FStar.Char.char) : bool =
    let n = BU.int_of_char c in n >= 48 && n <= 57 in
  let rec digits (cs : list FStar.Char.char)
    : Tot (list FStar.Char.char & list FStar.Char.char) (decreases cs) =
    match cs with
    | c :: cs' when is_digit c -> let (ds, rest) = digits cs' in (c :: ds, rest)
    | _ -> ([], cs) in
  let rec value (acc:int) (ds : list FStar.Char.char) : Tot int (decreases ds) =
    match ds with
    | [] -> acc
    | c :: ds -> value (acc * 10 + (BU.int_of_char c - 48)) ds in
  let value (ds : list FStar.Char.char) : int = value 0 ds in
  let (neg, cs) =
    match cs with
    | '-' :: cs -> (true, cs)
    | '+' :: cs -> (false, cs)
    | _ -> (false, cs) in
  let (ipart, cs) = digits cs in
  let (fpart, cs) =
    match cs with
    | '.' :: cs -> let (fs, cs) = digits cs in (fs, cs)
    | _ -> ([], cs) in
  (* At least one digit, on one side or the other: ".5" and "5." are both
     literals, "." and "e3" are not. *)
  if Nil? ipart && Nil? fpart then None else
  let (expo, cs) =
    match cs with
    | c :: cs when c = 'e' || c = 'E' ->
      let (eneg, cs) =
        match cs with
        | '-' :: cs -> (true, cs)
        | '+' :: cs -> (false, cs)
        | _ -> (false, cs) in
      let (ds, cs) = digits cs in
      if Nil? ds then (None, cs)
      else (Some (if eneg then - (value ds) else value ds), cs)
    | _ -> (Some 0, cs) in
  match expo, cs with
  | Some expo, [] ->
    let m = value (ipart @ fpart) in
    Some { fl_neg = neg; fl_mag = Real.mk m (expo - List.length fpart) }
  | _ -> None

(* Section 118.  The significand of [fw], in bits, counting the implicit
   leading one: a binary format holds an integer exactly when the integer's
   odd part fits in that many bits. *)
let significand_bits (fw:fwidth) : int =
  match fw with
  | Float32  -> 24
  | Float64  -> 53
  | Float16  -> 11
  | BFloat16 -> 8

let rec fits_in_bits (n:nat) (bits:nat) : Tot bool (decreases bits) =
  if n = 0 then true
  else if bits = 0 then false
  else fits_in_bits (n / 2) (bits - 1)

let rec odd_part (n:nat) : Tot nat (decreases n) =
  if n = 0 || n % 2 = 1 then n else odd_part (n / 2)

let float_lit_of_int (fw:fwidth) (n:int) : option float_lit =
  let a : nat = if n < 0 then -n else n in
  if fits_in_bits (odd_part a) (significand_bits fw)
  then Some { fl_neg = n < 0; fl_mag = Real.mk a 0 }
  else None

let int_lit_to_string (v:int) (b:int_base) : string = string_of_int_literal v b

let rec oct_digits (n:int) (acc:string) : Tot string (decreases n) =
  if n <= 0 then acc
  else oct_digits (n / 8) (Prims.string_of_int (n % 8) ^ acc)

let c_int_lit_to_string (v:int) (b:int_base) : string =
  match b with
  (* C writes octal with a leading zero, not with F*'s [0o]. *)
  | Oct ->
    if v = 0 then "0"
    else if v < 0 then "-0" ^ oct_digits (-v) ""
    else "0" ^ oct_digits v ""
  (* C has no binary literal before C23.  A base is a way of writing a number,
     so a base the target cannot write is dropped rather than approximated:
     the number is what may not change. *)
  | Bin -> string_of_int_literal v Dec
  | _ -> string_of_int_literal v b

let const_eq (c1 c2 : constant) : bool =
  match c1, c2 with
  | CInt (v1, _, sw1), CInt (v2, _, sw2) -> v1 = v2 && sw1 = sw2
  | _ -> c1 = c2

let at_int_width (o:prim_op) : bool =
  match o.po_ty with
  | Some (PInt _) -> true
  | _ -> false

let rec subst_cty (s:list (string & cty)) (c:cty) : ML cty =
  match c with
  | TVar v -> (match s |> List.tryFind (fun (p, _) -> p = v) with
               | Some (_, c') -> c'
               | None -> c)
  | TArrow (a, e, b) -> TArrow (subst_cty s a, e, subst_cty s b)
  | TTuple cs -> TTuple (cs |> List.map (subst_cty s))
  | TBuf c -> TBuf (subst_cty s c)
  | TRef c -> TRef (subst_cty s c)
  | TInline c -> TInline (subst_cty s c)
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

(* Section 69. *)
let extern_template_of_flags (fs : list flag) : ML (option (list tmpl_piece)) =
  match List.tryPick (fun f -> match f with
                               | Extern (t, _) -> t
                               | _ -> None) fs with
  | Some t -> let ps = template_of_string t in
              if is_template ps then Some ps else None
  | None -> None

let decl_flags (d:decl) : list flag =
  match d with
  | DType t -> t.dt_flags
  | DLet l -> l.dl_flags
  | DExternal e -> e.dx_flags
  | DExn e -> e.de_flags

let has_flag (fs : list flag) (f : flag) : ML bool =
  List.existsb (fun f' -> f' = f) fs

let rec type_names_of_cty (c : cty) : ML (list string) =
  match c with
  | TArrow (a, _, b) -> type_names_of_cty a @ type_names_of_cty b
  | TTuple cs -> cs |> List.collect type_names_of_cty
  | TBuf c | TRef c | TInline c -> type_names_of_cty c
  | TApp (n, args) -> string_of_name n :: (args |> List.collect type_names_of_cty)
  | _ -> []

let type_names_of_decl (d : decl) : ML (list string) =
  match d with
  | DType t ->
    (match t.dt_body with
     | TAbbrev c -> type_names_of_cty c
     | TRecord fs -> fs |> List.collect (fun (_, c) -> type_names_of_cty c)
     | TVariant cs -> cs |> List.collect (fun (_, fs) ->
                        fs |> List.collect (fun (_, c) -> type_names_of_cty c))
     | TAbstract -> [])
  | DLet l ->
    (l.dl_binders |> List.collect (fun b -> type_names_of_cty b.b_ty))
    @ type_names_of_cty l.dl_ret
  | DExternal x -> type_names_of_cty x.dx_ty
  | DExn e -> e.de_args |> List.collect type_names_of_cty

let imported_unit (d : decl) : ML (option string) =
  decl_flags d |> List.tryPick (function Imported (u, _) -> Some u | _ -> None)

let imported_home (d : decl) : ML (option string) =
  decl_flags d |> List.tryPick (function Imported (_, h) -> h | _ -> None)

(* Section 99.  See the comment on the declaration in the interface. *)
(* Section 121.  The two hand-written traversals that all the others are
   written against.  Everything else in this package that walks an expression
   -- and there were twenty-five such walks in [Simplify] alone -- now writes
   only the cases it has an opinion about and falls through to one of these.

   [children] and [map_children] must agree about what a child is and about
   the order they are in, so they are kept adjacent and are the only two
   places in the package that list every constructor for the sake of
   listing it. *)
let branch_children (br:branch) : ML (list expr) =
  let _, g, b = br in
  (match g with Some g -> [g] | None -> []) @ [b]

let children (x:expr) : ML (list expr) =
  match x.e with
  | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> []
  | ELet (_, _, e1, e2) -> [e1; e2]
  | EApp (h, es) -> h :: es
  | EFun (_, b) -> [b]
  | EMatch (s, brs) -> s :: List.collect branch_children brs
  | EIf (c, a, b) -> [c; a; b]
  | ESeq (a, b) -> [a; b]
  | ECtor (_, es) | ETuple es | EOp (_, es) -> es
  | ERecord (_, fs) -> List.map snd fs
  | EProj (e1, _, _) | EDiscrim (e1, _)
  | ECoerce (e1, _) | ECast (e1, _) | ERaise e1 -> [e1]
  | EWhile (a, b) -> [a; b]
  | ETry (a, brs) -> a :: List.collect branch_children brs

(* Written in the same applicative style the hand-written traversals used,
   rather than with explicit [let]s, so that a pass converted to it keeps the
   order in which its side effects -- a [GenSym.next_id], say -- used to
   happen.  A converted pass has to be a no-op on the output, and a gensym
   that renumbers is not one. *)
let map_branch (g : expr -> ML expr) (br:branch) : ML branch =
  let p, guard, b = br in
  (p, (match guard with None -> None | Some e -> Some (g e)), g b)

let map_children (g : expr -> ML expr) (x:expr) : ML expr =
  match x.e with
  | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> x
  | ELet (v, ty, e1, e2) -> { x with e = ELet (v, ty, g e1, g e2) }
  | EApp (h, es) -> { x with e = EApp (g h, es |> List.map g) }
  | EFun (bs, b) -> { x with e = EFun (bs, g b) }
  | EMatch (s, brs) -> { x with e = EMatch (g s, brs |> List.map (map_branch g)) }
  | EIf (c, a, b) -> { x with e = EIf (g c, g a, g b) }
  | ESeq (a, b) -> { x with e = ESeq (g a, g b) }
  | ECtor (n, es) -> { x with e = ECtor (n, es |> List.map g) }
  | ETuple es -> { x with e = ETuple (es |> List.map g) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map g) }
  | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, g e))) }
  | EProj (e1, n, f) -> { x with e = EProj (g e1, n, f) }
  | EDiscrim (e1, n) -> { x with e = EDiscrim (g e1, n) }
  | ECoerce (e1, c) -> { x with e = ECoerce (g e1, c) }
  | ECast (e1, c) -> { x with e = ECast (g e1, c) }
  | ERaise e1 -> { x with e = ERaise (g e1) }
  | EWhile (a, b) -> { x with e = EWhile (g a, g b) }
  | ETry (a, brs) -> { x with e = ETry (g a, brs |> List.map (map_branch g)) }

let iter_children (f : expr -> ML unit) (x:expr) : ML unit =
  List.iter f (children x)

let fold_children (#a:Type) (f : a -> expr -> ML a) (init:a) (x:expr) : ML a =
  List.fold_left f init (children x)

let exists_child (f : expr -> ML bool) (x:expr) : ML bool =
  List.existsb f (children x)

let for_all_children (f : expr -> ML bool) (x:expr) : ML bool =
  List.for_all f (children x)

let rec is_droppable (e:expr) : ML bool =
  let all (es:list expr) : ML bool = List.for_all is_droppable es in
  (* Section 120.  Ahead of both tests below, because it overrides both.  A
     comment is not a computation and its effect says so, but the text is the
     point of the node and deleting it loses what the author wrote. *)
  if (match e.e with EOp ({ po_op = Commented _ }, _) -> true | _ -> false)
  then false else
  (* The two predicates are not ordered, so this is genuinely a union.  An
     effect is a property of the *node*, and a pure call is deletable while
     the structural test below cannot see that -- [EApp] is opaque to it. *)
  is_pure e.eff ||
  (match e.e with
  | EConst _ | EVar _ | EQual _ | EAny -> true
  | EApp _ | EFun _ | EWhile _ | EAbort _ | ERaise _ | ETry _ -> false
  | EOp ({ po_op = BufRead }, es) -> all es
  | EOp ({ po_op = BufCreate _ }, _) | EOp ({ po_op = BufWrite }, _)
  | EOp ({ po_op = BufFree }, _) | EOp ({ po_op = BufBlit }, _) -> false
  | EOp (_, es) -> all es
  (* Everything else is deletable exactly when all of it is.  A branch's
     guard and body are children, and its pattern binds nothing that
     survives the deletion of the whole node. *)
  | ECtor _ | ETuple _ | ELet _ | ESeq _ | EIf _ | EMatch _
  | ERecord _ | EProj _ | EDiscrim _ | ECast _
  | ECoerce _ -> for_all_children is_droppable e)

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


let iwidth_to_string (w:iwidth) : string =
  match w with
  | W8 -> "8" | W16 -> "16" | W32 -> "32" | W64 -> "64" | W128 -> "128"
  | WSizet -> "size"

let width_to_string (sw:signedness & iwidth) : string =
  let s, w = sw in
  (match s with Unsigned -> "u" | Signed -> "i") ^ iwidth_to_string w

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
   | BufBlit -> "blit"
   | BufLit -> "lit" | BufUnconst -> "unconst"
   | Commented _ -> "comment") ^
  (match o.po_ty with
   | None -> ""
   | Some (PInt sw) -> width_to_string sw
   | Some (PFloat fw) -> fwidth_to_string fw)

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
  | CInt (v, b, None) -> text (int_lit_to_string v b)
  | CInt (v, b, Some (sg, w)) ->
    text (int_lit_to_string v b ^ "<" ^
          (match sg with Unsigned -> "u" | Signed -> "i") ^
          iwidth_to_string w ^ ">")
  | CFloat (v, fw) ->
    text (float_lit_to_string v ^ "<" ^ fwidth_to_string fw ^ ">")
  | CChar c -> text ("'" ^ escape_char c ^ "'")
  | CString s -> dquotes (text (escape_string s))

let constant_to_string (c:constant) : ML string = render (constant_to_doc c)

(* [prec] is the precedence of the enclosing context: 0 at the top, 1 under an
   arrow's domain, 2 as the argument of a type application. *)
let rec cty_to_doc' (prec:int) (t:cty) : ML document =
  match t with
  | TVar x -> text ("'" ^ x)
  | TInt sw -> text (width_to_string sw)
  | TFloat fw -> text (fwidth_to_string fw)
  | TUnit -> text "unit"
  | TExn -> text "exn"
  | TAny -> text "any"
  | TConst c -> constant_to_doc c
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
  | TInline t ->
    parens_if (prec >= 2) <| group (text "inline" ^/^ cty_to_doc' 2 t)
  | TTuple ts ->
    parens (sep_by (space ^^ text "*" ^^ space) (List.map (cty_to_doc' 1) ts))

let cty_to_doc (t:cty) : ML document = cty_to_doc' 0 t
let cty_to_string (t:cty) : ML string = render (cty_to_doc t)

(* The dump is meant to be re-readable by eye, so escape rather than emit raw
   control characters. *)
let rec pat_to_doc (p:pat) : ML document =
  match p with
  | PWild -> underscore
  | PVar x -> text x
  | PConst c -> constant_to_doc c
  | PCtor (n, []) -> name_to_doc n
  | PCtor (n, ps) ->
    group (name_to_doc n ^^ parens (sep_by (comma ^^ space) (List.map pat_to_doc ps)))
  | PRecord (_, fs) ->
    braces (sep_by (semi ^^ space) (fs |> List.map (fun (f, q) ->
      group (text f ^/^ equals ^/^ pat_to_doc q))))
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

  | ECoerce (e1, t) ->
    group (parens (nest 2 (expr_to_doc' 0 e1 ^/^ text "<:" ^/^ cty_to_doc t)))

  | ECast (e1, t) ->
    group (parens (nest 2 (expr_to_doc' 0 e1 ^/^ text ":>" ^/^ cty_to_doc t)))

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

  | ERaise e1 -> group (text "raise" ^/^ expr_to_doc' 1 e1)

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
  | Prologue s -> text ("prologue " ^ s)
  | Epilogue s -> text ("epilogue " ^ s)
  | ClosurePrologue (a, b) ->
    text ("closure_prologue " ^ a ^ " / " ^ b)
  | CMacro -> text "c_macro"
  | CReference -> text "c_reference"
  | CInline -> text "c_inline"
  | Realized -> text "realized"
  | Extern (n, h) ->
    text ("extern" ^ (match n with Some n -> " " ^ n | None -> "") ^
                     (match h with Some h -> " <" ^ h ^ ">" | None -> ""))
  | SourceRecord -> text "source-record"
  | Existential (c, f) -> text ("existential[" ^ c ^ "." ^ f ^ "]")
  | Modelled -> text "modelled"
  | Imported (u, h) ->
    text ("imported[" ^ u ^ (match h with Some m -> "@" ^ m | None -> "") ^ "]")

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
    flags_to_doc e.de_flags ^^
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
