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
module FStarC.SMTEncoding.Serialize

open FStarC
open FStarC.Effect
open FStarC.Serialize
open FStarC.Syntax.Serialize
open FStarC.SMTEncoding.Term
open FStarC.SMTEncoding.Pruning
open FStarC.SMTEncoding.Env
open FStarC.Range.Type
module BB = FStarC.ByteBuffer
module I = FStarC.SmallInt

(* Sorts and operators are written directly to the byte buffer, without
   sharing, since they are also part of the keys of hash-consed terms. *)

let tag (b:BB.writer) (t:int) : ML unit = BB.write_byte b (I.of_int t)
let untag (b:BB.reader) : ML int = I.to_int (BB.read_byte b)

let rec enc_sort (b:BB.writer) (s:sort) : ML unit =
  match s with
  | Bool_sort -> tag b 0
  | Int_sort -> tag b 1
  | String_sort -> tag b 2
  | Term_sort -> tag b 3
  | Fuel_sort -> tag b 4
  | BitVec_sort n -> tag b 5; BB.write_int b n
  | Array (s1, s2) -> tag b 6; enc_sort b s1; enc_sort b s2
  | Arrow (s1, s2) -> tag b 7; enc_sort b s1; enc_sort b s2
  | Sort n -> tag b 8; BB.write_string b n

let rec dec_sort (b:BB.reader) : ML sort =
  match untag b with
  | 0 -> Bool_sort
  | 1 -> Int_sort
  | 2 -> String_sort
  | 3 -> Term_sort
  | 4 -> Fuel_sort
  | 5 -> BitVec_sort (BB.read_int b)
  | 6 ->
    let s1 = dec_sort b in
    let s2 = dec_sort b in
    Array (s1, s2)
  | 7 ->
    let s1 = dec_sort b in
    let s2 = dec_sort b in
    Arrow (s1, s2)
  | 8 -> Sort (BB.read_string b)
  | t -> bad_tag "sort" t

let rec enc_sorts (b:BB.writer) (l:list sort) : ML unit =
  match l with
  | [] -> tag b 0
  | s :: l -> tag b 1; enc_sort b s; enc_sorts b l

let rec dec_sorts (b:BB.reader) : ML (list sort) =
  match untag b with
  | 0 -> []
  | 1 ->
    let s = dec_sort b in
    let l = dec_sorts b in
    s :: l
  | t -> bad_tag "sorts" t

instance serializable_sort : serializable sort = {
  ser = (fun w s -> enc_sort (raw_writer w) s);
  deser = (fun r -> dec_sort (raw_reader r));
}

let enc_op (b:BB.writer) (o:op) : ML unit =
  match o with
  | TrueOp -> tag b 0
  | FalseOp -> tag b 1
  | Not -> tag b 2
  | And -> tag b 3
  | Or -> tag b 4
  | Imp -> tag b 5
  | Iff -> tag b 6
  | Eq -> tag b 7
  | LT -> tag b 8
  | LTE -> tag b 9
  | GT -> tag b 10
  | GTE -> tag b 11
  | Add -> tag b 12
  | Sub -> tag b 13
  | Div -> tag b 14
  | RealDiv -> tag b 15
  | Mul -> tag b 16
  | Minus -> tag b 17
  | Mod -> tag b 18
  | BvAnd -> tag b 19
  | BvXor -> tag b 20
  | BvOr -> tag b 21
  | BvAdd -> tag b 22
  | BvSub -> tag b 23
  | BvShl -> tag b 24
  | BvShr -> tag b 25
  | BvUdiv -> tag b 26
  | BvMod -> tag b 27
  | BvMul -> tag b 28
  | BvUlt -> tag b 29
  | BvConcat -> tag b 30
  | BvRepeat x -> tag b 31; BB.write_int b x
  | BvExtRol -> tag b 32
  | BvExtRor -> tag b 33
  | BvRol x -> tag b 34; BB.write_int b x
  | BvRor x -> tag b 35; BB.write_int b x
  | BvUext x -> tag b 36; BB.write_int b x
  | BvSext x -> tag b 37; BB.write_int b x
  | BvExtract (x, y) -> tag b 38; BB.write_int b x; BB.write_int b y
  | BvNot -> tag b 39
  | BvNeg -> tag b 40
  | BvNand -> tag b 41
  | BvNor -> tag b 42
  | BvXnor -> tag b 43
  | BvComp -> tag b 44
  | BvUle -> tag b 45
  | BvUgt -> tag b 46
  | BvUge -> tag b 47
  | BvSlt -> tag b 48
  | BvSle -> tag b 49
  | BvSgt -> tag b 50
  | BvSge -> tag b 51
  | BvSdiv -> tag b 52
  | BvSrem -> tag b 53
  | BvSmod -> tag b 54
  | BvAshr -> tag b 55
  | BvNego -> tag b 56
  | BvUaddo -> tag b 57
  | BvSaddo -> tag b 58
  | BvUmulo -> tag b 59
  | BvSmulo -> tag b 60
  | BvUsubo -> tag b 61
  | BvSsubo -> tag b 62
  | BvSdivo -> tag b 63
  | NatToBv x -> tag b 64; BB.write_int b x
  | BvToNat -> tag b 65
  | SBvToInt -> tag b 66
  | ITE -> tag b 67
  | Var x -> tag b 68; BB.write_string b x

let dec_op (b:BB.reader) : ML op =
  match untag b with
  | 0 -> TrueOp
  | 1 -> FalseOp
  | 2 -> Not
  | 3 -> And
  | 4 -> Or
  | 5 -> Imp
  | 6 -> Iff
  | 7 -> Eq
  | 8 -> LT
  | 9 -> LTE
  | 10 -> GT
  | 11 -> GTE
  | 12 -> Add
  | 13 -> Sub
  | 14 -> Div
  | 15 -> RealDiv
  | 16 -> Mul
  | 17 -> Minus
  | 18 -> Mod
  | 19 -> BvAnd
  | 20 -> BvXor
  | 21 -> BvOr
  | 22 -> BvAdd
  | 23 -> BvSub
  | 24 -> BvShl
  | 25 -> BvShr
  | 26 -> BvUdiv
  | 27 -> BvMod
  | 28 -> BvMul
  | 29 -> BvUlt
  | 30 -> BvConcat
  | 31 -> BvRepeat (BB.read_int b)
  | 32 -> BvExtRol
  | 33 -> BvExtRor
  | 34 -> BvRol (BB.read_int b)
  | 35 -> BvRor (BB.read_int b)
  | 36 -> BvUext (BB.read_int b)
  | 37 -> BvSext (BB.read_int b)
  | 38 ->
    let x = BB.read_int b in
    let y = BB.read_int b in
    BvExtract (x, y)
  | 39 -> BvNot
  | 40 -> BvNeg
  | 41 -> BvNand
  | 42 -> BvNor
  | 43 -> BvXnor
  | 44 -> BvComp
  | 45 -> BvUle
  | 46 -> BvUgt
  | 47 -> BvUge
  | 48 -> BvSlt
  | 49 -> BvSle
  | 50 -> BvSgt
  | 51 -> BvSge
  | 52 -> BvSdiv
  | 53 -> BvSrem
  | 54 -> BvSmod
  | 55 -> BvAshr
  | 56 -> BvNego
  | 57 -> BvUaddo
  | 58 -> BvSaddo
  | 59 -> BvUmulo
  | 60 -> BvSmulo
  | 61 -> BvUsubo
  | 62 -> BvSsubo
  | 63 -> BvSdivo
  | 64 -> NatToBv (BB.read_int b)
  | 65 -> BvToNat
  | 66 -> SBvToInt
  | 67 -> ITE
  | 68 -> Var (BB.read_string b)
  | t -> bad_tag "op" t

(* Terms *)

let term_slot = new_slot "smt_term"

let enc_rng (b:BB.writer) (r:rng) : ML unit =
  BB.write_string b (file_of_rng r);
  BB.write_int b (int_of_pos (start_of_rng r));
  BB.write_int b (int_of_pos (end_of_rng r))

let enc_range (b:BB.writer) (r:range) : ML unit =
  enc_rng b (def_range r);
  enc_rng b (use_range r)

let enc_ids (b:BB.writer) (ids:list I.t) : ML unit =
  BB.write_uvarint b (I.of_int (List.length ids));
  List.iter (BB.write_uvarint b) ids

(* A node is written by [f b str rng], where [str] and [rng] write a string
   and a range.  Its key is what [f] writes with [str] and [rng] writing
   to the byte buffer, without sharing. *)
let node (w:writer)
  (f:BB.writer -> (string -> ML unit) -> (range -> ML unit) -> ML unit)
  : ML I.t =
  let kb = BB.writer_create () in
  f kb (BB.write_string kb) (enc_range kb);
  let key = BB.writer_contents kb in
  dag_node term_slot w key (fun w -> f (raw_writer w) (fun s -> ser w s) (fun r -> ser w r))

let rec intern (w:writer) (t:term) : ML I.t =
  match t with
  | Integer s -> node w (fun b str _ -> tag b 0; str s)
  | String s -> node w (fun b str _ -> tag b 1; str s)
  | Real x ->
    node w (fun b _ _ ->
      tag b 2;
      BB.write_int b (FStarC.Real.mantissa x);
      BB.write_int b (FStarC.Real.exponent x))
  | BoundV n -> node w (fun b _ _ -> tag b 3; BB.write_int b n)
  | FreeV (FV n s f) ->
    node w (fun b str _ -> tag b 4; str n; enc_sort b s; tag b (if f then 1 else 0))
  | App o args r ->
    let ids = intern_list w args in
    node w (fun b _ rng -> tag b 5; enc_op b o; enc_ids b ids; rng r)
  | Quant q pats wopt sorts body r ->
    let pids = List.map (intern_list w) pats in
    let bid = intern w body in
    node w (fun b _ rng ->
      tag b 6;
      tag b (match q with | Forall -> 0 | Exists -> 1);
      BB.write_uvarint b (I.of_int (List.length pids));
      List.iter (enc_ids b) pids;
      (match wopt with
       | None -> tag b 0
       | Some n -> tag b 1; BB.write_int b n);
      enc_sorts b sorts;
      BB.write_uvarint b bid;
      rng r)
  | Let es body ->
    let ids = intern_list w es in
    let bid = intern w body in
    node w (fun b _ _ -> tag b 7; enc_ids b ids; BB.write_uvarint b bid)
  | Labeled t msg r ->
    let id = intern w t in
    let msg = List.map Errors.Msg.renderdoc msg in
    node w (fun b str rng ->
      tag b 8;
      BB.write_uvarint b id;
      BB.write_uvarint b (I.of_int (List.length msg));
      List.iter str msg;
      rng r)

and intern_list (w:writer) (ts:list term) : ML (list I.t) =
  List.map (intern w) ts

let rec read_n (#a:Type) ([@@@FStar.Attributes.monomorphize] f:reader -> ML a)
  (r:reader) (n:I.t) (acc:list a) : ML (list a) =
  if n = I.zero then List.rev acc
  else
    let x = f r in
    read_n f r I.(n - one) (x :: acc)

let read_ids (r:reader) : ML (list term) =
  let n = BB.read_uvarint (raw_reader r) in
  read_n (dag_read_child term_slot) r n []

let read_node (r:reader) : ML term =
  let b = raw_reader r in
  match untag b with
  | 0 -> Integer (deser r)
  | 1 -> String (deser r)
  | 2 ->
    let m = BB.read_int b in
    let e = BB.read_int b in
    Real (FStarC.Real.mk m e)
  | 3 -> BoundV (BB.read_int b)
  | 4 ->
    let n : string = deser r in
    let s = dec_sort b in
    let f = untag b in
    FreeV (FV n s (f <> 0))
  | 5 ->
    let o = dec_op b in
    let args = read_ids r in
    let rng : range = deser r in
    App o args rng
  | 6 ->
    let q = (match untag b with | 0 -> Forall | 1 -> Exists | t -> bad_tag "qop" t) in
    let np = BB.read_uvarint b in
    let pats = read_n read_ids r np [] in
    let wopt =
      match untag b with
      | 0 -> None
      | 1 -> Some (BB.read_int b)
      | t -> bad_tag "option int" t
    in
    let sorts = dec_sorts b in
    let body : term = dag_read_child term_slot r in
    let rng : range = deser r in
    Quant q pats wopt sorts body rng
  | 7 ->
    let es = read_ids r in
    let body : term = dag_read_child term_slot r in
    Let es body
  | 8 ->
    let t : term = dag_read_child term_slot r in
    let n = BB.read_uvarint b in
    let msg : list string = read_n (fun r -> deser r) r n [] in
    let rng : range = deser r in
    Labeled t (List.map Pprint.arbitrary_string msg) rng
  | t -> bad_tag "smt term" t

instance serializable_smt_term : serializable term = {
  ser = (fun w t -> dag_end w (intern w t));
  deser = (fun r -> dag_read term_slot r read_node);
}

(* Declarations *)

let ser_fact_db_id (w:writer) (f:fact_db_id) : ML unit =
  match f with
  | Name l -> write_tag w 0; ser w l
  | Namespace l -> write_tag w 1; ser w l
  | Tag s -> write_tag w 2; ser w s

let deser_fact_db_id (r:reader) : ML fact_db_id =
  match read_tag r with
  | 0 -> Name (deser r)
  | 1 -> Namespace (deser r)
  | 2 -> Tag (deser r)
  | t -> bad_tag "fact_db_id" t

let ser_assumption (w:writer) (a:assumption) : ML unit =
  ser w a.assumption_term;
  ser w a.assumption_caption;
  ser w a.assumption_name;
  ser_list ser_fact_db_id w a.assumption_fact_ids

let deser_assumption (r:reader) : ML assumption =
  let assumption_term : term = deser r in
  let assumption_caption : caption = deser r in
  let assumption_name : string = deser r in
  let assumption_fact_ids = deser_list deser_fact_db_id r in
  { assumption_term; assumption_caption; assumption_name; assumption_fact_ids }

let rec ser_decl (w:writer) (d:decl) : ML unit =
  match d with
  | DefPrelude -> write_tag w 0
  | DeclFun n args s c -> write_tag w 1; ser w n; ser w args; ser w s; ser w c
  | DefineFun n args s t c ->
    write_tag w 2; ser w n; ser w args; ser w s; ser w t; ser w c
  | Assume a -> write_tag w 3; ser_assumption w a
  | Caption s -> write_tag w 4; ser w s
  | Module n ds -> write_tag w 5; ser w n; ser_list ser_decl w ds
  | Eval t -> write_tag w 6; ser w t
  | Echo s -> write_tag w 7; ser w s
  | RetainAssumptions l -> write_tag w 8; ser w l
  | Push n -> write_tag w 9; ser w n
  | Pop n -> write_tag w 10; ser w n
  | CheckSat -> write_tag w 11
  | SetOption k v -> write_tag w 12; ser w k; ser w v
  | GetStatistics -> write_tag w 13
  | GetReasonUnknown -> write_tag w 14
  | EmptyLine -> write_tag w 15

let rec deser_decl (r:reader) : ML decl =
  match read_tag r with
  | 0 -> DefPrelude
  | 1 ->
    let n : string = deser r in
    let args : list sort = deser r in
    let s : sort = deser r in
    let c : caption = deser r in
    DeclFun n args s c
  | 2 ->
    let n : string = deser r in
    let args : list sort = deser r in
    let s : sort = deser r in
    let t : term = deser r in
    let c : caption = deser r in
    DefineFun n args s t c
  | 3 -> Assume (deser_assumption r)
  | 4 -> Caption (deser r)
  | 5 ->
    let n : string = deser r in
    let ds = deser_list deser_decl r in
    Module n ds
  | 6 -> Eval (deser r)
  | 7 -> Echo (deser r)
  | 8 -> RetainAssumptions (deser r)
  | 9 -> Push (deser r)
  | 10 -> Pop (deser r)
  | 11 -> CheckSat
  | 12 ->
    let k : string = deser r in
    let v : string = deser r in
    SetOption k v
  | 13 -> GetStatistics
  | 14 -> GetReasonUnknown
  | 15 -> EmptyLine
  | t -> bad_tag "decl" t

instance serializable_decl : serializable decl = {
  ser = ser_decl;
  deser = deser_decl;
}

instance serializable_decls_elt : serializable decls_elt = {
  ser = (fun w e ->
    ser w e.sym_name;
    ser w e.key;
    ser w e.decls;
    ser w e.a_names);
  deser = (fun r ->
    let sym_name : option string = deser r in
    let key : option string = deser r in
    let decls : list decl = deser r in
    let a_names : list string = deser r in
    { sym_name; key; decls; a_names });
}

(* Pruning summaries *)

let ser_asum_kind (w:writer) (k:asum_kind) : ML unit =
  match k with
  | Sum_triggers t -> write_tag w 0; ser w t
  | Sum_ambient b -> write_tag w 1; ser w b
  | Sum_drop -> write_tag w 2

let deser_asum_kind (r:reader) : ML asum_kind =
  match read_tag r with
  | 0 -> Sum_triggers (deser r)
  | 1 -> Sum_ambient (deser r)
  | 2 -> Sum_drop
  | t -> bad_tag "asum_kind" t

let ser_decl_summary (w:writer) (s:decl_summary) : ML unit =
  match s with
  | Sum_assume a ->
    write_tag w 0;
    ser w a.asum_name;
    ser w a.asum_free_names;
    ser w a.asum_pretyping;
    ser_asum_kind w a.asum_kind
  | Sum_declfun n -> write_tag w 1; ser w n
  | Sum_definefun (n, l) -> write_tag w 2; ser w n; ser w l
  | Sum_retain l -> write_tag w 3; ser w l
  | Sum_ignored -> write_tag w 4
  | Sum_other d -> write_tag w 5; ser w d

let deser_decl_summary (r:reader) : ML decl_summary =
  match read_tag r with
  | 0 ->
    let asum_name : string = deser r in
    let asum_free_names : list string = deser r in
    let asum_pretyping : bool = deser r in
    let asum_kind = deser_asum_kind r in
    Sum_assume { asum_name; asum_free_names; asum_pretyping; asum_kind }
  | 1 -> Sum_declfun (deser r)
  | 2 ->
    let n : string = deser r in
    let l : list string = deser r in
    Sum_definefun (n, l)
  | 3 -> Sum_retain (deser r)
  | 4 -> Sum_ignored
  | 5 -> Sum_other (deser r)
  | t -> bad_tag "decl_summary" t

instance serializable_elt_summary : serializable elt_summary = {
  ser = (fun w e ->
    ser w e.elts_key;
    ser w e.elts_a_names;
    ser_list ser_decl_summary w e.elts_sums);
  deser = (fun r ->
    let elts_key : option string = deser r in
    let elts_a_names : list string = deser r in
    let elts_sums = deser_list deser_decl_summary r in
    { elts_key; elts_a_names; elts_sums });
}

instance serializable_fvar_binding : serializable fvar_binding = {
  ser = (fun w b ->
    ser w b.fvar_lid;
    ser w b.univ_arity;
    ser w b.smt_arity;
    ser w b.smt_id;
    ser w b.smt_token;
    ser w b.smt_fuel_partial_app;
    ser w b.fvb_thunked;
    ser w b.needs_fuel_and_universe_instantiations);
  deser = (fun r ->
    let fvar_lid : Ident.lident = deser r in
    let univ_arity : int = deser r in
    let smt_arity : int = deser r in
    let smt_id : string = deser r in
    let smt_token : option term = deser r in
    let smt_fuel_partial_app : option (term & term) = deser r in
    let fvb_thunked : bool = deser r in
    let needs_fuel_and_universe_instantiations : option (list Ident.ident) = deser r in
    { fvar_lid; univ_arity; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
      fvb_thunked; needs_fuel_and_universe_instantiations });
}
