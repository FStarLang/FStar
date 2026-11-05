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

let tag (b:BB.writer) (t:FStar.UInt8.t) : ML unit = BB.write_byte b t
let untag (b:BB.reader) : ML FStar.UInt8.t = BB.read_byte b

let rec enc_sort (b:BB.writer) (s:sort) : ML unit =
  match s with
  | Bool_sort -> tag b 0uy
  | Int_sort -> tag b 1uy
  | String_sort -> tag b 2uy
  | Term_sort -> tag b 3uy
  | Fuel_sort -> tag b 4uy
  | BitVec_sort n -> tag b 5uy; BB.write_int b n
  | Array (s1, s2) -> tag b 6uy; enc_sort b s1; enc_sort b s2
  | Arrow (s1, s2) -> tag b 7uy; enc_sort b s1; enc_sort b s2
  | Sort n -> tag b 8uy; BB.write_string b n

let rec dec_sort (b:BB.reader) : ML sort =
  match untag b with
  | 0uy -> Bool_sort
  | 1uy -> Int_sort
  | 2uy -> String_sort
  | 3uy -> Term_sort
  | 4uy -> Fuel_sort
  | 5uy -> BitVec_sort (BB.read_int b)
  | 6uy ->
    let s1 = dec_sort b in
    let s2 = dec_sort b in
    Array (s1, s2)
  | 7uy ->
    let s1 = dec_sort b in
    let s2 = dec_sort b in
    Arrow (s1, s2)
  | 8uy -> Sort (BB.read_string b)
  | t -> bad_tag "sort" t

let rec enc_sorts (b:BB.writer) (l:list sort) : ML unit =
  match l with
  | [] -> tag b 0uy
  | s :: l -> tag b 1uy; enc_sort b s; enc_sorts b l

let rec dec_sorts (b:BB.reader) : ML (list sort) =
  match untag b with
  | 0uy -> []
  | 1uy ->
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
  | TrueOp -> tag b 0uy
  | FalseOp -> tag b 1uy
  | Not -> tag b 2uy
  | And -> tag b 3uy
  | Or -> tag b 4uy
  | Imp -> tag b 5uy
  | Iff -> tag b 6uy
  | Eq -> tag b 7uy
  | LT -> tag b 8uy
  | LTE -> tag b 9uy
  | GT -> tag b 10uy
  | GTE -> tag b 11uy
  | Add -> tag b 12uy
  | Sub -> tag b 13uy
  | Div -> tag b 14uy
  | RealDiv -> tag b 15uy
  | Mul -> tag b 16uy
  | Minus -> tag b 17uy
  | Mod -> tag b 18uy
  | BvAnd -> tag b 19uy
  | BvXor -> tag b 20uy
  | BvOr -> tag b 21uy
  | BvAdd -> tag b 22uy
  | BvSub -> tag b 23uy
  | BvShl -> tag b 24uy
  | BvShr -> tag b 25uy
  | BvUdiv -> tag b 26uy
  | BvMod -> tag b 27uy
  | BvMul -> tag b 28uy
  | BvUlt -> tag b 29uy
  | BvConcat -> tag b 30uy
  | BvRepeat x -> tag b 31uy; BB.write_int b x
  | BvExtRol -> tag b 32uy
  | BvExtRor -> tag b 33uy
  | BvRol x -> tag b 34uy; BB.write_int b x
  | BvRor x -> tag b 35uy; BB.write_int b x
  | BvUext x -> tag b 36uy; BB.write_int b x
  | BvSext x -> tag b 37uy; BB.write_int b x
  | BvExtract (x, y) -> tag b 38uy; BB.write_int b x; BB.write_int b y
  | BvNot -> tag b 39uy
  | BvNeg -> tag b 40uy
  | BvNand -> tag b 41uy
  | BvNor -> tag b 42uy
  | BvXnor -> tag b 43uy
  | BvComp -> tag b 44uy
  | BvUle -> tag b 45uy
  | BvUgt -> tag b 46uy
  | BvUge -> tag b 47uy
  | BvSlt -> tag b 48uy
  | BvSle -> tag b 49uy
  | BvSgt -> tag b 50uy
  | BvSge -> tag b 51uy
  | BvSdiv -> tag b 52uy
  | BvSrem -> tag b 53uy
  | BvSmod -> tag b 54uy
  | BvAshr -> tag b 55uy
  | BvNego -> tag b 56uy
  | BvUaddo -> tag b 57uy
  | BvSaddo -> tag b 58uy
  | BvUmulo -> tag b 59uy
  | BvSmulo -> tag b 60uy
  | BvUsubo -> tag b 61uy
  | BvSsubo -> tag b 62uy
  | BvSdivo -> tag b 63uy
  | NatToBv x -> tag b 64uy; BB.write_int b x
  | BvToNat -> tag b 65uy
  | SBvToInt -> tag b 66uy
  | ITE -> tag b 67uy
  | Var x -> tag b 68uy; BB.write_string b x

let dec_op (b:BB.reader) : ML op =
  match untag b with
  | 0uy -> TrueOp
  | 1uy -> FalseOp
  | 2uy -> Not
  | 3uy -> And
  | 4uy -> Or
  | 5uy -> Imp
  | 6uy -> Iff
  | 7uy -> Eq
  | 8uy -> LT
  | 9uy -> LTE
  | 10uy -> GT
  | 11uy -> GTE
  | 12uy -> Add
  | 13uy -> Sub
  | 14uy -> Div
  | 15uy -> RealDiv
  | 16uy -> Mul
  | 17uy -> Minus
  | 18uy -> Mod
  | 19uy -> BvAnd
  | 20uy -> BvXor
  | 21uy -> BvOr
  | 22uy -> BvAdd
  | 23uy -> BvSub
  | 24uy -> BvShl
  | 25uy -> BvShr
  | 26uy -> BvUdiv
  | 27uy -> BvMod
  | 28uy -> BvMul
  | 29uy -> BvUlt
  | 30uy -> BvConcat
  | 31uy -> BvRepeat (BB.read_int b)
  | 32uy -> BvExtRol
  | 33uy -> BvExtRor
  | 34uy -> BvRol (BB.read_int b)
  | 35uy -> BvRor (BB.read_int b)
  | 36uy -> BvUext (BB.read_int b)
  | 37uy -> BvSext (BB.read_int b)
  | 38uy ->
    let x = BB.read_int b in
    let y = BB.read_int b in
    BvExtract (x, y)
  | 39uy -> BvNot
  | 40uy -> BvNeg
  | 41uy -> BvNand
  | 42uy -> BvNor
  | 43uy -> BvXnor
  | 44uy -> BvComp
  | 45uy -> BvUle
  | 46uy -> BvUgt
  | 47uy -> BvUge
  | 48uy -> BvSlt
  | 49uy -> BvSle
  | 50uy -> BvSgt
  | 51uy -> BvSge
  | 52uy -> BvSdiv
  | 53uy -> BvSrem
  | 54uy -> BvSmod
  | 55uy -> BvAshr
  | 56uy -> BvNego
  | 57uy -> BvUaddo
  | 58uy -> BvSaddo
  | 59uy -> BvUmulo
  | 60uy -> BvSmulo
  | 61uy -> BvUsubo
  | 62uy -> BvSsubo
  | 63uy -> BvSdivo
  | 64uy -> NatToBv (BB.read_int b)
  | 65uy -> BvToNat
  | 66uy -> SBvToInt
  | 67uy -> ITE
  | 68uy -> Var (BB.read_string b)
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
  | Integer s -> node w (fun b str _ -> tag b 0uy; str s)
  | String s -> node w (fun b str _ -> tag b 1uy; str s)
  | Real x ->
    node w (fun b _ _ ->
      tag b 2uy;
      BB.write_int b (FStarC.Real.mantissa x);
      BB.write_int b (FStarC.Real.exponent x))
  | BoundV n -> node w (fun b _ _ -> tag b 3uy; BB.write_int b n)
  | FreeV (FV n s f) ->
    node w (fun b str _ -> tag b 4uy; str n; enc_sort b s; tag b (if f then 1uy else 0uy))
  | App o args r ->
    let ids = intern_list w args in
    node w (fun b _ rng -> tag b 5uy; enc_op b o; enc_ids b ids; rng r)
  | Quant q pats wopt sorts body r ->
    let pids = List.map (intern_list w) pats in
    let bid = intern w body in
    node w (fun b _ rng ->
      tag b 6uy;
      tag b (match q with | Forall -> 0uy | Exists -> 1uy);
      BB.write_uvarint b (I.of_int (List.length pids));
      List.iter (enc_ids b) pids;
      (match wopt with
       | None -> tag b 0uy
       | Some n -> tag b 1uy; BB.write_int b n);
      enc_sorts b sorts;
      BB.write_uvarint b bid;
      rng r)
  | Let es body ->
    let ids = intern_list w es in
    let bid = intern w body in
    node w (fun b _ _ -> tag b 7uy; enc_ids b ids; BB.write_uvarint b bid)
  | Labeled t msg r ->
    let id = intern w t in
    let msg = List.map Errors.Msg.renderdoc msg in
    node w (fun b str rng ->
      tag b 8uy;
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
  | 0uy -> Integer (deser r)
  | 1uy -> String (deser r)
  | 2uy ->
    let m = BB.read_int b in
    let e = BB.read_int b in
    Real (FStarC.Real.mk m e)
  | 3uy -> BoundV (BB.read_int b)
  | 4uy ->
    let n : string = deser r in
    let s = dec_sort b in
    let f = untag b in
    FreeV (FV n s (f <> 0uy))
  | 5uy ->
    let o = dec_op b in
    let args = read_ids r in
    let rng : range = deser r in
    App o args rng
  | 6uy ->
    let q = (match untag b with | 0uy -> Forall | 1uy -> Exists | t -> bad_tag "qop" t) in
    let np = BB.read_uvarint b in
    let pats = read_n read_ids r np [] in
    let wopt =
      match untag b with
      | 0uy -> None
      | 1uy -> Some (BB.read_int b)
      | t -> bad_tag "option int" t
    in
    let sorts = dec_sorts b in
    let body : term = dag_read_child term_slot r in
    let rng : range = deser r in
    Quant q pats wopt sorts body rng
  | 7uy ->
    let es = read_ids r in
    let body : term = dag_read_child term_slot r in
    Let es body
  | 8uy ->
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
  | Name l -> write_tag w 0uy; ser w l
  | Namespace l -> write_tag w 1uy; ser w l
  | Tag s -> write_tag w 2uy; ser w s

let deser_fact_db_id (r:reader) : ML fact_db_id =
  match read_tag r with
  | 0uy -> Name (deser r)
  | 1uy -> Namespace (deser r)
  | 2uy -> Tag (deser r)
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
  | DefPrelude -> write_tag w 0uy
  | DeclFun n args s c -> write_tag w 1uy; ser w n; ser w args; ser w s; ser w c
  | DefineFun n args s t c ->
    write_tag w 2uy; ser w n; ser w args; ser w s; ser w t; ser w c
  | Assume a -> write_tag w 3uy; ser_assumption w a
  | Caption s -> write_tag w 4uy; ser w s
  | Module n ds -> write_tag w 5uy; ser w n; ser_list ser_decl w ds
  | Eval t -> write_tag w 6uy; ser w t
  | Echo s -> write_tag w 7uy; ser w s
  | RetainAssumptions l -> write_tag w 8uy; ser w l
  | Push n -> write_tag w 9uy; ser w n
  | Pop n -> write_tag w 10uy; ser w n
  | CheckSat -> write_tag w 11uy
  | SetOption k v -> write_tag w 12uy; ser w k; ser w v
  | GetStatistics -> write_tag w 13uy
  | GetReasonUnknown -> write_tag w 14uy
  | EmptyLine -> write_tag w 15uy

let rec deser_decl (r:reader) : ML decl =
  match read_tag r with
  | 0uy -> DefPrelude
  | 1uy ->
    let n : string = deser r in
    let args : list sort = deser r in
    let s : sort = deser r in
    let c : caption = deser r in
    DeclFun n args s c
  | 2uy ->
    let n : string = deser r in
    let args : list sort = deser r in
    let s : sort = deser r in
    let t : term = deser r in
    let c : caption = deser r in
    DefineFun n args s t c
  | 3uy -> Assume (deser_assumption r)
  | 4uy -> Caption (deser r)
  | 5uy ->
    let n : string = deser r in
    let ds = deser_list deser_decl r in
    Module n ds
  | 6uy -> Eval (deser r)
  | 7uy -> Echo (deser r)
  | 8uy -> RetainAssumptions (deser r)
  | 9uy -> Push (deser r)
  | 10uy -> Pop (deser r)
  | 11uy -> CheckSat
  | 12uy ->
    let k : string = deser r in
    let v : string = deser r in
    SetOption k v
  | 13uy -> GetStatistics
  | 14uy -> GetReasonUnknown
  | 15uy -> EmptyLine
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
  | Sum_triggers t -> write_tag w 0uy; ser w t
  | Sum_ambient b -> write_tag w 1uy; ser w b
  | Sum_drop -> write_tag w 2uy

let deser_asum_kind (r:reader) : ML asum_kind =
  match read_tag r with
  | 0uy -> Sum_triggers (deser r)
  | 1uy -> Sum_ambient (deser r)
  | 2uy -> Sum_drop
  | t -> bad_tag "asum_kind" t

let ser_decl_summary (w:writer) (s:decl_summary) : ML unit =
  match s with
  | Sum_assume a ->
    write_tag w 0uy;
    ser w a.asum_name;
    ser w a.asum_free_names;
    ser w a.asum_pretyping;
    ser_asum_kind w a.asum_kind
  | Sum_declfun n -> write_tag w 1uy; ser w n
  | Sum_definefun (n, l) -> write_tag w 2uy; ser w n; ser w l
  | Sum_retain l -> write_tag w 3uy; ser w l
  | Sum_ignored -> write_tag w 4uy
  | Sum_other d -> write_tag w 5uy; ser w d

let deser_decl_summary (r:reader) : ML decl_summary =
  match read_tag r with
  | 0uy ->
    let asum_name : string = deser r in
    let asum_free_names : list string = deser r in
    let asum_pretyping : bool = deser r in
    let asum_kind = deser_asum_kind r in
    Sum_assume { asum_name; asum_free_names; asum_pretyping; asum_kind }
  | 1uy -> Sum_declfun (deser r)
  | 2uy ->
    let n : string = deser r in
    let l : list string = deser r in
    Sum_definefun (n, l)
  | 3uy -> Sum_retain (deser r)
  | 4uy -> Sum_ignored
  | 5uy -> Sum_other (deser r)
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
