(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStarC.SMTEncoding.Term

open FStarC
open FStarC.Effect
open FStarC.Pprint

module BU  = FStarC.Util

let escape (s:string) = BU.replace_char s '\'' '_'

let render = pretty_string (BU.float_of_string "1.0") 100

let form_core (children: list document) : document =
  parens (nest 1 (group (separate (break_ 1) children)))
let form (fn: string) (args: list document) : document =
  form_core (doc_of_string fn :: args)
let binder (fn: string) (b: document) (args: list document) : document =
  form_core (nest 1 (group (doc_of_string fn ^/^ b)) :: args)
let mk_qid (id: string) : document =
  nest 1 (group (doc_of_string ":qid" ^/^ doc_of_string id))
let mk_lblpos (id: string) : document =
  nest 1 (group (doc_of_string ":lblpos" ^/^ doc_of_string id))
let mk_named (id: string) : document =
  nest 1 (group (doc_of_string ":named" ^/^ doc_of_string id))
let mk_pattern (pat: document) : document =
  nest 1 (group (doc_of_string ":pattern" ^/^ pat))

let rec strSort x = match x with
  | Bool_sort  -> "Bool"
  | Int_sort  -> "Int"
  | Term_sort -> "Term"
  | String_sort -> "FString"
  | Fuel_sort -> "Fuel"
  | BitVec_sort n -> Format.fmt1 "(_ BitVec %s)" (show n)
  | Array(s1, s2) -> Format.fmt2 "(Array %s %s)" (strSort s1) (strSort s2)
  | Arrow(s1, s2) -> Format.fmt2 "(%s -> %s)" (strSort s1) (strSort s2)
  | Sort s -> s

let rec docSort x = match x with
  | Bool_sort  -> doc_of_string "Bool"
  | Int_sort  -> doc_of_string "Int"
  | Term_sort -> doc_of_string "Term"
  | String_sort -> doc_of_string "FString"
  | Fuel_sort -> doc_of_string "Fuel"
  | BitVec_sort n -> form "_" [doc_of_string "BitVec"; doc_of_string (show n)]
  | Array(s1, s2) -> form "Array" [docSort s1; docSort s2]
  | Arrow(s1, s2) ->
    nest 1 (group (parens (docSort s1 ^^ doc_of_string " ->" ^/^ docSort s2)))
  | Sort s -> doc_of_string s

(** Note [Thunking Nullary Constants]

### The problem: Top-level nullary constants lead to SMT context
    pollution

Given a top-level nullary constant, say,

```let n : u32 = 0ul```

F* would encode this to SMT as (roughly)

```
(declare-fun n () Term)
(assert (HasType n u32))
(assert (n = U32.uint_to_t 0))
```

i.e., ground facts about the `n`'s typing and definition would be
introduced into the top-level SMT context.

Now, for a subsequent proof that has nothing to do with `n`, these
facts are still available in the context leading to clutter. E.g., in
this case, the `HasType n u32` leads to Z3 deriving facts like about
`0 <= n < pow2 32`, then potentially unfolding the `pow2 32` recursive
functions ... etc. all for potentially no good reason.

### The fix: Protect assumptions about nullary constants under a dummy
    quantifier

The change in this PR is to avoid introducing these ground facts into
the SMT context by default. Instead, we now thunk these nullary
constants, adding a dummy argument, like so:

```
(declare-fun n (Dummy_sort) Term)
(assert (forall ((x Dummy_sort) (! (HasType (n x) u32) :pattern ((n x)))))
(assert (forall ((x Dummy_sort) (! (= (n x) (U32.uint_to_t 0)) :pattern ((n x)))))
```

Now, instead of ground facts, we have quantified formulae that are
triggered on occurrences of `n x`.

Every occurrence of `n` in the rest of the proof is forced to `(n
Dummy_value)`: so, only when such an occurrence is present, do facts
about `n` become available, not polluting the context otherwise.

For some proofs in large contexts, this leads to massive SMT
performance gains: e.g., in miTLS with LowParse in context, some
queries in HSL.Common are sped up by 20x; Negotiation.fst has an
end-to-end speed up (full verification time) by 8-9x. etc. So, this
can be a big win.

#### An implementation detail

Note, this thunking happens at a very low-level in the SMT
encoding. Basically, the thunks are forced at the very last minute
just before terms are printed to SMT. This is important since it
ensures that things like sharing of SMT terms are not destroyed by
discrepancies in thunking behavior (and earlier attempt did thunking
at a higher level in the encoding, but this led to many regressions).

The bool in the fv is used in termToSmt to force the thunk before
printing.
 **)

let mk_decls name key decls aux_decls = [{
  sym_name    = Some name;
  key         = Some key;
  decls       = decls;
  a_names     =  //AR: collect the names of aux_decls and decls to be retained in case of a cache hit
    let sm = SMap.create 20 in
    List.iter (fun elt ->
      List.iter (fun s -> SMap.add sm s "0") elt.a_names
    ) aux_decls;
    List.iter (fun d -> match d with
                        | Assume a -> SMap.add sm (a.assumption_name) "0"
                        | _ -> ()) decls;
    SMap.keys sm
}]

let mk_decls_trivial decls = [{
  sym_name = None;
  key = None;
  decls = decls;
  a_names = List.collect (function
              | Assume a -> [a.assumption_name]
              | _ -> []) decls;
}]

let decls_list_of l = l |> List.collect (fun elt -> elt.decls)

let mk_fv (x, y) : fv = FV (x, y, false)

let fv_name (x:fv) = let FV (nm, _, _) = x in nm

instance deq_fv : deq fv = {
  (=?) = (fun fv1 fv2 -> fv_name fv1 = fv_name fv2);
}
instance ord_fv : ord fv = {
  super = deq_fv;
  cmp = (fun fv1 fv2 -> Order.order_from_int (BU.compare (fv_name fv1) (fv_name fv2)));
}

let fv_sort (x:fv) = let FV (_, sort, _) = x in sort
let fv_force (x:fv) = let FV (_, _, force) = x in force
let fv_eq (x:fv) (y:fv) = fv_name x = fv_name y
let fvs_subset_of (x:fvs) (y:fvs) =
  let open FStarC.Class.Setlike in
  subset (from_list x <: RBSet.t fv) (from_list y)

let freevar_eq x y = match x.tm, y.tm with
    | FreeV x, FreeV y -> fv_eq x y
    | _ -> false
let freevar_sort  = function
    | {tm=FreeV x} -> fv_sort x
    | _ -> failwith "impossible"
let fv_of_term = function
    | {tm=FreeV fv} -> fv
    | _ -> failwith "impossible"
let rec freevars t = match t.tm with
  | Integer _
  | String _
  | Real _
  | BoundV _ -> []
  | FreeV fv when fv_force fv -> [] //this is actually a top-level constant
  | FreeV fv -> [fv]
  | App(_, tms) -> List.collect freevars tms
  | Quant(_, _, _, _, t)
  | Labeled(t, _, _) -> freevars t
  | Let (es, body) -> List.collect freevars (body::es)

//memo-ized
let free_variables t = match !t.freevars with
  | Some b -> b
  | None ->
    let fvs = BU.remove_dups fv_eq (freevars t) in
    t.freevars := Some fvs;
    fvs

open FStarC.Class.Setlike
let free_top_level_names (t:term)
: RBSet.t string
= let rec free_top_level_names acc t =
    match t.tm with
    | FreeV (FV (nm, _, _)) -> add nm acc
    | App (Var s, args) -> 
      let acc = add s acc in
      List.fold_left free_top_level_names acc args
    | App (_, args) -> List.fold_left free_top_level_names acc args
    | Quant (_, pats, _, _, body) ->
      let acc = List.fold_left (fun acc pats -> List.fold_left free_top_level_names acc pats) acc pats in
      free_top_level_names acc body
    | Let(tms, t) ->
      let acc = List.fold_left free_top_level_names acc tms in
      free_top_level_names acc t
    | Labeled(t, _, _) -> free_top_level_names acc t
    | _ -> acc
  in
  free_top_level_names (empty()) t

(*****************************************************)
(* Pretty printing terms and decls in SMT Lib format *)
(*****************************************************)
let qop_to_string = function
  | Forall -> "forall"
  | Exists -> "exists"

let op_to_string = function
  | TrueOp -> "true"
  | FalseOp -> "false"
  | Not -> "not"
  | And -> "and"
  | Or  -> "or"
  | Imp -> "implies"
  | Iff -> "iff"
  | Eq  -> "="
  | LT  -> "<"
  | LTE -> "<="
  | GT  -> ">"
  | GTE -> ">="
  | Add -> "+"
  | Sub -> "-"
  | Div -> "div"
  | RealDiv -> "/"
  | Mul -> "*"
  | Minus -> "-"
  | Mod  -> "mod"
  | ITE -> "ite"
  | BvAnd -> "bvand"
  | BvXor -> "bvxor"
  | BvOr -> "bvor"
  | BvAdd -> "bvadd"
  | BvSub -> "bvsub"
  | BvShl -> "bvshl"
  | BvShr -> "bvlshr"
  | BvUdiv -> "bvudiv"
  | BvMod -> "bvurem"
  | BvMul -> "bvmul"
  | BvUlt -> "bvult"
  | BvToNat -> "bv2int"
  | BvUext n -> Format.fmt1 "(_ zero_extend %s)" (show n)
  | NatToBv n -> Format.fmt1 "(_ int2bv %s)" (show n)
  | Var s -> s

let weightToSmtStr : option int -> string = function
  | None -> ""
  | Some i -> Format.fmt1 ":weight %s\n" (show i)

let weightToSmt : option int -> list document = function
  | None -> []
  | Some i -> [nest 1 (group (doc_of_string ":weight" ^/^ doc_of_string (show i)))]

(* NOTE: these hashes are used for variable names in the encoding (Tm_refine_xxx, etc).
These names can affect the behavior of Z3 and make the difference between a success and
a failure, especially on flaky queries. So this function SHOULD NOT depend on any
external factors, like filepaths, timestamps, etc. There used to be a string_of_range
call here for the Labeled case, which caused flakiness across machines. *)
let rec hash_of_term' t =
  match t with
  | Integer i ->  i
  | String s -> s
  | Real r -> r
  | BoundV i  -> "@"^show i
  | FreeV x   -> fv_name x ^ ":" ^ strSort (fv_sort x) //Question: Why is the sort part of the hash?
  | App(op, tms) -> "("^(op_to_string op)^(List.map hash_of_term tms |> String.concat " ")^")"
  | Labeled(t, _, _) ->
    hash_of_term t // labels are semantically irrelevant, ignore them
  | Quant(qop, pats, wopt, sorts, body) ->
      "("
    ^ (qop_to_string qop)
    ^ " ("
    ^ (List.map strSort sorts |> String.concat " ")
    ^ ")(! "
    ^ (hash_of_term body)
    ^ " "
    ^ (weightToSmtStr wopt)
    ^ " "
    ^ (pats |> List.map (fun pats -> (List.map hash_of_term pats |> String.concat " ")) |> String.concat "; ")
    ^ "))"
  | Let (es, body) ->
    "(let (" ^ (List.map hash_of_term es |> String.concat " ") ^ ") " ^ hash_of_term body ^ ")"
and hash_of_term tm = hash_of_term' tm.tm

let mkBoxFunctions s = (s, s ^ "_proj_0")
let boxIntFun        = mkBoxFunctions "BoxInt"
let boxBoolFun       = mkBoxFunctions "BoxBool"
let boxStringFun     = mkBoxFunctions "BoxString"
let boxBitVecFun (sz:int) = mkBoxFunctions ("BoxBitVec" ^ show sz)
let boxRealFun       = mkBoxFunctions "BoxReal"

// Assume the Box/Unbox functions to be injective
let isInjective s =
    if (FStar.String.length s >= 3) then
        String.substring s 0 3 = "Box" &&
        not (List.existsML (fun c -> c = '.') (FStar.String.list_of_string s))
    else false

let mk t r = {tm=t; freevars=mk_ref None; rng=r}
let mkTrue  r       = mk (App(TrueOp, [])) r
let mkFalse r       = mk (App(FalseOp, [])) r
let mkUnreachable   = mk (App(Var "Unreachable", [])) Range.dummyRange
let mkInteger i  r  = mk (Integer (BU.ensure_decimal i)) r
let mkInteger' i r  = mkInteger (show i) r
let mkReal i r      = mk (Real i) r
let mkBoundV i r    = mk (BoundV i) r
let mkFreeV x r     = mk (FreeV x) r
let mkApp' f r      = mk (App f) r
let mkApp (s, args) r = mk (App (Var s, args)) r
let mkNot t r       = match t.tm with
  | App(TrueOp, _)  -> mkFalse r
  | App(FalseOp, _) -> mkTrue r
  | _ -> mkApp'(Not, [t]) r
let mkAnd (t1, t2) r = match t1.tm, t2.tm with
  | App(TrueOp, _), _ -> t2
  | _, App(TrueOp, _) -> t1
  | App(FalseOp, _), _
  | _, App(FalseOp, _) -> mkFalse r
  | App(And, ts1), App(And, ts2) -> mkApp'(And, ts1@ts2) r
  | _, App(And, ts2) -> mkApp'(And, t1::ts2) r
  | App(And, ts1), _ -> mkApp'(And, ts1@[t2]) r
  | _ -> mkApp'(And, [t1;t2]) r
let mkOr (t1, t2) r = match t1.tm, t2.tm with
  | App(TrueOp, _), _
  | _, App(TrueOp, _) -> mkTrue r
  | App(FalseOp, _), _ -> t2
  | _, App(FalseOp, _) -> t1
  | App(Or, ts1), App(Or, ts2) -> mkApp'(Or, ts1@ts2) r
  | _, App(Or, ts2) -> mkApp'(Or, t1::ts2) r
  | App(Or, ts1), _ -> mkApp'(Or, ts1@[t2]) r
  | _ -> mkApp'(Or, [t1;t2]) r
let mkImp (t1, t2) r = match t1.tm, t2.tm with
  | _, App(TrueOp, _)
  | App(FalseOp, _), _ -> mkTrue r
  | App(TrueOp, _), _ -> t2
  | _, App(Imp, [t1'; t2']) -> mkApp'(Imp, [mkAnd(t1, t1') r; t2']) r
  | _ -> mkApp'(Imp, [t1; t2]) r

let mk_bin_op op (t1,t2) r = mkApp'(op, [t1;t2]) r
let mkMinus t r = mkApp'(Minus, [t]) r
let mkNatToBv sz t r = mkApp'(NatToBv sz, [t]) r
let mkBvUext sz t r = mkApp'(BvUext sz, [t]) r
let mkBvToNat t r = mkApp'(BvToNat, [t]) r
let mkBvAnd = mk_bin_op BvAnd
let mkBvXor = mk_bin_op BvXor
let mkBvOr = mk_bin_op BvOr
let mkBvAdd = mk_bin_op BvAdd
let mkBvSub = mk_bin_op BvSub
let mkBvShl sz (t1, t2) r = mkApp'(BvShl, [t1;(mkNatToBv sz t2 r)]) r
let mkBvShr sz (t1, t2) r = mkApp'(BvShr, [t1;(mkNatToBv sz t2 r)]) r
let mkBvUdiv sz (t1, t2) r = mkApp'(BvUdiv, [t1;(mkNatToBv sz t2 r)]) r
let mkBvMod sz (t1, t2) r = mkApp'(BvMod, [t1;(mkNatToBv sz t2 r)]) r
let mkBvMul sz (t1, t2) r = mkApp' (BvMul, [t1;(mkNatToBv sz t2 r)]) r
let mkBvShl' sz (t1, t2) r = mkApp'(BvShl, [t1;t2]) r
let mkBvShr' sz (t1, t2) r = mkApp'(BvShr, [t1;t2]) r
let mkBvMul' sz (t1, t2) r = mkApp' (BvMul, [t1;t2]) r
let mkBvUdivUnsafe sz (t1, t2) r = mkApp'(BvUdiv, [t1;t2]) r
let mkBvModUnsafe sz (t1, t2) r = mkApp'(BvMod, [t1;t2]) r
let mkBvUlt = mk_bin_op BvUlt
let mkIff = mk_bin_op Iff
let mkEq (t1, t2) r = match t1.tm, t2.tm with
    | App (Var f1, [s1]), App (Var f2, [s2]) when f1 = f2 && isInjective f1 ->
        mk_bin_op Eq (s1, s2) r
    | _ -> mk_bin_op Eq (t1, t2) r
let mkLT  = mk_bin_op LT
let mkLTE = mk_bin_op LTE
let mkGT  = mk_bin_op GT
let mkGTE = mk_bin_op GTE
let mkAdd = mk_bin_op Add
let mkSub = mk_bin_op Sub
let mkDiv = mk_bin_op Div
let mkRealDiv = mk_bin_op RealDiv
let mkMul = mk_bin_op Mul
let mkMod = mk_bin_op Mod
let mkRealOfInt t r = mkApp ("to_real", [t]) r
let mkITE (t1, t2, t3) r =
  match t1.tm with
  | App(TrueOp, _) -> t2
  | App(FalseOp, _) -> t3
  | _ -> begin
    match t2.tm, t3.tm with
    | App(TrueOp,_), App(TrueOp, _) -> mkTrue r
    | App(TrueOp,_), _ -> mkImp (mkNot t1 t1.rng, t3) r
    | _, App(TrueOp, _) -> mkImp(t1, t2) r
    | _, _ ->  mkApp'(ITE, [t1; t2; t3]) r
  end
let mkCases t r = match t with
  | [] -> failwith "Impos"
  | hd::tl -> List.fold_left (fun out t -> mkAnd (out, t) r) hd tl


let check_pattern_ok (t:term) : option term =
    let rec aux t =
        match t.tm with
        | Integer _
        | String _
        | Real _
        | BoundV _
        | FreeV _ -> None
        | Let(tms, tm) ->
          aux_l (tm::tms)
        | App(head, terms) ->
            let head_ok =
                match head with
                | Var _ -> true
                | TrueOp
                | FalseOp -> true
                | Not
                | And
                | Or
                | Imp
                | Iff
                | Eq -> false
                | LT
                | LTE
                | GT
                | GTE
                | Add
                | Sub
                | Div
                | RealDiv
                | Mul
                | Minus
                | Mod -> true
                | BvAnd
                | BvXor
                | BvOr
                | BvAdd
                | BvSub
                | BvShl
                | BvShr
                | BvUdiv
                | BvMod
                | BvMul
                | BvUlt
                | BvUext _
                | NatToBv _
                | BvToNat
                | ITE -> false
            in
            if not head_ok then Some t
            else aux_l terms
        | Labeled(t, _, _) ->
          aux t
        | Quant _ -> Some t
    and aux_l ts =
        match ts with
        | [] -> None
        | t::ts ->
          match aux t with
          | Some t -> Some t
          | None -> aux_l ts
    in
    aux t

 let rec print_smt_term (t:term) :string =
  match t.tm with
  | Integer n               -> Format.fmt1 "(Integer %s)" n
  | String s                -> Format.fmt1 "(String %s)" s
  | Real r                  -> Format.fmt1 "(Real %s)" r
  | BoundV  n               -> Format.fmt1 "(BoundV %s)" (show n)
  | FreeV  fv               -> Format.fmt1 "(FreeV %s)" (fv_name fv)
  | App (op, l)             -> Format.fmt2 "(%s %s)" (op_to_string op) (print_smt_term_list l)
  | Labeled(t, r1, r2)      -> Format.fmt2 "(Labeled '%s' %s)" (Errors.Msg.rendermsg r1) (print_smt_term t)
  | Quant (qop, l, _, _, t) -> Format.fmt3 "(%s %s %s)" (qop_to_string qop) (print_smt_term_list_list l) (print_smt_term t)
  | Let (es, body) -> Format.fmt2 "(let %s %s)" (print_smt_term_list es) (print_smt_term body)

and print_smt_term_list (l:list term) :string = List.map print_smt_term l |> String.concat " "

and print_smt_term_list_list (l:list (list term)) :string =
    List.fold_left (fun s l -> (s ^ "; [ " ^ (print_smt_term_list l) ^ " ] ")) "" l

let mkQuant r check_pats (qop, pats, wopt, vars, body) =
    let all_pats_ok pats =
        if not check_pats then pats else
        match BU.find_map pats (fun x -> BU.find_map x check_pattern_ok) with
        | None -> pats
        | Some p ->
          begin
            Errors.log_issue r Errors.Warning_SMTPatternIllFormed
              (Format.fmt1 "Pattern (%s) contains illegal symbols; dropping it" (print_smt_term p));
            []
           end
    in
    if List.length vars = 0 then body
    else match body.tm with
         | App(TrueOp, _) -> body
         | _ -> mk (Quant(qop, all_pats_ok pats, wopt, vars, body)) r

let mkLet (es, body) r =
  if List.length es = 0 then body
  else mk (Let (es,body)) r

(*****************************************************)
(* abstracting free names; instantiating bound vars  *)
(*****************************************************)
let abstr fvs t = //fvs is a subset of the free vars of t; the result closes over fvs
  let nvars = List.length fvs in
  let index_of fv = match BU.try_find_index (fv_eq fv) fvs with
    | None -> None
    | Some i -> Some (nvars - (i + 1))
  in
  let rec aux ix t =
    match !t.freevars with
    | Some [] -> t
    | _ ->
      begin match t.tm with
        | Integer _
        | String _
        | Real _
        | BoundV _ -> t
        | FreeV x ->
          begin match index_of x with
            | None -> t
            | Some i -> mkBoundV (i + ix) t.rng
          end
        | App(op, tms) -> mkApp'(op, List.map (aux ix) tms) t.rng
        | Labeled(t, r1, r2) -> mk (Labeled(aux ix t, r1, r2)) t.rng
        | Quant(qop, pats, wopt, vars, body) ->
          let n = List.length vars in
          mkQuant t.rng false (qop, pats |> List.map (List.map (aux (ix + n))), wopt, vars, aux (ix + n) body)
        | Let (es, body) ->
          let ix, es_rev = List.fold_left (fun (ix, l) e -> ix+1, aux ix e::l) (ix, []) es in
          mkLet (List.rev es_rev, aux ix body) t.rng
      end
  in
  aux 0 t

let inst tms t =
  let tms = List.rev tms in //forall x y . t   ... y is an index 0 in t
  let n = List.length tms in //instantiate the first n BoundV's with tms, in order
  let rec aux shift t = match t.tm with
    | Integer _
    | String _
    | Real _
    | FreeV _ -> t
    | BoundV i ->
      if 0 <= i - shift && i - shift < n
      then List.nth tms (i - shift)
      else t
    | App(op, tms) -> mkApp'(op, List.map (aux shift) tms) t.rng
    | Labeled(t, r1, r2) -> mk (Labeled(aux shift t, r1, r2)) t.rng
    | Quant(qop, pats, wopt, vars, body) ->
      let m = List.length vars in
      let shift = shift + m in
      mkQuant t.rng false (qop, pats |> List.map (List.map (aux shift)), wopt, vars, aux shift body)
    | Let (es, body) ->
      let shift, es_rev = List.fold_left (fun (ix, es) e -> shift+1, aux shift e::es) (shift, []) es in
      mkLet (List.rev es_rev, aux shift body) t.rng
  in
  aux 0 t

let subst (t:term) (fv:fv) (s:term) = inst [s] (abstr [fv] t)
let mkQuant' r (qop, pats, wopt, vars, body) =
    mkQuant r true (qop, pats |> List.map (List.map (abstr vars)), wopt, List.map fv_sort vars, abstr vars body)

//these are the external facing functions for building quantifiers
let mkForall r (pats, vars, body) =
    mkQuant' r (Forall, pats, None, vars, body)
let mkForall'' r (pats, wopt, sorts, body) =
    mkQuant r true (Forall, pats, wopt, sorts, body)
let mkForall' r (pats, wopt, vars, body) =
    mkQuant' r (Forall, pats, wopt, vars, body)
let mkExists r (pats, vars, body) =
    mkQuant' r (Exists, pats, None, vars, body)

let mkLet' (bindings, body) r =
  let vars, es = List.split bindings in
  mkLet (es, abstr vars body) r

let norng = Range.dummyRange
let mkDefineFun (nm, vars, s, tm, c) = DefineFun(nm, List.map fv_sort vars, s, abstr vars tm, c)
let constr_id_of_sort sort = Format.fmt1 "%s_constr_id" (strSort sort)
let fresh_token (tok_name, sort) id =
    let a_name = "fresh_token_" ^tok_name in
    let tm = mkEq(mkInteger' id norng,
                                  mkApp(constr_id_of_sort sort,
                                        [mkApp (tok_name,[]) norng]) norng) norng in
    let a = {assumption_name=escape a_name;
             assumption_caption=Some "fresh token";
             assumption_term=tm;
             assumption_fact_ids=[];
             assumption_free_names=free_top_level_names tm} in
    Assume a

let fresh_constructor rng (name, arg_sorts, sort, id) =
  let id = show id in
  let bvars = arg_sorts |> List.mapi (fun i s -> mkFreeV(mk_fv ("x_" ^ show i, s)) norng) in
  let bvar_names = List.map fv_of_term bvars in
  let capp = mkApp(name, bvars) norng in
  let cid_app = mkApp(constr_id_of_sort sort, [capp]) norng in
  let a_name = "constructor_distinct_" ^name in
  let tm = mkForall rng ([[capp]], bvar_names, mkEq(mkInteger id norng, cid_app) norng) in
  let a = {
    assumption_name=escape a_name;
    assumption_caption=Some "Constructor distinct";
    assumption_term=tm;
    assumption_fact_ids=[];
    assumption_free_names=free_top_level_names tm
  } in
  Assume a

let injective_constructor
  (rng:Range.t)
  ((name, fields, sort):(string & list constructor_field & sort)) :list decl =
    let n_bvars = List.length fields in
    let bvar_name i = "x_" ^ show i in
    let bvar_index i = n_bvars - (i + 1) in
    let bvar i s = mkFreeV <| mk_fv (bvar_name i, s) in
    let bvars = fields |> List.mapi (fun i f -> bvar i f.field_sort norng) in
    let bvar_names = List.map fv_of_term bvars in
    let capp = mkApp(name, bvars) norng in
    fields
    |> List.mapi (fun i {field_projectible=projectible; field_name=name; field_sort=s} ->
            if projectible
            then
              let cproj_app = mkApp(name, [capp]) norng in
              let proj_name = DeclFun(name, [sort], s, Some "Projector") in
              let tm = mkForall rng ([[capp]], bvar_names, mkEq(cproj_app, bvar i s norng) norng) in
              let a = {
                    assumption_name = escape ("projection_inverse_"^name);
                    assumption_caption = Some "Projection inverse";
                    assumption_term = tm;
                    assumption_fact_ids = [];
                    assumption_free_names = free_top_level_names tm
                 } in
              [proj_name; Assume a]
            else [])
    |> List.flatten

let discriminator_name constr = "is-"^constr.constr_name

let constructor_to_decl rng constr =
    let sort = constr.constr_sort in
    let field_sorts = constr.constr_fields |> List.map (fun f -> f.field_sort) in
    let cdecl = DeclFun(constr.constr_name, field_sorts, constr.constr_sort, Some "Constructor") in
    let cid = 
      match constr.constr_id with
      | None -> []
      | Some id -> [fresh_constructor rng (constr.constr_name, field_sorts, sort, id)]
    in
    let disc =
        let disc_name = discriminator_name constr in
        let xfv = mk_fv ("x", sort) in
        let xx = mkFreeV xfv norng in
        let proj_terms, ex_vars =
            constr.constr_fields
         |> List.mapi (fun i {field_projectible=projectible; field_sort=s; field_name=proj} ->
                if projectible
                then mkApp(proj, [xx]) norng, []
                else let fi = mk_fv ("f_" ^ show i, s) in
                     mkFreeV fi norng, [fi])
         |> List.split in
        let ex_vars = List.flatten ex_vars in
        let disc_inv_body = mkEq(xx, mkApp(constr.constr_name, proj_terms) norng) norng in
        let disc_inv_body = match ex_vars with
            | [] -> disc_inv_body
            | _ -> mkExists norng ([], ex_vars, disc_inv_body) in
        let disc_ax =
          match constr.constr_id with
          | None -> disc_inv_body
          | Some id ->
            let disc_eq = mkEq(mkApp(constr_id_of_sort constr.constr_sort, [xx]) norng, mkInteger (show id) norng) norng in
            mkAnd(disc_eq, disc_inv_body) norng in
        let def = mkDefineFun(disc_name, [xfv], Bool_sort,
                    disc_ax,
                    Some "Discriminator definition") in
        def in
    let projs = injective_constructor rng (constr.constr_name, constr.constr_fields, sort) in
    let base =
      if not constr.constr_base
      then []
      else (
        let arg_sorts =
          constr.constr_fields 
          |> List.filter (fun f -> f.field_projectible)
          |> List.map (fun _ -> Term_sort)
        in
        let base_name = constr.constr_name ^ "@base" in
        let decl = DeclFun(base_name, arg_sorts, Term_sort, Some "Constructor base") in
        let formals = List.mapi (fun i _ -> mk_fv ("x" ^ show i, Term_sort)) constr.constr_fields in
        let constructed_term = mkApp(constr.constr_name, List.map (fun fv -> mkFreeV fv norng) formals) norng in
        let inj_formals = List.flatten <| List.map2 (fun f fld -> if fld.field_projectible then [f] else []) formals constr.constr_fields in
        let base_term = mkApp(base_name, List.map (fun fv -> mkFreeV fv norng) inj_formals) norng in
        let eq = mkEq(constructed_term, base_term) norng in
        let guard = mkApp(discriminator_name constr, [constructed_term]) norng in
        let q = mkForall rng ([[constructed_term]], formals, mkImp (guard, eq) norng) in
        //forall (x0...xn:Term). {:pattern (C x0 ...xn)} is-C (C x0..xn) ==> C x0..xn == C-base x2 x3..xn
        let a = {
          assumption_name=escape ("constructor_base_" ^ constr.constr_name);
          assumption_caption=Some "Constructor base";
          assumption_term=q;
          assumption_fact_ids=[];
          assumption_free_names=free_top_level_names q
        } in
        [decl; Assume a]
    )
    in
    Caption (Format.fmt1 "<start constructor %s>" constr.constr_name)::
    [cdecl]@cid@projs@[disc]@base
    @[Caption (Format.fmt1 "</end constructor %s>" constr.constr_name)]

(****************************************************************************)
(* Standard SMTLib prelude for F* and some term constructors                *)
(****************************************************************************)
let name_binders_inner prefix_opt (outer_names:list fv) start sorts =
    let names, binders, n = sorts |> List.fold_left (fun (names, binders, n) s ->
        let prefix = match s with
            | Term_sort -> "@x"
            | _ -> "@u" in
        let prefix =
            match prefix_opt with
            | None -> prefix
            | Some p -> p ^ prefix in
        let nm = prefix ^ show n in
        let names = mk_fv (nm,s)::names in
        let b = form nm [docSort s] in
        names, b::binders, n+1)
        (outer_names, [], start)  in
    names, List.rev binders, n

let name_macro_binders sorts =
    let names, binders, n = name_binders_inner (Some "__") [] 0 sorts in
    List.rev names, binders

let mk_tag f attrs = form_core ((doc_of_string "! " ^^ f) :: attrs)

let termToSmt
  : print_ranges:bool -> enclosing_name:string -> t:term -> document
  =
  //a counter and a hash table for string constants to integer ids mapping
  let string_id_counter = mk_ref 0 in
  let string_cache= SMap.create 20 in

  fun print_ranges enclosing_name t ->
      let next_qid =
          let ctr = mk_ref 0 in
          fun depth ->
            let n = !ctr in
            BU.incr ctr;
            if n = 0 then enclosing_name
            else Format.fmt2 "%s.%s" enclosing_name (show n)
      in
      let remove_guard_free pats =
        pats |> List.map (fun ps ->
          ps |> List.map (fun tm ->
            match tm.tm with
            | App(Var "Prims.guard_free", [{tm=BoundV _}]) -> tm
            | App(Var "Prims.guard_free", [p]) -> p
            | _ -> tm))
      in
      let rec aux' depth n (names:list fv) t : document =
        let aux = aux (depth + 1) in
        match t.tm with
        | Integer i -> doc_of_string i
        | Real r -> doc_of_string r
        | String s ->
          let id_opt = SMap.try_find string_cache s in
          doc_of_string (match id_opt with
           | Some id -> id
           | None ->
             let id = !string_id_counter |> show in
             BU.incr string_id_counter;
             SMap.add string_cache s id;
             id)
        | BoundV i ->
          List.nth names i |> fv_name |> doc_of_string
        | FreeV x when fv_force x -> form (fv_name x) [doc_of_string "Dummy_value"] //force a thunked name
        | FreeV x -> doc_of_string (fv_name x)
        | App(op, []) -> doc_of_string (op_to_string op)
        | App(op, tms) -> form (op_to_string op) (List.map (aux n names) tms)
        | Labeled(t, _, _) -> aux n names t
        | Quant(qop, pats, wopt, sorts, body) ->
          let qid = next_qid () in
          let names, binders, n = name_binders_inner None names n sorts in
          let pats = remove_guard_free pats in
          let pats_str =
            match pats with
            | [[]]
            | [] -> [] //if print_ranges then [doc_of_string ";; no pats" ^^ hardline] else []
            | _ -> List.map (fun pats -> mk_pattern (form_core (List.map (aux n names) pats))) pats
          in
          binder (qop_to_string qop) (form_core binders)
            [mk_tag (aux n names body) (weightToSmt wopt @ pats_str @ [mk_qid qid])]

        | Let (es, body) ->
          (* binders are reversed but according to the smt2 standard *)
          (* substitution should occur in parallel and order should not matter *)
          let names, binders, n =
            List.fold_left (fun (names0, binders, n0) e ->
              let nm = "@lb" ^ show n0 in
              let names0 = mk_fv (nm, Term_sort)::names0 in
              let b = form nm [aux n names e] in
              names0, b::binders, n0+1)
            (names, [], n)
            es
          in
          binder "let" (form_core binders) [aux n names body]

      and aux depth n names t : document =
        let s = aux' depth n names t in
        if print_ranges && t.rng <> norng
        then
          doc_of_string ";; def=" ^^ doc_of_string (Range.string_of_range t.rng) ^^
          doc_of_string "; use=" ^^ doc_of_string (Range.string_of_use_range t.rng) ^^ hardline ^^
          s
        else s
      in
      aux 0 0 [] t

let rec declToSmt' print_captions z3options decl : document =
  let with_caption c body =
    match c with
    | Some c when print_captions ->
      let c = String.split ['\n'] c |> List.map BU.trim_string |> String.concat " " in
      doc_of_string ("; " ^ c) ^^ hardline ^^ body
    | _ -> body in
  match decl with
  | DefPrelude ->
    doc_of_string (mkPrelude z3options)
  | Module (s, decls) ->
    let res = separate_map hardline (declToSmt' print_captions z3options) decls in
    if Options.keep_query_captions()
    then
      doc_of_string ";;; Start " ^^ doc_of_string s ^^ hardline ^^
      res ^^ hardline ^^
      doc_of_string ";;; End " ^^ doc_of_string s ^^
        parens (doc_of_string (show (List.length decls)) ^^ doc_of_string " decls") ^^ hardline
    else res
  | Caption c ->
    if print_captions
    then (BU.splitlines c |> separate_map hardline (fun s -> doc_of_string ("; " ^ s)))
    else FStarC.Pprint.empty
  | DeclFun(f,argsorts,retsort,c) ->
    with_caption c <|
      form "declare-fun" [
        doc_of_string f;
        form_core (List.map docSort argsorts);
        docSort retsort;
      ]
  | DefineFun(f,arg_sorts,retsort,body,c) ->
    let names, binders = name_macro_binders arg_sorts in
    let body = inst (List.map (fun x -> mkFreeV x norng) names) body in
    with_caption c <|
      form_core [
        group (nest 1 (separate (break_ 1) [
          doc_of_string "define-fun";
          doc_of_string f;
          form_core binders;
          docSort retsort;
        ]));
        termToSmt print_captions (escape f) body;
      ]
  | Assume a ->
    let fact_ids_to_string ids =
        ids |> List.map (function
        | Name n -> "Name " ^ Ident.string_of_lid n
        | Namespace ns -> "Namespace " ^ Ident.string_of_lid ns
        | Tag t -> "Tag " ^t)
    in
    let fids =
        if print_captions
        then Format.fmt1 ";;; Fact-ids: %s\n"
                        (String.concat "; " (fact_ids_to_string a.assumption_fact_ids))
        else "" in
    let n = a.assumption_name in
    with_caption a.assumption_caption <|
      doc_of_string fids ^^ // FIXME
      form "assert" [
        mk_tag (termToSmt print_captions n a.assumption_term) [mk_named n]
      ]
  | Eval t ->
    form "eval" [termToSmt print_captions "eval" t]
  | Echo s ->
    form "echo" [doc_of_string "\"" ^^ doc_of_string s ^^ doc_of_string "\""]
  | RetainAssumptions _ ->
    FStarC.Pprint.empty
  | CheckSat -> doc_of_string "(echo \"<result>\")\n(check-sat)\n(echo \"</result>\")"
  | GetUnsatCore -> doc_of_string "(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
  | EmptyLine -> FStarC.Pprint.empty
  | Push n -> doc_of_string "(push) ;; push{" ^^ doc_of_string (show n)
  | Pop n -> doc_of_string "(pop) ;; " ^^ doc_of_string (show n) ^^ doc_of_string "}pop"
  | SetOption (s, v) ->
    form "set-option" [
      doc_of_string (":" ^ s);
      doc_of_string v;
    ]
  | GetStatistics -> doc_of_string "(echo \"<statistics>\") (get-info :all-statistics) (echo \"</statistics>\")"
  | GetReasonUnknown-> doc_of_string "(echo \"<reason-unknown>\") (get-info :reason-unknown) (echo \"</reason-unknown>\")"

and declToSmt z3options decl =
  render <| declToSmt' (Options.keep_query_captions())  z3options decl

and mkPrelude z3options =
  let basic = z3options ^
                "(declare-sort FString)\n\
                (declare-fun FString_constr_id (FString) Int)\n\
                \n\
                (declare-sort Term)\n\
                (declare-fun Term_constr_id (Term) Int)\n\
                (declare-sort Dummy_sort)\n\
                (declare-fun Dummy_value () Dummy_sort)\n\
                (declare-datatypes () ((Fuel \n\
                                        (ZFuel) \n\
                                        (SFuel (prec Fuel)))))\n\
                (declare-fun MaxIFuel () Fuel)\n\
                (declare-fun MaxFuel () Fuel)\n\
                (declare-fun PreType (Term) Term)\n\
                (declare-fun Valid (Term) Bool)\n\
                (declare-fun HasTypeFuel (Fuel Term Term) Bool)\n\
                (define-fun HasTypeZ ((x Term) (t Term)) Bool\n\
                    (HasTypeFuel ZFuel x t))\n\
                (define-fun HasType ((x Term) (t Term)) Bool\n\
                    (HasTypeFuel MaxIFuel x t))\n\
                (declare-fun IsTotFun (Term) Bool)\n
                ;;fuel irrelevance\n\
                (assert (forall ((f Fuel) (x Term) (t Term))\n\
                                (! (= (HasTypeFuel (SFuel f) x t)\n\
                                          (HasTypeZ x t))\n\
                                   :pattern ((HasTypeFuel (SFuel f) x t)))))\n\
                (declare-fun NoHoist (Term Bool) Bool)\n\
                ;;no-hoist\n\
                (assert (forall ((dummy Term) (b Bool))\n\
                                (! (= (NoHoist dummy b) b)\n\
                                   :pattern ((NoHoist dummy b)))))\n\
                (define-fun  IsTyped ((x Term)) Bool\n\
                    (exists ((t Term)) (HasTypeZ x t)))\n\
                (declare-fun ApplyTF (Term Fuel) Term)\n\
                (declare-fun ApplyTT (Term Term) Term)\n\
                (declare-fun Prec (Term Term) Bool)\n\
                (assert (forall ((x Term) (y Term) (z Term))\n\
                                (! (implies (and (Prec x y) (Prec y z)) (Prec x z))\n\
                                   :pattern ((Prec x z) (Prec x y)))))\n\
                (assert (forall ((x Term) (y Term))\n\
                         (implies (Prec x y)\n\
                                  (not (Prec y x)))))\n\
                (declare-fun Closure (Term) Term)\n\
                (declare-fun ConsTerm (Term Term) Term)\n\
                (declare-fun ConsFuel (Fuel Term) Term)\n\
                (declare-fun Tm_uvar (Int) Term)\n\
                (define-fun Reify ((x Term)) Term x)\n\
                (declare-fun Prims.precedes (Term Term Term Term) Term)\n\
                (declare-fun Range_const (Int) Term)\n\
                (declare-fun _mul (Int Int) Int)\n\
                (declare-fun _div (Int Int) Int)\n\
                (declare-fun _mod (Int Int) Int)\n\
                (declare-fun __uu__PartialApp () Term)\n\
                (assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n\
                (assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n\
                (assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))\n\
                (declare-fun _rmul (Real Real) Real)\n\
                (declare-fun _rdiv (Real Real) Real)\n\
                (assert (forall ((x Real) (y Real)) (! (= (_rmul x y) (* x y)) :pattern ((_rmul x y)))))\n\
                (assert (forall ((x Real) (y Real)) (! (= (_rdiv x y) (/ x y)) :pattern ((_rdiv x y)))))\n\
                (define-fun Unreachable () Bool false)"
   in
   let as_constr (name, fields, sort, id, _injective)
     : constructor_t
     = { constr_name=name;
         constr_fields=List.map (fun (field_name, field_sort, field_projectible) -> {field_name; field_sort; field_projectible}) fields;
         constr_sort=sort;
         constr_id=Some id;
         constr_base=false }
   in
   let constrs : constructors = 
     List.map as_constr
       [("FString_const", ["FString_const_proj_0", Int_sort, true], String_sort, 0, true);
        ("Tm_type",  [], Term_sort, 2, true);
        ("Tm_arrow", [("Tm_arrow_id", Int_sort, true)],  Term_sort, 3, false);
        ("Tm_unit",  [], Term_sort, 6, true);
        (fst boxIntFun,     [snd boxIntFun,  Int_sort, true],   Term_sort, 7, true);
        (fst boxBoolFun,    [snd boxBoolFun, Bool_sort, true],  Term_sort, 8, true);
        (fst boxStringFun,  [snd boxStringFun, String_sort, true], Term_sort, 9, true);
        (fst boxRealFun,    [snd boxRealFun, Sort "Real", true], Term_sort, 10, true)] in
   let bcons = constrs |> List.collect (constructor_to_decl norng)
                       |> List.map (declToSmt z3options) |> String.concat "\n" in

   let precedes_partial_app = "\n\
     (declare-fun Prims.precedes@tok () Term)\n\
     (assert\n\
      (forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))\n\
       (! (= (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.precedes@tok @x0) @x1) @x2) @x3)
        (Prims.precedes @x0 @x1 @x2 @x3))\n\
       :pattern ((ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.precedes@tok @x0) @x1) @x2) @x3)))))\n" in

   let lex_ordering = "\n(declare-fun Prims.lex_t () Term)\n\
                      (assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n\
                                                          (! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n\
                                                                  (Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n\
                                                          :pattern (Prims.precedes t1 t2 e1 e2))))\n\
                      (assert (forall ((t1 Term) (t2 Term))\n\
                                      (! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n\
                                              (Prec t1 t2))\n\
                                      :pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n" in

   let valid_intro =
     "(assert (forall ((e Term) (t Term))\n\
                      (! (implies (HasType e t)\n\
                                  (Valid t))\n\
                       :pattern ((HasType e t)\n\
                                 (Valid t))\n\
                       :qid __prelude_valid_intro)))\n"
   in
   let valid_elim =
     "(assert (forall ((t Term))\n\
                      (! (implies (Valid t)\n\
                                  (exists ((e Term)) (HasType e t)))\n\
                       :pattern ((Valid t))\n\
                       :qid __prelude_valid_elim)))\n"
   in
   basic
   ^ bcons
   ^ precedes_partial_app
   ^ lex_ordering
   ^ (if FStarC.Options.smtencoding_valid_intro()
      then valid_intro
      else "")
   ^ (if FStarC.Options.smtencoding_valid_elim()
      then valid_elim
      else "")

let declsToSmt        z3options decls = List.map (declToSmt z3options) decls |> String.concat "\n"
let declToSmt_no_caps z3options decl = render <| declToSmt' false z3options decl

(* Generate boxing/unboxing functions for bitvectors of various sizes. *)
(* For ids, to avoid dealing with generation of fresh ids,
   I am computing them based on the size in this not very robust way.
   z3options are only used by the prelude so passing the empty string should be ok. *)
let mkBvConstructor (sz : int) =
  let constr : constructor_t = {
    constr_name=fst (boxBitVecFun sz);
    constr_sort=Term_sort;
    constr_id=None;
    constr_fields=[{field_projectible=true; field_name=snd (boxBitVecFun sz); field_sort=BitVec_sort sz }];
    constr_base=false
  } in
  constructor_to_decl norng constr, 
  constr.constr_name, 
  discriminator_name constr

let __range_c = mk_ref 0
let mk_Range_const () =
    let i = !__range_c in
    __range_c := !__range_c + 1;
    mkApp("Range_const", [mkInteger' i norng]) norng

let mk_Term_type        = mkApp("Tm_type", []) norng
let mk_Term_app t1 t2 r = mkApp("Tm_app", [t1;t2]) r
let mk_Term_uvar i    r = mkApp("Tm_uvar", [mkInteger' i norng]) r
let mk_Term_unit        = mkApp("Tm_unit", []) norng
let elim_box cond u v t =
    match t.tm with
    | App(Var v', [t]) when v=v' && cond -> t
    | _ -> mkApp(u, [t]) t.rng
let maybe_elim_box u v t =
    elim_box (Options.smtencoding_elim_box()) u v t
let boxInt t      = maybe_elim_box (fst boxIntFun) (snd boxIntFun) t
let unboxInt t    = maybe_elim_box (snd boxIntFun) (fst boxIntFun) t
let boxBool t     = maybe_elim_box (fst boxBoolFun) (snd boxBoolFun) t
let unboxBool t   = maybe_elim_box (snd boxBoolFun) (fst boxBoolFun) t
let boxString t   = maybe_elim_box (fst boxStringFun) (snd boxStringFun) t
let unboxString t = maybe_elim_box (snd boxStringFun) (fst boxStringFun) t
let boxReal t     = maybe_elim_box (fst boxRealFun) (snd boxRealFun) t
let unboxReal t   = maybe_elim_box (snd boxRealFun) (fst boxRealFun) t
let boxBitVec (sz:int) t =
    elim_box true (fst (boxBitVecFun sz)) (snd (boxBitVecFun sz)) t
let unboxBitVec (sz:int) t =
    elim_box true (snd (boxBitVecFun sz)) (fst (boxBitVecFun sz)) t
let boxTerm sort t = match sort with
  | Int_sort -> boxInt t
  | Bool_sort -> boxBool t
  | String_sort -> boxString t
  | BitVec_sort sz -> boxBitVec sz t
  | Sort "Real" -> boxReal t
  | _ -> raise BU.Impos
let unboxTerm sort t = match sort with
  | Int_sort -> unboxInt t
  | Bool_sort -> unboxBool t
  | String_sort -> unboxString t
  | BitVec_sort sz -> unboxBitVec sz t
  | Sort "Real" -> unboxReal t
  | _ -> raise BU.Impos

let getBoxedInteger (t:term) =
  match t.tm with
  | App(Var s, [t2]) when s = fst boxIntFun ->
    begin
    match t2.tm with
    | Integer n -> Some (BU.int_of_string n)
    | _ -> None
    end
  | _ -> None

let mk_PreType t      = mkApp("PreType", [t]) t.rng
let mk_Valid t        = match t.tm with
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_Equality", [_; t1; t2])}]) -> mkEq (t1, t2) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_disEquality", [_; t1; t2])}]) -> mkNot (mkEq (t1, t2) norng) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_LessThanOrEqual", [t1; t2])}]) -> mkLTE (unboxInt t1, unboxInt t2) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_LessThan", [t1; t2])}]) -> mkLT (unboxInt t1, unboxInt t2) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_GreaterThanOrEqual", [t1; t2])}]) -> mkGTE (unboxInt t1, unboxInt t2) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_GreaterThan", [t1; t2])}]) -> mkGT (unboxInt t1, unboxInt t2) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_AmpAmp", [t1; t2])}]) -> mkAnd (unboxBool t1, unboxBool t2) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_BarBar", [t1; t2])}]) -> mkOr (unboxBool t1, unboxBool t2) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "Prims.op_Negation", [t])}]) -> mkNot (unboxBool t) t.rng
    | App(Var "Prims.b2t", [{tm=App(Var "FStar.BV.bvult", [t0; t1;t2])}])
    | App(Var "Prims.equals", [_; {tm=App(Var "FStar.BV.bvult", [t0; t1;t2])}; _])
            when (Some? (getBoxedInteger t0))->
        // sometimes b2t gets needlessly normalized...
        let sz = match getBoxedInteger t0 with | Some sz -> sz | _ -> failwith "impossible" in
        mkBvUlt (unboxBitVec sz t1, unboxBitVec sz t2) t.rng
    | App(Var "Prims.b2t", [t1]) -> {unboxBool t1 with rng=t.rng}
    | _ ->
        mkApp("Valid",  [t]) t.rng
let mk_unit_type = mkApp("Prims.unit", []) norng
let mk_subtype_of_unit v = mkApp("Prims.subtype_of", [v;mk_unit_type]) v.rng
let mk_HasType v t    = mkApp("HasType", [v;t]) t.rng
let mk_HasTypeZ v t   = mkApp("HasTypeZ", [v;t]) t.rng
let mk_IsTotFun t     = mkApp("IsTotFun", [t]) t.rng
let mk_HasTypeFuel f v t =
   if Options.unthrottle_inductives()
   then mk_HasType v t
   else mkApp("HasTypeFuel", [f;v;t]) t.rng
let mk_HasTypeWithFuel f v t = match f with
    | None -> mk_HasType v t
    | Some f -> mk_HasTypeFuel f v t
let mk_NoHoist dummy b = mkApp("NoHoist", [dummy;b]) b.rng
let mk_tester n t     = mkApp("is-"^n,   [t]) t.rng
let mk_ApplyTF t t'   = mkApp("ApplyTF", [t;t']) t.rng
let mk_ApplyTT t t'  r  = mkApp("ApplyTT", [t;t']) r
let kick_partial_app t  = mk_ApplyTT (mkApp("__uu__PartialApp", []) t.rng) t t.rng |> mk_Valid
let mk_String_const s r = mkApp ("FString_const", [mk (String s) r]) r
let mk_Precedes x1 x2 x3 x4 r = mkApp("Prims.precedes", [x1;x2;x3;x4])  r|> mk_Valid
let rec n_fuel n =
    if n = 0 then mkApp("ZFuel", []) norng
    else mkApp("SFuel", [n_fuel (n - 1)]) norng

let mk_and_l l r = List.fold_right (fun p1 p2 -> mkAnd(p1, p2) r) l (mkTrue r)

let mk_or_l l r = List.fold_right (fun p1 p2 -> mkOr(p1,p2) r) l (mkFalse r)

let mk_haseq t = mk_Valid (mkApp ("Prims.hasEq", [t]) t.rng)
let dummy_sort = Sort "Dummy_sort"

instance showable_smt_term = {
  show = print_smt_term;
}

instance showable_decl = {
  show = declToSmt_no_caps "";
}

let rec names_of_decl d =
  match d with
  | Assume a -> [a.assumption_name]
  | Module (_, ds) -> List.collect names_of_decl ds
  | _ -> []

let decl_to_string_short d =
  match d with
  | DefPrelude -> "prelude"
  | DeclFun (s, _, _, _) -> "DeclFun " ^ s
  | DefineFun (s, _, _, _, _) -> "DefineFun " ^ s
  | Assume a -> "Assumption " ^ a.assumption_name
  | Caption s -> "Caption " ^s
  | Module (s, _) -> "Module " ^ s
  | Eval _ -> "Eval"
  | Echo s -> "Echo " ^ s
  | RetainAssumptions _ -> "RetainAssumptions"
  | Push n -> Format.fmt1 "push %s" (show n)
  | Pop n -> Format.fmt1 "pop %s" (show n)
  | CheckSat -> "check-sat"
  | GetUnsatCore -> "get-unsat-core"
  | EmptyLine -> "; empty line"
  | SetOption (s, v) -> "SetOption " ^ s ^ " " ^ v
  | GetStatistics -> "get-statistics"
  | GetReasonUnknown -> "get-reason-unknown"
