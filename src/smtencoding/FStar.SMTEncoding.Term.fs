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
#light "off"

module FStar.SMTEncoding.Term
open FStar.ST
open FStar.Exn
open FStar.All

open FStar
open FStar.Syntax.Syntax
open FStar.Syntax
open FStar.Util
module BU = FStar.Util
module U = FStar.Syntax.Util

let escape (s:string) = BU.replace_char s '\'' '_'

type sort =
  | Bool_sort
  | Int_sort
  | String_sort
  | Term_sort
  | Fuel_sort
  | BitVec_sort of int // BitVectors parameterized by their size
  | Array of sort * sort
  | Arrow of sort * sort
  | Sort of string

let rec strSort x = match x with
  | Bool_sort  -> "Bool"
  | Int_sort  -> "Int"
  | Term_sort -> "Term"
  | String_sort -> "FString"
  | Fuel_sort -> "Fuel"
  | BitVec_sort n -> format1 "(_ BitVec %s)" (string_of_int n)
  | Array(s1, s2) -> format2 "(Array %s %s)" (strSort s1) (strSort s2)
  | Arrow(s1, s2) -> format2 "(%s -> %s)" (strSort s1) (strSort s2)
  | Sort s -> s

type op =
  | TrueOp
  | FalseOp
  | Not
  | And
  | Or
  | Imp
  | Iff
  | Eq
  | LT
  | LTE
  | GT
  | GTE
  | Add
  | Sub
  | Div
  | Mul
  | Minus
  | Mod
  | BvAnd
  | BvXor
  | BvOr
  | BvAdd
  | BvSub
  | BvShl
  | BvShr  // unsigned shift right\
  | BvUdiv
  | BvMod
  | BvMul
  | BvUlt
  | BvUext of Prims.int
  | NatToBv of Prims.int // need to explicitly define the size of the bitvector
  | BvToNat
  | ITE
  | Var of string //Op corresponding to a user/encoding-defined uninterpreted function

type qop =
  | Forall
  | Exists

(*
    forall (x:Term). {:pattern HasType x Int}
            HasType x int ==> P


*)
//de Bruijn representation of terms in locally nameless style
type term' =
  | Integer    of string //unbounded mathematical integers
  | Real       of string //real numbers
  | BoundV     of int
  | FreeV      of fv
  | App        of op  * list<term> //ops are always fully applied; we're in a first-order theory
  | Quant      of qop
                  * list<list<pat>>  //disjunction of conjunctive patterns
                  * option<int>      //an optional weight; seldom used
                  * list<sort>       //sorts of each bound variable
                  * term             //body
  | Let        of list<term> // bound terms
                * term       // body
  | Labeled    of term * string * Range.range
  | LblPos     of term * string
and pat  = term
and term = {tm:term'; freevars:Syntax.memo<fvs>; rng:Range.range}
and fv = string * sort * bool
//The bool in the fc signals if this occurrence
//is a thunk that should be forced.
//See note [Thunking Nullary Constants] below]
and fvs = list<fv>


(** Note [Thunking Nullary Constants]

### The problem: Top-level nullary constants lead to SMT context
    pollution

Given a top-level nullary constant, say,

```let n : u32 = 0ul```

F* would encode this to SMT as (roughly)

```
(declare-fun n () Term)
(assert (HasType n u32))
(assert (n = U32.uint_to_to 0))
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

type caption = option<string>
type binders = list<(string * sort)>
type constructor_field = string  //name of the field
                       * sort    //sort of the field
                       * bool    //true if the field is projectible
type constructor_t = (string * list<constructor_field> * sort * int * bool)
type constructors  = list<constructor_t>
type fact_db_id =
    | Name of Ident.lid
    | Namespace of Ident.lid
    | Tag of string
type assumption = {
    assumption_term: term;
    assumption_caption: caption;
    assumption_name: string;
    assumption_fact_ids:list<fact_db_id>
}
type decl =
  | DefPrelude
  | DeclFun    of string * list<sort> * sort * caption
  | DefineFun  of string * list<sort> * sort * term * caption
  | Assume     of assumption
  | Caption    of string
  | Module     of string * list<decl>
  | Eval       of term
  | Echo       of string
  | RetainAssumptions of list<string>
  | Push
  | Pop
  | CheckSat
  | GetUnsatCore
  | SetOption  of string * string
  | GetStatistics
  | GetReasonUnknown
type decls_t = list<decl>

type error_label = (fv * string * Range.range)
type error_labels = list<error_label>

let mk_fv (x, y) : fv = x, y, false
let fv_name (x:fv) = let nm, _, _ = x in nm
let fv_sort (x:fv) = let _, sort, _ = x in sort
let fv_force (x:fv) = let _, _, force = x in force
let fv_eq (x:fv) (y:fv) = fv_name x = fv_name y
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
  | Real _
  | BoundV _ -> []
  | FreeV fv -> [fv]
  | App(_, tms) -> List.collect freevars tms
  | Quant(_, _, _, _, t)
  | Labeled(t, _, _)
  | LblPos(t, _) -> freevars t
  | Let (es, body) -> List.collect freevars (body::es)

//memo-ized
let free_variables t = match !t.freevars with
  | Some b -> b
  | None ->
    let fvs = BU.remove_dups fv_eq (freevars t) in
    t.freevars := Some fvs;
    fvs

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
  | BvUext n -> format1 "(_ zero_extend %s)" (string_of_int n)
  | NatToBv n -> format1 "(_ int2bv %s)" (string_of_int n)
  | Var s -> s

let weightToSmt = function
  | None -> ""
  | Some i -> BU.format1 ":weight %s\n" (string_of_int i)

let rec hash_of_term' t = match t with
  | Integer i ->  i
  | Real r -> r
  | BoundV i  -> "@"^string_of_int i
  | FreeV x   -> fv_name x ^ ":" ^ strSort (fv_sort x) //Question: Why is the sort part of the hash?
  | App(op, tms) -> "("^(op_to_string op)^(List.map hash_of_term tms |> String.concat " ")^")"
  | Labeled(t, r1, r2) -> hash_of_term t ^ r1 ^ (Range.string_of_range r2)
  | LblPos(t, r) -> "(! " ^hash_of_term t^ " :lblpos " ^r^ ")"
  | Quant(qop, pats, wopt, sorts, body) ->
      "("
    ^ (qop_to_string qop)
    ^ " ("
    ^ (List.map strSort sorts |> String.concat " ")
    ^ ")(! "
    ^ (hash_of_term body)
    ^ " "
    ^ (weightToSmt wopt)
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
let boxBitVecFun sz  = mkBoxFunctions ("BoxBitVec" ^ (string_of_int sz))
let boxRealFun       = mkBoxFunctions "BoxReal"

// Assume the Box/Unbox functions to be injective
let isInjective s =
    if (FStar.String.length s >= 3) then
        String.substring s 0 3 = "Box" &&
        not (List.existsML (fun c -> c = '.') (FStar.String.list_of_string s))
    else false

let mk t r = {tm=t; freevars=BU.mk_ref None; rng=r}
let mkTrue  r       = mk (App(TrueOp, [])) r
let mkFalse r       = mk (App(FalseOp, [])) r
let mkInteger i  r  = mk (Integer (ensure_decimal i)) r
let mkInteger' i r  = mkInteger (string_of_int i) r
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


let check_pattern_ok (t:term) : option<term> =
    let rec aux t =
        match t.tm with
        | Integer _
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
        | Quant _
        | LblPos _ -> Some t
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
  | Integer n               -> BU.format1 "(Integer %s)" n
  | Real r                  -> BU.format1 "(Real %s)" r
  | BoundV  n               -> BU.format1 "(BoundV %s)" (BU.string_of_int n)
  | FreeV  fv               -> BU.format1 "(FreeV %s)" (fv_name fv)
  | App (op, l)             -> BU.format2 "(%s %s)" (op_to_string op) (print_smt_term_list l)
  | Labeled(t, r1, r2)      -> BU.format2 "(Labeled '%s' %s)" r1 (print_smt_term t)
  | LblPos(t, s)            -> BU.format2 "(LblPos %s %s)" s (print_smt_term t)
  | Quant (qop, l, _, _, t) -> BU.format3 "(%s %s %s)" (qop_to_string qop) (print_smt_term_list_list l) (print_smt_term t)
  | Let (es, body) -> BU.format2 "(let %s %s)" (print_smt_term_list es) (print_smt_term body)

and print_smt_term_list (l:list<term>) :string = List.map print_smt_term l |> String.concat " "

and print_smt_term_list_list (l:list<list<term>>) :string =
    List.fold_left (fun s l -> (s ^ "; [ " ^ (print_smt_term_list l) ^ " ] ")) "" l

let mkQuant r check_pats (qop, pats, wopt, vars, body) =
    let all_pats_ok pats =
        if not check_pats then pats else
        match BU.find_map pats (fun x -> BU.find_map x check_pattern_ok) with
        | None -> pats
        | Some p ->
          begin
            Errors.log_issue
                    r
                    (Errors.Warning_SMTPatternMissingBoundVar,
                     BU.format1 "Pattern (%s) contains illegal symbols; dropping it" (print_smt_term p));
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
        | Real _
        | BoundV _ -> t
        | FreeV x ->
          begin match index_of x with
            | None -> t
            | Some i -> mkBoundV (i + ix) t.rng
          end
        | App(op, tms) -> mkApp'(op, List.map (aux ix) tms) t.rng
        | Labeled(t, r1, r2) -> mk (Labeled(aux ix t, r1, r2)) t.rng
        | LblPos(t, r) -> mk (LblPos(aux ix t, r)) t.rng
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
    | Real _
    | FreeV _ -> t
    | BoundV i ->
      if 0 <= i - shift && i - shift < n
      then List.nth tms (i - shift)
      else t
    | App(op, tms) -> mkApp'(op, List.map (aux shift) tms) t.rng
    | Labeled(t, r1, r2) -> mk (Labeled(aux shift t, r1, r2)) t.rng
    | LblPos(t, r) -> mk (LblPos(aux shift t, r)) t.rng
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
let constr_id_of_sort sort = format1 "%s_constr_id" (strSort sort)
let fresh_token (tok_name, sort) id =
    let a_name = "fresh_token_" ^tok_name in
    let a = {assumption_name=escape a_name;
             assumption_caption=Some "fresh token";
             assumption_term=mkEq(mkInteger' id norng,
                                  mkApp(constr_id_of_sort sort,
                                        [mkApp (tok_name,[]) norng]) norng) norng;
             assumption_fact_ids=[]} in
    Assume a

let fresh_constructor rng (name, arg_sorts, sort, id) =
  let id = string_of_int id in
  let bvars = arg_sorts |> List.mapi (fun i s -> mkFreeV(mk_fv ("x_" ^ string_of_int i, s)) norng) in
  let bvar_names = List.map fv_of_term bvars in
  let capp = mkApp(name, bvars) norng in
  let cid_app = mkApp(constr_id_of_sort sort, [capp]) norng in
  let a_name = "constructor_distinct_" ^name in
  let a = {
    assumption_name=escape a_name;
    assumption_caption=Some "Constructor distinct";
    assumption_term=mkForall rng ([[capp]], bvar_names, mkEq(mkInteger id norng, cid_app) norng);
    assumption_fact_ids=[]
  } in
  Assume a

let injective_constructor rng (name, fields, sort) =
    let n_bvars = List.length fields in
    let bvar_name i = "x_" ^ string_of_int i in
    let bvar_index i = n_bvars - (i + 1) in
    let bvar i s = mkFreeV <| mk_fv (bvar_name i, s) in
    let bvars = fields |> List.mapi (fun i (_, s, _) -> bvar i s norng) in
    let bvar_names = List.map fv_of_term bvars in
    let capp = mkApp(name, bvars) norng in
    fields
    |> List.mapi (fun i (name, s, projectible) ->
            let cproj_app = mkApp(name, [capp]) norng in
            let proj_name = DeclFun(name, [sort], s, Some "Projector") in
            if projectible
            then let a = {
                    assumption_name = escape ("projection_inverse_"^name);
                    assumption_caption = Some "Projection inverse";
                    assumption_term = mkForall rng ([[capp]], bvar_names, mkEq(cproj_app, bvar i s norng) norng);
                    assumption_fact_ids = []
                 } in
                 [proj_name; Assume a]
            else [proj_name])
    |> List.flatten

let constructor_to_decl rng (name, fields, sort, id, injective) =
    let injective = injective || true in
    let field_sorts = fields |> List.map (fun (_, sort, _) -> sort) in
    let cdecl = DeclFun(name, field_sorts, sort, Some "Constructor") in
    let cid = fresh_constructor rng (name, field_sorts, sort, id) in
    let disc =
        let disc_name = "is-"^name in
        let xfv = mk_fv ("x", sort) in
        let xx = mkFreeV xfv norng in
        let disc_eq = mkEq(mkApp(constr_id_of_sort sort, [xx]) norng, mkInteger (string_of_int id) norng) norng in
        let proj_terms, ex_vars =
            fields
         |> List.mapi (fun i (proj, s, projectible) ->
                if projectible
                then mkApp(proj, [xx]) norng, []
                else let fi = mk_fv ("f_" ^ BU.string_of_int i, s) in
                     mkFreeV fi norng, [fi])
         |> List.split in
        let ex_vars = List.flatten ex_vars in
        let disc_inv_body = mkEq(xx, mkApp(name, proj_terms) norng) norng in
        let disc_inv_body = match ex_vars with
            | [] -> disc_inv_body
            | _ -> mkExists norng ([], ex_vars, disc_inv_body) in
        let disc_ax = mkAnd(disc_eq, disc_inv_body) norng in
        let def = mkDefineFun(disc_name, [xfv], Bool_sort,
                    disc_ax,
                    Some "Discriminator definition") in
        def in
    let projs =
        if injective
        then injective_constructor rng (name, fields, sort)
        else [] in
    Caption (format1 "<start constructor %s>" name)::cdecl::cid::projs@[disc]@[Caption (format1 "</end constructor %s>" name)]

(****************************************************************************)
(* Standard SMTLib prelude for F* and some term constructors                *)
(****************************************************************************)
let name_binders_inner prefix_opt (outer_names:list<fv>) start sorts =
    let names, binders, n = sorts |> List.fold_left (fun (names, binders, n) s ->
        let prefix = match s with
            | Term_sort -> "@x"
            | _ -> "@u" in
        let prefix =
            match prefix_opt with
            | None -> prefix
            | Some p -> p ^ prefix in
        let nm = prefix ^ string_of_int n in
        let names = mk_fv (nm,s)::names in
        let b = BU.format2 "(%s %s)" nm (strSort s) in
        names, b::binders, n+1)
        (outer_names, [], start)  in
    names, List.rev binders, n

let name_macro_binders sorts =
    let names, binders, n = name_binders_inner (Some "__") [] 0 sorts in
    List.rev names, binders

let termToSmt
  : print_ranges:bool -> enclosing_name:string -> t:term -> string
  =
  fun print_ranges enclosing_name t ->
      let next_qid =
          let ctr = BU.mk_ref 0 in
          fun depth ->
            let n = !ctr in
            BU.incr ctr;
            if n = 0 then enclosing_name
            else BU.format2 "%s.%s" enclosing_name (BU.string_of_int n)
      in
      let remove_guard_free pats =
        pats |> List.map (fun ps ->
          ps |> List.map (fun tm ->
            match tm.tm with
            | App(Var "Prims.guard_free", [{tm=BoundV _}]) -> tm
            | App(Var "Prims.guard_free", [p]) -> p
            | _ -> tm))
      in
      let rec aux' depth n (names:list<fv>) t =
        let aux = aux (depth + 1) in
        match t.tm with
        | Integer i -> i
        | Real r -> r
        | BoundV i ->
          List.nth names i |> fv_name
        | FreeV x when fv_force x -> "(" ^ fv_name x ^ " Dummy_value)" //force a thunked name
        | FreeV x -> fv_name x
        | App(op, []) -> op_to_string op
        | App(op, tms) -> BU.format2 "(%s %s)" (op_to_string op) (List.map (aux n names) tms |> String.concat "\n")
        | Labeled(t, _, _) -> aux n names t
        | LblPos(t, s) -> BU.format2 "(! %s :lblpos %s)" (aux n names t) s
        | Quant(qop, pats, wopt, sorts, body) ->
          let qid = next_qid () in
          let names, binders, n = name_binders_inner None names n sorts in
          let binders = binders |> String.concat " " in
          let pats = remove_guard_free pats in
          let pats_str =
            match pats with
            | [[]]
            | [] -> ";;no pats"
            | _ ->
              pats
              |> List.map (fun pats ->
                format1 "\n:pattern (%s)" (String.concat " " (List.map (fun p ->
                  format1 "%s" (aux n names p)) pats)))
              |> String.concat "\n"
          in
          BU.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                    [qop_to_string qop;
                     binders;
                     aux n names body;
                     weightToSmt wopt;
                     pats_str;
                     qid]

        | Let (es, body) ->
          (* binders are reversed but according to the smt2 standard *)
          (* substitution should occur in parallel and order should not matter *)
          let names, binders, n =
            List.fold_left (fun (names0, binders, n0) e ->
              let nm = "@lb" ^ string_of_int n0 in
              let names0 = mk_fv (nm, Term_sort)::names0 in
              let b = BU.format2 "(%s %s)" nm (aux n names e) in
              names0, b::binders, n0+1)
            (names, [], n)
            es
          in
          BU.format2 "(let (%s)\n%s)"
                     (String.concat " " binders)
                     (aux n names body)

      and aux depth n names t =
        let s = aux' depth n names t in
        if print_ranges && t.rng <> norng
        then BU.format3 "\n;; def=%s; use=%s\n%s\n" (Range.string_of_range t.rng) (Range.string_of_use_range t.rng) s
        else s
      in
      aux 0 0 [] t

let caption_to_string print_captions =
    function
    | Some c
       when print_captions ->
        let c = String.split ['\n'] c |> List.map BU.trim_string |> String.concat " " in
        ";;;;;;;;;;;;;;;;" ^ c ^ "\n"
    | _ -> ""


let rec declToSmt' print_captions z3options decl =
  match decl with
  | DefPrelude ->
    mkPrelude z3options
  | Module (s, decls) ->
    let res = List.map (declToSmt' print_captions z3options) decls |> String.concat "\n" in
    if Options.keep_query_captions()
    then BU.format5 "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                    s
                    res
                    s
                    (BU.string_of_int (List.length decls))
                    (BU.string_of_int (String.length res))
    else res
  | Caption c ->
    if print_captions
    then "\n" ^ (BU.splitlines c |> List.map (fun s -> "; " ^ s ^ "\n") |> String.concat "")
    else ""
  | DeclFun(f,argsorts,retsort,c) ->
    let l = List.map strSort argsorts in
    format4 "%s(declare-fun %s (%s) %s)"
      (caption_to_string print_captions c)
      f
      (String.concat " " l)
      (strSort retsort)
  | DefineFun(f,arg_sorts,retsort,body,c) ->
    let names, binders = name_macro_binders arg_sorts in
    let body = inst (List.map (fun x -> mkFreeV x norng) names) body in
    format5 "%s(define-fun %s (%s) %s\n %s)"
      (caption_to_string print_captions c)
      f
      (String.concat " " binders)
      (strSort retsort)
      (termToSmt print_captions (escape f) body)
  | Assume a ->
    let fact_ids_to_string ids =
        ids |> List.map (function
        | Name n -> "Name " ^Ident.text_of_lid n
        | Namespace ns -> "Namespace " ^Ident.text_of_lid ns
        | Tag t -> "Tag " ^t)
    in
    let fids =
        if print_captions
        then BU.format1 ";;; Fact-ids: %s\n"
                        (String.concat "; " (fact_ids_to_string a.assumption_fact_ids))
        else "" in
    let n = a.assumption_name in
    format4 "%s%s(assert (! %s\n:named %s))"
            (caption_to_string print_captions a.assumption_caption)
            fids
            (termToSmt print_captions n a.assumption_term)
            n
  | Eval t ->
    format1 "(eval %s)" (termToSmt print_captions "eval" t)
  | Echo s ->
    format1 "(echo \"%s\")" s
  | RetainAssumptions _ ->
    ""
  | CheckSat -> "(echo \"<result>\")\n(check-sat)\n(echo \"</result>\")"
  | GetUnsatCore -> "(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
  | Push -> "(push)"
  | Pop -> "(pop)"
  | SetOption (s, v) -> format2 "(set-option :%s %s)" s v
  | GetStatistics -> "(echo \"<statistics>\")\n(get-info :all-statistics)\n(echo \"</statistics>\")"
  | GetReasonUnknown-> "(echo \"<reason-unknown>\")\n(get-info :reason-unknown)\n(echo \"</reason-unknown>\")"

and declToSmt         z3options decl = declToSmt' (Options.keep_query_captions())  z3options decl
and declToSmt_no_caps z3options decl = declToSmt' false z3options decl
and declsToSmt        z3options decls = List.map (declToSmt z3options) decls |> String.concat "\n"

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
                ;;fuel irrelevance\n\
                (assert (forall ((f Fuel) (x Term) (t Term))\n\
                                (! (= (HasTypeFuel (SFuel f) x t)\n\
                                          (HasTypeZ x t))\n\
                                   :pattern ((HasTypeFuel (SFuel f) x t)))))\n\
                (declare-fun NoHoist (Term Bool) Bool)\n\
                ;;no-hoist\n\
                (assert (forall ((dummy Term) (b Bool))\n\
                                (! (= (NoHoist dummy b)\n\
                                          b)\n\
                                   :pattern ((NoHoist dummy b)))))\n\
                (define-fun  IsTyped ((x Term)) Bool\n\
                    (exists ((t Term)) (HasTypeZ x t)))\n\
                (declare-fun ApplyTF (Term Fuel) Term)\n\
                (declare-fun ApplyTT (Term Term) Term)\n\
                (declare-fun Rank (Term) Int)\n\
                (declare-fun Closure (Term) Term)\n\
                (declare-fun ConsTerm (Term Term) Term)\n\
                (declare-fun ConsFuel (Fuel Term) Term)\n\
                (declare-fun Tm_uvar (Int) Term)\n\
                (define-fun Reify ((x Term)) Term x)\n\
                (assert (forall ((t Term))\n\
                            (! (iff (exists ((e Term)) (HasType e t))\n\
                                    (Valid t))\n\
                                :pattern ((Valid t)))))\n\
                (declare-fun Prims.precedes (Term Term Term Term) Term)\n\
                (declare-fun Range_const (Int) Term)\n\
                (declare-fun _mul (Int Int) Int)\n\
                (declare-fun _div (Int Int) Int)\n\
                (declare-fun _mod (Int Int) Int)\n\
                (declare-fun __uu__PartialApp () Term)\n\
                (assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n\
                (assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n\
                (assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))"
   in
   let constrs : constructors = [("FString_const", ["FString_const_proj_0", Int_sort, true], String_sort, 0, true);
                                 ("Tm_type",  [], Term_sort, 2, true);
                                 ("Tm_arrow", [("Tm_arrow_id", Int_sort, true)],  Term_sort, 3, false);
                                 ("Tm_unit",  [], Term_sort, 6, true);
                                 (fst boxIntFun,     [snd boxIntFun,  Int_sort, true],   Term_sort, 7, true);
                                 (fst boxBoolFun,    [snd boxBoolFun, Bool_sort, true],  Term_sort, 8, true);
                                 (fst boxStringFun,  [snd boxStringFun, String_sort, true], Term_sort, 9, true);
                                 (fst boxRealFun,    [snd boxRealFun, Sort "Real", true], Term_sort, 10, true);
                                 ("LexCons",    [("LexCons_0", Term_sort, true); ("LexCons_1", Term_sort, true); ("LexCons_2", Term_sort, true)], Term_sort, 11, true)] in
   let bcons = constrs |> List.collect (constructor_to_decl norng) |> List.map (declToSmt z3options) |> String.concat "\n" in
   let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n\
                                   (is-LexCons t))\n\
                       (declare-fun Prims.lex_t () Term)\n\
                       (assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n\
                                    (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n\
                                         (or (Valid (Prims.precedes t1 t2 x1 y1))\n\
                                             (and (= x1 y1)\n\
                                                  (Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n\
                      (assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n\
                                                          (! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n\
                                                                  (Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n\
                                                          :pattern (Prims.precedes t1 t2 e1 e2))))\n\
                      (assert (forall ((t1 Term) (t2 Term))\n\
                                      (! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n\
                                      (< (Rank t1) (Rank t2)))\n\
                                      :pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n" in

   basic ^ bcons ^ lex_ordering


(* Generate boxing/unboxing functions for bitvectors of various sizes. *)
(* For ids, to avoid dealing with generation of fresh ids,
   I am computing them based on the size in this not very robust way.
   z3options are only used by the prelude so passing the empty string should be ok. *)
let mkBvConstructor (sz : int) =
    (fst (boxBitVecFun sz),
        [snd (boxBitVecFun sz), BitVec_sort sz, true], Term_sort, 12+sz, true)
    |> constructor_to_decl norng

let __range_c = BU.mk_ref 0
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
  | _ -> raise Impos
let unboxTerm sort t = match sort with
  | Int_sort -> unboxInt t
  | Bool_sort -> unboxBool t
  | String_sort -> unboxString t
  | BitVec_sort sz -> unboxBitVec sz t
  | Sort "Real" -> unboxReal t
  | _ -> raise Impos

let getBoxedInteger (t:term) =
  match t.tm with
  | App(Var s, [t2]) when s = fst boxIntFun ->
    begin
    match t2.tm with
    | Integer n -> Some (int_of_string n)
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
            when (FStar.Util.is_some (getBoxedInteger t0))->
        // sometimes b2t gets needlessly normalized...
        let sz = match getBoxedInteger t0 with | Some sz -> sz | _ -> failwith "impossible" in
        mkBvUlt (unboxBitVec sz t1, unboxBitVec sz t2) t.rng
    | App(Var "Prims.b2t", [t1]) -> {unboxBool t1 with rng=t.rng}
    | _ ->
        mkApp("Valid",  [t]) t.rng
let mk_HasType v t    = mkApp("HasType", [v;t]) t.rng
let mk_HasTypeZ v t   = mkApp("HasTypeZ", [v;t]) t.rng
let mk_IsTyped v      = mkApp("IsTyped", [v]) norng
let mk_HasTypeFuel f v t =
   if Options.unthrottle_inductives()
   then mk_HasType v t
   else mkApp("HasTypeFuel", [f;v;t]) t.rng
let mk_HasTypeWithFuel f v t = match f with
    | None -> mk_HasType v t
    | Some f -> mk_HasTypeFuel f v t
let mk_NoHoist dummy b = mkApp("NoHoist", [dummy;b]) b.rng
let mk_Destruct v     = mkApp("Destruct", [v])
let mk_Rank x         = mkApp("Rank", [x])
let mk_tester n t     = mkApp("is-"^n,   [t]) t.rng
let mk_ApplyTF t t'   = mkApp("ApplyTF", [t;t']) t.rng
let mk_ApplyTT t t'  r  = mkApp("ApplyTT", [t;t']) r
let kick_partial_app t  = mk_ApplyTT (mkApp("__uu__PartialApp", []) t.rng) t t.rng |> mk_Valid
let mk_String_const i r = mkApp("FString_const", [ mkInteger' i norng]) r
let mk_Precedes x1 x2 x3 x4 r = mkApp("Prims.precedes", [x1;x2;x3;x4])  r|> mk_Valid
let mk_LexCons x1 x2 x3 r  = mkApp("LexCons", [x1;x2;x3]) r
let rec n_fuel n =
    if n = 0 then mkApp("ZFuel", []) norng
    else mkApp("SFuel", [n_fuel (n - 1)]) norng
let fuel_2 = n_fuel 2
let fuel_100 = n_fuel 100

let mk_and_opt p1 p2 r = match p1, p2  with
  | Some p1, Some p2 -> Some (mkAnd(p1, p2) r)
  | Some p, None
  | None, Some p -> Some p
  | None, None -> None

let mk_and_opt_l pl r =
  List.fold_right (fun p out -> mk_and_opt p out r) pl None

let mk_and_l l r = List.fold_right (fun p1 p2 -> mkAnd(p1, p2) r) l (mkTrue r)

let mk_or_l l r = List.fold_right (fun p1 p2 -> mkOr(p1,p2) r) l (mkFalse r)

let mk_haseq t = mk_Valid (mkApp ("Prims.hasEq", [t]) t.rng)
let dummy_sort = Sort "Dummy_sort"
