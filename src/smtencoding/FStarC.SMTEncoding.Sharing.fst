module FStarC.SMTEncoding.Sharing

open FStarC
open FStarC.Effect
open FStarC.SMTEncoding.Term
open FStarC.Class.Deq
open FStarC.Class.Hashable

module Pruning = FStarC.SMTEncoding.Pruning
module H = FStarC.Hash
module HT = FStarC.HashTable
module R = FStarC.Range.Ops
module U = FStarC.Util
module Real = FStarC.Real
module Ident = FStarC.Ident

let tag (n:int) : H.hash_code = H.of_int n
let mix (x y:H.hash_code) : H.hash_code = H.mix x y

let rec hash_list (#a:Type) (f:a -> ML H.hash_code) (xs:list a)
  : ML H.hash_code =
  match xs with
  | [] -> tag 0
  | x::xs -> mix (tag 1) (mix (f x) (hash_list f xs))

let hash_option (#a:Type) (f:a -> ML H.hash_code) (x:option a)
  : ML H.hash_code =
  match x with
  | None -> tag 0
  | Some x -> mix (tag 1) (f x)

let equal_list (#a:Type) (f:a -> a -> ML bool) (xs ys:list a)
  : ML bool =
  FStarC.List.forall2 f xs ys

let equal_option (#a:Type) (f:a -> a -> ML bool) (x y:option a)
  : ML bool =
  match x, y with
  | None, None -> true
  | Some x, Some y -> f x y
  | _ -> false

let rec hash_sort (s:sort) : ML H.hash_code =
  match s with
  | Bool_sort -> tag 0
  | Int_sort -> tag 1
  | String_sort -> tag 2
  | Term_sort -> tag 3
  | Fuel_sort -> tag 4
  | BitVec_sort n -> mix (tag 5) (H.of_int n)
  | Array (a, b) -> mix (tag 6) (mix (hash_sort a) (hash_sort b))
  | Arrow (a, b) -> mix (tag 7) (mix (hash_sort a) (hash_sort b))
  | Sort s -> mix (tag 8) (H.of_string s)

let rec equal_sort (x y:sort) : ML bool =
  match x, y with
  | Bool_sort, Bool_sort
  | Int_sort, Int_sort
  | String_sort, String_sort
  | Term_sort, Term_sort
  | Fuel_sort, Fuel_sort -> true
  | BitVec_sort x, BitVec_sort y -> x = y
  | Array (x1, x2), Array (y1, y2)
  | Arrow (x1, x2), Arrow (y1, y2) ->
      equal_sort x1 y1 && equal_sort x2 y2
  | Sort x, Sort y -> x = y
  | _ -> false

(* These discriminants are part of the hash scheme: each constructor has a
   distinct stable tag, while equality still checks every payload. *)
let op_tag (o:op) : int =
  match o with
  | TrueOp -> 0 | FalseOp -> 1 | Not -> 2
  | And -> 3 | Or -> 4 | Imp -> 5 | Iff -> 6
  | Eq -> 7 | LT -> 8 | LTE -> 9 | GT -> 10
  | GTE -> 11 | Add -> 12 | Sub -> 13 | Div -> 14
  | RealDiv -> 15 | Mul -> 16 | Minus -> 17
  | Mod -> 18 | BvAnd -> 19 | BvXor -> 20
  | BvOr -> 21 | BvAdd -> 22 | BvSub -> 23
  | BvShl -> 24 | BvShr -> 25 | BvUdiv -> 26
  | BvMod -> 27 | BvMul -> 28 | BvUlt -> 29
  | BvConcat -> 30 | BvRepeat _ -> 31
  | BvExtRol -> 32 | BvExtRor -> 33
  | BvRol _ -> 34 | BvRor _ -> 35
  | BvUext _ -> 36 | BvSext _ -> 37
  | BvExtract _ -> 38
  | BvNot -> 39 | BvNeg -> 40 | BvNand -> 41
  | BvNor -> 42 | BvXnor -> 43 | BvComp -> 44
  | BvUle -> 45 | BvUgt -> 46 | BvUge -> 47
  | BvSlt -> 48 | BvSle -> 49 | BvSgt -> 50
  | BvSge -> 51 | BvSdiv -> 52 | BvSrem -> 53
  | BvSmod -> 54 | BvAshr -> 55 | BvNego -> 56
  | BvUaddo -> 57 | BvSaddo -> 58 | BvUmulo -> 59
  | BvSmulo -> 60 | BvUsubo -> 61 | BvSsubo -> 62
  | BvSdivo -> 63 | NatToBv _ -> 64
  | BvToNat -> 65 | SBvToInt -> 66 | ITE -> 67
  | Var _ -> 68

let hash_op (o:op) : ML H.hash_code =
  match o with
  | BvRepeat n | BvRol n | BvRor n | BvUext n | BvSext n
  | NatToBv n -> mix (tag (op_tag o)) (H.of_int n)
  | BvExtract (n, m) ->
      mix (tag 38) (mix (H.of_int n) (H.of_int m))
  | Var s -> mix (tag 68) (H.of_string s)
  | _ -> tag (op_tag o)

let equal_op (x y:op) : ML bool =
  match x, y with
  | BvRepeat x, BvRepeat y | BvRol x, BvRol y
  | BvRor x, BvRor y | BvUext x, BvUext y
  | BvSext x, BvSext y | NatToBv x, NatToBv y -> x = y
  | BvExtract (x1, x2), BvExtract (y1, y2) -> x1 = y1 && x2 = y2
  | Var x, Var y -> x = y
  | _ -> op_tag x = op_tag y

let hash_qop (q:qop) : H.hash_code =
  match q with Forall -> tag 0 | Exists -> tag 1

let equal_qop (x y:qop) : bool =
  match x, y with
  | Forall, Forall | Exists, Exists -> true
  | _ -> false

let hash_pos (p:Range.pos) : H.hash_code =
  mix (H.of_int (R.line_of_pos p)) (H.of_int (R.col_of_pos p))

let equal_pos (x y:Range.pos) : ML bool = x =? y

let hash_range (r:Range.t) : H.hash_code =
  let hdef =
    mix (H.of_string (R.file_of_range r))
      (mix (hash_pos (R.start_of_range r)) (hash_pos (R.end_of_range r))) in
  let huse =
    mix (H.of_string (R.file_of_use_range r))
      (mix (hash_pos (R.start_of_use_range r))
           (hash_pos (R.end_of_use_range r))) in
  mix hdef huse

let equal_range (x y:Range.t) : ML bool =
  R.file_of_range x = R.file_of_range y &&
  equal_pos (R.start_of_range x) (R.start_of_range y) &&
  equal_pos (R.end_of_range x) (R.end_of_range y) &&
  R.file_of_use_range x = R.file_of_use_range y &&
  equal_pos (R.start_of_use_range x) (R.start_of_use_range y) &&
  equal_pos (R.end_of_use_range x) (R.end_of_use_range y)

(* [lident] has internal cached fields not exposed by its interface. Treat the
   whole value as opaque so exact interning cannot merge inconsistent caches. *)
let hash_lid (_:Ident.lid) : H.hash_code = tag 0

let equal_lid (x y:Ident.lid) : bool = U.physical_equality x y

let hash_fv (x:fv) : ML H.hash_code =
  let FV name s force = x in
  mix (H.of_string name) (mix (hash_sort s) (hash force))

let equal_fv_exact (x y:fv) : ML bool =
  let FV xn xs xf = x in
  let FV yn ys yf = y in
  xn = yn && equal_sort xs ys && xf = yf

let hash_fact_db_id (x:fact_db_id) : ML H.hash_code =
  match x with
  | Name x -> mix (tag 0) (hash_lid x)
  | Namespace x -> mix (tag 1) (hash_lid x)
  | Tag x -> mix (tag 2) (H.of_string x)

let equal_fact_db_id (x y:fact_db_id) : ML bool =
  match x, y with
  | Name x, Name y | Namespace x, Namespace y -> equal_lid x y
  | Tag x, Tag y -> x = y
  | _ -> false

noeq type hashed_term = {
  ht_hash:H.hash_code;
  ht_term:term
}

let term_hash (x:hashed_term) = x.ht_hash
let term_value (x:hashed_term) = x.ht_term

let physical_term (x y:term) : bool = U.physical_equality x y

let equal_term_node (x y:term) : ML bool =
  match x, y with
  | Integer x, Integer y | String x, String y -> x = y
  | Real x, Real y ->
      Real.mantissa x = Real.mantissa y &&
      Real.exponent x = Real.exponent y
  | BoundV x, BoundV y -> x = y
  | FreeV x, FreeV y -> equal_fv_exact x y
  | App xo xa xr, App yo ya yr ->
      equal_op xo yo &&
      equal_list physical_term xa ya &&
      equal_range xr yr
  | Quant xo xp xw xs xb xr, Quant yo yp yw ys yb yr ->
      equal_qop xo yo &&
      equal_list (equal_list physical_term) xp yp &&
      equal_option (fun x y -> x = y) xw yw &&
      equal_list equal_sort xs ys &&
      physical_term xb yb &&
      equal_range xr yr
  | Let xv xb, Let yv yb ->
      equal_list physical_term xv yv && physical_term xb yb
  | Labeled xb xm xr, Labeled yb ym yr ->
      physical_term xb yb &&
      U.physical_equality xm ym &&
      equal_range xr yr
  | _ -> false

noeq type term_key = {
  tk_hash:H.hash_code;
  tk_term:term
}

instance deq_term_key : deq term_key = {
  (=?) = (fun x y -> x.tk_hash =? y.tk_hash &&
                     equal_term_node x.tk_term y.tk_term);
}

instance hashable_term_key : hashable term_key = {
  hash = (fun x -> x.tk_hash);
}

noeq type term_table = {
  term_find:term_key -> ML (option term);
  term_add:term_key -> term -> ML unit
}

let canonical_term
    (table:term_table) (candidate:term) (h:H.hash_code)
  : ML hashed_term =
  let key = {
    tk_hash = h;
    tk_term = candidate
  } in
  match table.term_find key with
  | Some existing -> { ht_hash = h; ht_term = existing }
  | None ->
      table.term_add key candidate;
      { ht_hash = h; ht_term = candidate }

let rec intern_term (table:term_table) (x:term) : ML hashed_term =
  match x with
  | Integer s -> canonical_term table x (mix (tag 0) (H.of_string s))
  | String s -> canonical_term table x (mix (tag 1) (H.of_string s))
  | Real r ->
      canonical_term table x
        (mix (tag 2)
          (mix (H.of_int (Real.mantissa r)) (H.of_int (Real.exponent r))))
  | BoundV n -> canonical_term table x (mix (tag 3) (H.of_int n))
  | FreeV fv -> canonical_term table x (mix (tag 4) (hash_fv fv))
  | App op args range ->
      let args = List.map (intern_term table) args in
      let rebuilt = App op (List.map term_value args) range in
      canonical_term table rebuilt
        (mix (tag 5)
          (mix (hash_op op)
            (mix (hash_list term_hash args) (hash_range range))))
  | Quant q patterns weight sorts body range ->
      let patterns =
        List.map (fun p -> List.map (intern_term table) p) patterns in
      let body = intern_term table body in
      let rebuilt =
        Quant q
          (List.map (List.map term_value) patterns)
          weight sorts body.ht_term range in
      canonical_term table rebuilt
        (mix (tag 6)
          (mix (hash_qop q)
            (mix (hash_list (hash_list term_hash) patterns)
              (mix (hash_option H.of_int weight)
                (mix (hash_list hash_sort sorts)
                  (mix body.ht_hash (hash_range range)))))))
  | Let values body ->
      let values = List.map (intern_term table) values in
      let body = intern_term table body in
      let rebuilt = Let (List.map term_value values) body.ht_term in
      canonical_term table rebuilt
        (mix (tag 7) (mix (hash_list term_hash values) body.ht_hash))
  | Labeled body message range ->
      let body = intern_term table body in
      let rebuilt = Labeled body.ht_term message range in
      canonical_term table rebuilt
        (mix (tag 8) (mix body.ht_hash (mix (tag 0) (hash_range range))))

noeq type hashed_decl = {
  hd_hash:H.hash_code;
  hd_decl:decl
}

let decl_hash (x:hashed_decl) = x.hd_hash
let decl_value (x:hashed_decl) = x.hd_decl
let physical_decl (x y:decl) : bool = U.physical_equality x y

let equal_assumption (x y:assumption) : ML bool =
  physical_term x.assumption_term y.assumption_term &&
  equal_option (fun x y -> x = y) x.assumption_caption y.assumption_caption &&
  x.assumption_name = y.assumption_name &&
  equal_list equal_fact_db_id x.assumption_fact_ids y.assumption_fact_ids

let equal_decl_node (x y:decl) : ML bool =
  match x, y with
  | DefPrelude, DefPrelude | CheckSat, CheckSat
  | GetStatistics, GetStatistics | GetReasonUnknown, GetReasonUnknown
  | EmptyLine, EmptyLine -> true
  | DeclFun xn xa xr xc, DeclFun yn ya yr yc ->
      xn = yn && equal_list equal_sort xa ya && equal_sort xr yr &&
      equal_option (fun x y -> x = y) xc yc
  | DefineFun xn xa xr xb xc, DefineFun yn ya yr yb yc ->
      xn = yn && equal_list equal_sort xa ya && equal_sort xr yr &&
      physical_term xb yb && equal_option (fun x y -> x = y) xc yc
  | Assume x, Assume y -> equal_assumption x y
  | Caption x, Caption y | Echo x, Echo y -> x = y
  | Module xn xd, Module yn yd ->
      xn = yn && equal_list physical_decl xd yd
  | Eval x, Eval y -> physical_term x y
  | RetainAssumptions x, RetainAssumptions y ->
      equal_list (fun x y -> x = y) x y
  | Push x, Push y | Pop x, Pop y -> x = y
  | SetOption xk xv, SetOption yk yv -> xk = yk && xv = yv
  | _ -> false

noeq type decl_key = {
  dk_hash:H.hash_code;
  dk_decl:decl
}

instance deq_decl_key : deq decl_key = {
  (=?) = (fun x y -> x.dk_hash =? y.dk_hash &&
                     equal_decl_node x.dk_decl y.dk_decl);
}

instance hashable_decl_key : hashable decl_key = {
  hash = (fun x -> x.dk_hash);
}

noeq type decl_table = {
  decl_find:decl_key -> ML (option decl);
  decl_add:decl_key -> decl -> ML unit
}

let canonical_decl
    (table:decl_table) (candidate:decl) (h:H.hash_code)
  : ML hashed_decl =
  let key = {
    dk_hash = h;
    dk_decl = candidate
  } in
  match table.decl_find key with
  | Some existing -> { hd_hash = h; hd_decl = existing }
  | None ->
      table.decl_add key candidate;
      { hd_hash = h; hd_decl = candidate }

let hash_caption (x:caption) : ML H.hash_code =
  hash_option H.of_string x

let rec intern_decl
    (terms:term_table) (decls:decl_table) (x:decl)
  : ML hashed_decl =
  match x with
  | DefPrelude -> canonical_decl decls x (tag 0)
  | DeclFun name args result caption ->
      canonical_decl decls x
        (mix (tag 1)
          (mix (H.of_string name)
            (mix (hash_list hash_sort args)
              (mix (hash_sort result) (hash_caption caption)))))
  | DefineFun name args result body caption ->
      let body = intern_term terms body in
      let rebuilt = DefineFun name args result body.ht_term caption in
      canonical_decl decls rebuilt
        (mix (tag 2)
          (mix (H.of_string name)
            (mix (hash_list hash_sort args)
              (mix (hash_sort result)
                (mix body.ht_hash (hash_caption caption))))))
  | Assume a ->
      let body = intern_term terms a.assumption_term in
      let rebuilt =
        Assume { a with assumption_term = body.ht_term } in
      canonical_decl decls rebuilt
        (mix (tag 3)
          (mix body.ht_hash
            (mix (hash_caption a.assumption_caption)
              (mix (H.of_string a.assumption_name)
                   (hash_list hash_fact_db_id a.assumption_fact_ids)))))
  | Caption s -> canonical_decl decls x (mix (tag 4) (H.of_string s))
  | Module name children ->
      let children = List.map (intern_decl terms decls) children in
      let rebuilt = Module name (List.map decl_value children) in
      canonical_decl decls rebuilt
        (mix (tag 5)
          (mix (H.of_string name) (hash_list decl_hash children)))
  | Eval t ->
      let t = intern_term terms t in
      canonical_decl decls (Eval t.ht_term) (mix (tag 6) t.ht_hash)
  | Echo s -> canonical_decl decls x (mix (tag 7) (H.of_string s))
  | RetainAssumptions names ->
      canonical_decl decls x
        (mix (tag 8) (hash_list H.of_string names))
  | Push n -> canonical_decl decls x (mix (tag 9) (H.of_int n))
  | Pop n -> canonical_decl decls x (mix (tag 10) (H.of_int n))
  | CheckSat -> canonical_decl decls x (tag 11)
  | SetOption key value ->
      canonical_decl decls x
        (mix (tag 12) (mix (H.of_string key) (H.of_string value)))
  | GetStatistics -> canonical_decl decls x (tag 13)
  | GetReasonUnknown -> canonical_decl decls x (tag 14)
  | EmptyLine -> canonical_decl decls x (tag 15)

noeq type elt_key = {
  ek_hash:H.hash_code;
  ek_elt:decls_elt
}

let equal_elt (x y:decls_elt) : ML bool =
  equal_option (fun x y -> x = y) x.sym_name y.sym_name &&
  equal_option (fun x y -> x = y) x.key y.key &&
  equal_list physical_decl x.decls y.decls &&
  equal_list (fun x y -> x = y) x.a_names y.a_names

instance deq_elt_key : deq elt_key = {
  (=?) = (fun x y -> x.ek_hash =? y.ek_hash && equal_elt x.ek_elt y.ek_elt);
}

instance hashable_elt_key : hashable elt_key = {
  hash = (fun x -> x.ek_hash);
}

noeq type elt_table = {
  elt_find:elt_key -> ML (option decls_elt);
  elt_add:elt_key -> decls_elt -> ML unit
}

let intern_elt
    (terms:term_table)
    (decls:decl_table)
    (elts:elt_table)
    (x:decls_elt)
  : ML decls_elt =
  let children = List.map (intern_decl terms decls) x.decls in
  let rebuilt = { x with decls = List.map decl_value children } in
  let h =
    mix (hash_option H.of_string x.sym_name)
      (mix (hash_option H.of_string x.key)
        (mix (hash_list decl_hash children)
             (hash_list H.of_string x.a_names))) in
  let key = {
    ek_hash = h;
    ek_elt = rebuilt
  } in
  match elts.elt_find key with
  | Some existing -> existing
  | None -> elts.elt_add key rebuilt; rebuilt

let intern_decls (declarations:decls_t) : ML decls_t =
  let count = List.length declarations in
  let elt_size = if count = 0 then 1 else count in
  let decl_size = if count = 0 then 1 else 2 * count in
  let term_size = if count = 0 then 1 else 4 * count in
  let elt_entries = HT.create elt_size in
  let decl_entries = HT.create decl_size in
  let term_entries = HT.create term_size in
  let elts = {
    elt_find = (fun key -> HT.try_find elt_entries key);
    elt_add = (fun key value -> HT.add elt_entries key value)
  } in
  let decls = {
    decl_find = (fun key -> HT.try_find decl_entries key);
    decl_add = (fun key value -> HT.add decl_entries key value)
  } in
  let terms = {
    term_find = (fun key -> HT.try_find term_entries key);
    term_add = (fun key value -> HT.add term_entries key value)
  } in
  List.map (intern_elt terms decls elts) declarations

let hash_asum_kind (x:Pruning.asum_kind) : ML H.hash_code =
  match x with
  | Pruning.Sum_triggers triggers ->
      mix (tag 0) (hash_list (hash_list H.of_string) triggers)
  | Pruning.Sum_ambient root -> mix (tag 1) (hash root)
  | Pruning.Sum_drop -> tag 2

let equal_asum_kind (x y:Pruning.asum_kind) : ML bool =
  match x, y with
  | Pruning.Sum_triggers x, Pruning.Sum_triggers y ->
      equal_list (equal_list (fun x y -> x = y)) x y
  | Pruning.Sum_ambient x, Pruning.Sum_ambient y -> x = y
  | Pruning.Sum_drop, Pruning.Sum_drop -> true
  | _ -> false

let hash_assumption_summary (x:Pruning.assumption_summary) : ML H.hash_code =
  mix (H.of_string x.Pruning.asum_name)
    (mix (hash_list H.of_string x.Pruning.asum_free_names)
      (mix (hash x.Pruning.asum_pretyping)
           (hash_asum_kind x.Pruning.asum_kind)))

let equal_assumption_summary
    (x y:Pruning.assumption_summary) : ML bool =
  x.Pruning.asum_name = y.Pruning.asum_name &&
  equal_list (fun x y -> x = y)
    x.Pruning.asum_free_names y.Pruning.asum_free_names &&
  x.Pruning.asum_pretyping = y.Pruning.asum_pretyping &&
  equal_asum_kind x.Pruning.asum_kind y.Pruning.asum_kind

noeq type hashed_summary = {
  hs_hash:H.hash_code;
  hs_summary:Pruning.decl_summary
}

let summary_hash (x:hashed_summary) = x.hs_hash
let summary_value (x:hashed_summary) = x.hs_summary
let physical_summary (x y:Pruning.decl_summary) : bool =
  U.physical_equality x y

let equal_summary (x y:Pruning.decl_summary) : ML bool =
  match x, y with
  | Pruning.Sum_assume x, Pruning.Sum_assume y ->
      equal_assumption_summary x y
  | Pruning.Sum_declfun x, Pruning.Sum_declfun y -> x = y
  | Pruning.Sum_definefun (xn, xf), Pruning.Sum_definefun (yn, yf) ->
      xn = yn && equal_list (fun x y -> x = y) xf yf
  | Pruning.Sum_retain x, Pruning.Sum_retain y ->
      equal_list (fun x y -> x = y) x y
  | Pruning.Sum_ignored, Pruning.Sum_ignored -> true
  | Pruning.Sum_other x, Pruning.Sum_other y -> physical_decl x y
  | _ -> false

noeq type summary_key = {
  sk_hash:H.hash_code;
  sk_summary:Pruning.decl_summary
}

instance deq_summary_key : deq summary_key = {
  (=?) = (fun x y -> x.sk_hash =? y.sk_hash &&
                     equal_summary x.sk_summary y.sk_summary);
}

instance hashable_summary_key : hashable summary_key = {
  hash = (fun x -> x.sk_hash);
}

noeq type summary_table = {
  summary_find:summary_key -> ML (option Pruning.decl_summary);
  summary_add:summary_key -> Pruning.decl_summary -> ML unit
}

let intern_summary
    (terms:term_table)
    (decls:decl_table)
    (summaries:summary_table)
    (x:Pruning.decl_summary)
  : ML hashed_summary =
  let rebuilt, h =
    match x with
    | Pruning.Sum_assume a ->
        x, mix (tag 0) (hash_assumption_summary a)
    | Pruning.Sum_declfun name ->
        x, mix (tag 1) (H.of_string name)
    | Pruning.Sum_definefun (name, free) ->
        x, mix (tag 2)
             (mix (H.of_string name) (hash_list H.of_string free))
    | Pruning.Sum_retain names ->
        x, mix (tag 3) (hash_list H.of_string names)
    | Pruning.Sum_ignored -> x, tag 4
    | Pruning.Sum_other d ->
        let d = intern_decl terms decls d in
        Pruning.Sum_other d.hd_decl, mix (tag 5) d.hd_hash in
  let key = {
    sk_hash = h;
    sk_summary = rebuilt
  } in
  match summaries.summary_find key with
  | Some existing -> { hs_hash = h; hs_summary = existing }
  | None ->
      summaries.summary_add key rebuilt;
      { hs_hash = h; hs_summary = rebuilt }

noeq type summary_elt_key = {
  sek_hash:H.hash_code;
  sek_elt:Pruning.elt_summary
}

let equal_summary_elt (x y:Pruning.elt_summary) : ML bool =
  equal_option (fun x y -> x = y) x.Pruning.elts_key y.Pruning.elts_key &&
  equal_list (fun x y -> x = y)
    x.Pruning.elts_a_names y.Pruning.elts_a_names &&
  equal_list physical_summary x.Pruning.elts_sums y.Pruning.elts_sums

instance deq_summary_elt_key : deq summary_elt_key = {
  (=?) = (fun x y -> x.sek_hash =? y.sek_hash &&
                     equal_summary_elt x.sek_elt y.sek_elt);
}

instance hashable_summary_elt_key : hashable summary_elt_key = {
  hash = (fun x -> x.sek_hash);
}

noeq type summary_elt_table = {
  summary_elt_find:summary_elt_key -> ML (option Pruning.elt_summary);
  summary_elt_add:summary_elt_key -> Pruning.elt_summary -> ML unit
}

let intern_summary_elt
    (terms:term_table)
    (decls:decl_table)
    (summaries:summary_table)
    (elts:summary_elt_table)
    (x:Pruning.elt_summary)
  : ML Pruning.elt_summary =
  let children =
    List.map (intern_summary terms decls summaries) x.Pruning.elts_sums in
  let rebuilt =
    { x with Pruning.elts_sums = List.map summary_value children } in
  let h =
    mix (hash_option H.of_string x.Pruning.elts_key)
      (mix (hash_list H.of_string x.Pruning.elts_a_names)
           (hash_list summary_hash children)) in
  let key = {
    sek_hash = h;
    sek_elt = rebuilt
  } in
  match elts.summary_elt_find key with
  | Some existing -> existing
  | None -> elts.summary_elt_add key rebuilt; rebuilt

let intern_index (index:list Pruning.elt_summary)
  : ML (list Pruning.elt_summary) =
  let count = List.length index in
  let size = if count = 0 then 1 else count in
  let term_size = 4 * size in
  let decl_size = 2 * size in
  let summary_size = 2 * size in
  let term_entries = HT.create term_size in
  let decl_entries = HT.create decl_size in
  let summary_entries = HT.create summary_size in
  let summary_elt_entries = HT.create size in
  let terms = {
    term_find = (fun key -> HT.try_find term_entries key);
    term_add = (fun key value -> HT.add term_entries key value)
  } in
  let decls = {
    decl_find = (fun key -> HT.try_find decl_entries key);
    decl_add = (fun key value -> HT.add decl_entries key value)
  } in
  let summaries = {
    summary_find = (fun key -> HT.try_find summary_entries key);
    summary_add = (fun key value -> HT.add summary_entries key value)
  } in
  let elts = {
    summary_elt_find = (fun key -> HT.try_find summary_elt_entries key);
    summary_elt_add =
      (fun key value -> HT.add summary_elt_entries key value)
  } in
  List.map (intern_summary_elt terms decls summaries elts) index
