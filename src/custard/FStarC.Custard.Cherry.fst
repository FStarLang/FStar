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
module FStarC.Custard.Cherry

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Custard.Syntax
open FStarC.Errors.Msg

module HashTable = FStarC.HashTable
module E = FStarC.Errors
module Options = FStarC.Options

(* -------------------------------------------------------------------- *)
(* Which types are reference counted                                    *)
(* -------------------------------------------------------------------- *)

let type_table (p:program) : ML (HashTable.t string dtype) =
  let t = HashTable.create 50 in
  p |> List.iter (fun d ->
    match d with
    | DType dt -> HashTable.add t (string_of_name dt.dt_name) dt
    | _ -> ());
  t

let field_types (b:tydef) : ML (list cty) =
  match b with
  | TAbbrev c -> [c]
  | TRecord fs -> List.map snd fs
  | TVariant cs -> List.collect (fun (_, fs) -> List.map snd fs) cs
  | TAbstract -> []

(* What stands for every function type in the tables below: a function value
   is a counted closure, whatever its type. *)
let arrow_key : string = "->"

(* And every exception: a counted cell (cherry.md, "Exceptions"). *)
let exn_key : string = "Prims.exn"

(* And every ML reference, [TRef (RGc, _)], and every [TAny], the
   representation of [FStar.Dyn.dyn]: the runtime's counted cells, which no
   type name can spell. *)
let ref_key : string = "<ref>"
let any_key : string = "<any>"

(* An immutable array, [FStar.ImmutableArray.Base.t] (cherry.md, "Arrays"). *)
let iarray_key : string = "FStar.ImmutableArray.Base.t"
let is_iarray_name (n:name) : bool =
  n.ns = ["FStar"; "ImmutableArray"; "Base"] && n.id = "t"

(* The type names a value of [t] holds by value.  A pointer is a size, and
   what it reaches is not part of the value. *)
let rec by_value (t:cty) : ML (list string) =
  match t with
  | TRef (RGc, _) -> [ref_key]
  | TAny -> [any_key]
  | TApp (n, _) when is_iarray_name n -> [iarray_key]
  | TApp (n, args) -> string_of_name n :: List.collect by_value args
  | TTuple ts -> List.collect by_value ts
  | TArrow _ -> [arrow_key]
  | TExn -> [exn_key]
  | _ -> []

(* Does a value of [t] contain a value of [target], through any number of
   by-value fields?
   Each type is visited once: a type with two fields of a third, recursive,
   one would otherwise be explored along every path through it. *)
let reaches (tbl:HashTable.t string dtype) (target:string) (t:cty) : ML bool =
  let seen : HashTable.t string bool = HashTable.create 20 in
  let rec go (t:cty) : ML bool =
    by_value t |> List.existsb (fun n ->
      n = target ||
      (if HashTable.mem seen n then false else begin
         HashTable.add seen n true;
         match HashTable.try_find tbl n with
         | Some d -> field_types d.dt_body |> List.existsb go
         | None -> false
       end)) in
  go t

let boxed_types (p:program) : ML (list string) =
  let tbl = type_table p in
  p |> List.collect (fun d ->
    match d with
    | DType dt when (TVariant? dt.dt_body || TRecord? dt.dt_body) ->
      let k = string_of_name dt.dt_name in
      if has_flag dt.dt_flags CherryBoxed ||
         field_types dt.dt_body |> List.existsb (reaches tbl k) then [k] else []
    | _ -> [])

(* The types the runtime (ulib/c/cherry.h) represents as counted cells. *)
let runtime_types : list string = ["Prims.int"; "Prims.string"; iarray_key]

(* The operands a [Dyn] operation takes owned: the value [mk] wraps. *)
let dyn_owns (f:string) : list bool = if f = "mk" then [true] else []

(* The operands an immutable array operation (Syntax.IArr) takes owned: the
   array an update or a push changes in place when it can, and the value it
   stores. *)
let iarr_owns (f:string) : list bool =
  match f with
  | "upd" -> [true; false; true]
  | "push" -> [true; true]
  | _ -> []

(* The operands a Pulse container operation (Syntax.PBuf) takes owned: the
   value stored. *)
let pbuf_owns (f:string) : list bool =
  match f with
  | "alloc" -> [true; false]
  | "init" -> [false; true; false]
  | "write" -> [false; false; true]
  | _ -> []

(* An ML reference (Builtins.ml_ref_ty). *)
let is_ml_ref (t:cty) : bool =
  match t with
  | TRef (RGc, _) -> true
  | _ -> false

let nonplain_types (p:program) : ML (list string) =
  let tbl = type_table p in
  let np : HashTable.t string bool = HashTable.create 50 in
  runtime_types |> List.iter (fun k -> HashTable.add np k true);
  HashTable.add np ref_key true;
  HashTable.add np any_key true;
  HashTable.add np arrow_key true;
  HashTable.add np exn_key true;
  boxed_types p |> List.iter (fun k -> HashTable.add np k true);
  let rec settle (fuel:int) : ML unit =
    let changed = mk_ref false in
    p |> List.iter (fun d ->
      match d with
      | DType dt ->
        let k = string_of_name dt.dt_name in
        if not (HashTable.mem np k) &&
           (field_types dt.dt_body |> List.existsb (fun t ->
              by_value t |> List.existsb (HashTable.mem np)))
        then (HashTable.add np k true; changed := true)
      | _ -> ());
    if !changed && fuel > 0 then settle (fuel - 1) in
  settle 1000;
  ignore tbl;
  HashTable.keys np

(* -------------------------------------------------------------------- *)
(* State of one run                                                     *)
(* -------------------------------------------------------------------- *)

let np_tbl : ref (HashTable.t string bool) = mk_ref (HashTable.create 0)
let boxed_tbl : ref (HashTable.t string bool) = mk_ref (HashTable.create 0)
let ctor_tbl : ref (HashTable.t string (list (string & cty))) = mk_ref (HashTable.create 0)
let record_tbl : ref (HashTable.t string (list (string & cty))) = mk_ref (HashTable.create 0)
(* For each external, which of its arguments it takes ownership of. *)
let extern_tbl : ref (HashTable.t string (list bool)) = mk_ref (HashTable.create 0)
(* The functions this program defines: their parameters and result. *)
let fn_tbl : ref (HashTable.t string (list binder & cty)) = mk_ref (HashTable.create 0)
(* The program's globals: definitions without parameters. *)
let global_tbl : ref (HashTable.t string bool) = mk_ref (HashTable.create 0)
(* How many arguments each external takes. *)
let extern_arity : ref (HashTable.t string (int & option cty)) = mk_ref (HashTable.create 0)
let current : ref string = mk_ref ""
let counter : ref int = mk_ref 0

let unsupported (#a:Type) (what:string) : ML a =
  E.raise_error0 E.Error_CustardNoCRepresentation [
    text ("Cherry: " ^ what ^ " is not supported yet, in " ^ !current ^ ".");
    text "The Cherry backend is a prototype (see cherry.md)."]

let rec is_np (t:cty) : ML bool =
  match t with
  | TApp (n, _) -> HashTable.mem !np_tbl (string_of_name n)
  | TTuple ts -> List.existsb is_np ts
  | TArrow _ | TExn | TRef (RGc, _) | TAny -> true
  | _ -> false

(* A Pulse reference or array of counted values (Syntax.PBuf). *)
let is_pbuf (t:cty) : ML bool =
  match t with
  | TRef (RManual, u) | TBuf u -> is_np u
  | _ -> false

(* The definitions that may return with an exception pending. *)
let raise_tbl : ref (HashTable.t string bool) = mk_ref (HashTable.create 0)

(* A partial application of a definition: it builds a closure and runs
   nothing, so raises nothing whatever the definition does.  (An
   over-application has been split by then, see [lift].) *)
let is_pap (node:expr) : ML bool =
  match node.e with
  | EApp ({ e = EQual (f, _) }, args) ->
    (match HashTable.try_find !fn_tbl (string_of_name f) with
     | Some (bs, _) -> List.length args < List.length bs
     | None -> false)
  | _ -> false

(* May this node, once its operands are atoms, return with an exception
   pending?  A closure call may if it has an effect: its target is unknown.
   So is a call through a global, which holds a closure: its initializer
   raising nothing says nothing about the closure. *)
let may_raise (node:expr) : ML bool =
  match node.e with
  | EApp _ when is_pap node -> false
  | EApp ({ e = EQual (f, _) }, _)
    when not (HashTable.mem !global_tbl (string_of_name f)) ->
    HashTable.mem !raise_tbl (string_of_name f)
  | EApp _ -> not (is_pure node.eff)
  | _ -> false

(* Does evaluating [e] involve a non-plain value anywhere, or an exception?
   The function a direct call names is not a value. *)
let rec touches (e:expr) : ML bool =
  is_np e.ty || is_pbuf e.ty ||
  (match e.e with
   | ELet (_, t, _, _) when is_np t -> true
   | ERaise _ | ETry _ -> true
   | EApp ({ e = EQual _ }, args) -> may_raise e || List.existsb touches args
   | _ -> exists_child touches e)

let fresh () : ML string =
  counter := !counter + 1;
  "cherry_tmp" ^ string_of_int !counter

(* -------------------------------------------------------------------- *)
(* Free variables, precisely: shadowing decides who owns a reference.   *)
(* -------------------------------------------------------------------- *)

let rec pat_vars (p:pat) : ML (list string) =
  match p with
  | PWild | PConst _ -> []
  | PVar x -> [x]
  | PCtor (_, ps) | PTuple ps -> List.collect pat_vars ps
  | PRecord (_, fs) -> List.collect (fun (_, q) -> pat_vars q) fs
  | POr (q :: _) -> pat_vars q
  | POr [] -> []

let without (xs:list string) (ys:list string) : ML (list string) =
  List.filter (fun y -> not (List.mem y xs)) ys

let rec fv (e:expr) : ML (list string) =
  match e.e with
  | EVar x -> [x]
  | ELet (x, _, a, b) -> fv a @ without [x] (fv b)
  | EFun (bs, b) -> without (List.map (fun b -> b.b_name) bs) (fv b)
  | EMatch (s, brs) | ETry (s, brs) -> fv s @ List.collect fv_branch brs
  | _ -> List.collect fv (children e)

and fv_branch (br:branch) : ML (list string) =
  let p, g, b = br in
  without (pat_vars p) ((match g with Some g -> fv g | None -> []) @ fv b)

(* The typed variables a pattern binds against a scrutinee of type [t]. *)
let rec pat_binds (p:pat) (t:cty) : ML (list (string & cty)) =
  match p with
  | PWild | PConst _ -> []
  | PVar x -> [(x, t)]
  | PCtor (cn, ps) ->
    (match HashTable.try_find !ctor_tbl (string_of_name cn) with
     | Some fs ->
       List.zip (List.map snd fs) ps
       |> List.collect (fun (ft, q) -> pat_binds q ft)
     | None -> unsupported ("the constructor " ^ string_of_name cn))
  | PRecord (tn, fps) ->
    (match HashTable.try_find !record_tbl (string_of_name tn) with
     | Some fs ->
       fps |> List.collect (fun (f, q) ->
         match List.tryFind (fun (g, _) -> g = f) fs with
         | Some (_, ft) -> pat_binds q ft
         | None -> unsupported ("the field " ^ f))
     | None -> unsupported ("the record " ^ string_of_name tn))
  | PTuple _ -> unsupported "a tuple pattern"
  | POr _ -> unsupported "a pattern disjunction"

(* The typed variables a pattern binds, as far as they can be told; used
   only to type what a lambda captures. *)
let rec pat_binds_opt (p:pat) (t:cty) : ML (list (string & cty)) =
  match p, t with
  | PVar x, _ -> [(x, t)]
  | PCtor (cn, ps), _ ->
    (match HashTable.try_find !ctor_tbl (string_of_name cn) with
     | Some fs when List.length fs = List.length ps ->
       List.zip (List.map snd fs) ps |> List.collect (fun (ft, q) -> pat_binds_opt q ft)
     | _ -> [])
  | PRecord (tn, fps), _ ->
    (match HashTable.try_find !record_tbl (string_of_name tn) with
     | Some fs ->
       fps |> List.collect (fun (f, q) ->
         match List.tryFind (fun (g, _) -> g = f) fs with
         | Some (_, ft) -> pat_binds_opt q ft
         | None -> [])
     | None -> [])
  | PTuple ps, TTuple ts when List.length ps = List.length ts ->
    List.zip ps ts |> List.collect (fun (q, t) -> pat_binds_opt q t)
  | POr (q :: _), _ -> pat_binds_opt q t
  | _ -> []

(* -------------------------------------------------------------------- *)
(* Closures: every lambda becomes a definition of its own               *)
(* -------------------------------------------------------------------- *)

(* A lambda becomes a top-level function taking what it captures and then
   its own parameters, and the lambda itself the partial application of that
   function to the captured variables -- which is a closure.  A call given
   more arguments than the function it names takes becomes a call of the
   function's result.  So afterwards a function value is only ever a
   function's name, a partial application, or a variable. *)

let lifted : ref (list decl) = mk_ref []
let lift_parent : ref (option dlet) = mk_ref None

let rec dedup (xs:list string) : ML (list string) =
  match xs with
  | [] -> []
  | x :: rest -> x :: dedup (List.filter (fun y -> y <> x) rest)

let rec arrow_split (n:int) (t:cty) : ML (list cty & cty) =
  if n <= 0 then ([], t) else
  match t with
  | TArrow (a, _, b) -> let ts, r = arrow_split (n - 1) b in (a :: ts, r)
  | _ -> unsupported "an external whose type has fewer arguments than its arity"

let rec arrows (ts:list cty) (r:cty) : ML cty =
  match ts with
  | [] -> r
  | t :: ts -> TArrow (t, E_Pure, arrows ts r)

let new_fn (bs:list binder) (body:expr) : ML name =
  let parent = Some?.v !lift_parent in
  counter := !counter + 1;
  let n = { parent.dl_name with id = parent.dl_name.id ^ "__clo" ^ string_of_int !counter } in
  let flags = Private :: (parent.dl_flags |> List.filter Imported?) in
  let l = { dl_name = n; dl_typars = []; dl_binders = bs; dl_ret = body.ty;
            dl_eff = body.eff; dl_body = body; dl_flags = flags } in
  lifted := DLet l :: !lifted;
  HashTable.add !fn_tbl (string_of_name n) (bs, body.ty);
  n

(* An external has no closure of its own, so one used as a value, or given
   fewer arguments than it takes, is wrapped in a definition calling it. *)
let eta_extern (hd:expr) : ML (option expr) =
  match hd.e with
  | EQual (f, _) ->
    (match HashTable.try_find !extern_arity (string_of_name f) with
     | Some (n, dty) when n > 0 ->
       (* The node's own type, which is instantiated, when it is the whole
          arrow; otherwise the declared one, if that is monomorphic. *)
       let rec count (t:cty) : ML int = match t with TArrow (_, _, b) -> 1 + count b | _ -> 0 in
       let t = if count hd.ty >= n then hd.ty
               else match dty with
                    | Some t -> t
                    | None -> unsupported "a polymorphic external used as a value" in
       let doms, r = arrow_split n t in
       let hd = { hd with ty = t } in
       let bs = doms |> List.mapi (fun i t -> { b_name = "cherry_x" ^ string_of_int i; b_ty = t }) in
       let body = mk (EApp (hd, bs |> List.map (fun b -> mk (EVar b.b_name) b.b_ty E_Pure)))
                     r E_Impure in
       Some (mk (EQual (new_fn bs body, [])) t E_Pure)
     | _ -> None)
  | _ -> None

let rec lift (env:list (string & cty)) (e:expr) : ML expr =
  match e.e with
  | EQual _ when TArrow? e.ty ->
    (match eta_extern e with Some e' -> e' | None -> e)
  | ELet (x, t, a, b) ->
    { e with e = ELet (x, t, lift env a, lift ((x, t) :: env) b) }
  | EMatch (s, brs) ->
    { e with e = EMatch (lift env s, List.map (lift_branch env s.ty) brs) }
  (* The body of a [try] becomes a function of its own (cherry.md,
     "Exceptions"): an exception raised in it leaves that function, and the
     [try] is a call followed by a test. *)
  | ETry (s, brs) ->
    let s = lift env s in
    (* A body that only raises has whatever type it is used at, which a
       handler may know better than the [try]. *)
    let t = (s.ty :: e.ty :: List.map (fun (_, _, b) -> b.ty) brs)
            |> List.tryFind (fun t -> not (TAny? t)) in
    let t = (match t with Some t -> t | None -> e.ty) in
    let e = { e with ty = t } in
    let s = { s with ty = t } in
    let caps = dedup (fv s) |> List.map (fun x ->
                 match List.assoc x env with
                 | Some t -> { b_name = x; b_ty = t }
                 | None -> unsupported ("a try capturing " ^ x ^ ", whose type is unknown")) in
    let caps, args =
      if Nil? caps then [{ b_name = "cherry_unit"; b_ty = TUnit }], [unit_expr]
      else caps, List.map (fun b -> mk (EVar b.b_name) b.b_ty E_Pure) caps in
    let n = new_fn caps s in
    let hd = mk (EQual (n, [])) (arrows (List.map (fun b -> b.b_ty) caps) s.ty) E_Pure in
    { e with e = ETry (mk (EApp (hd, args)) s.ty E_Impure,
                       List.map (lift_branch env TExn) brs) }
  | EFun (bs, body) ->
    let body = lift (List.map (fun b -> (b.b_name, b.b_ty)) bs @ env) body in
    let caps = dedup (without (List.map (fun b -> b.b_name) bs) (fv body))
      |> List.map (fun x ->
           match List.assoc x env with
           | Some t -> { b_name = x; b_ty = t }
           | None -> unsupported ("a lambda capturing " ^ x ^ ", whose type is unknown")) in
    let n = new_fn (caps @ bs) body in
    if Nil? caps then mk (EQual (n, [])) e.ty E_Pure
    else
      let hd = mk (EQual (n, [])) (arrows (List.map (fun b -> b.b_ty) caps) e.ty) E_Pure in
      mk (EApp (hd, List.map (fun b -> mk (EVar b.b_name) b.b_ty E_Pure) caps)) e.ty E_Impure
  | EApp (hd, args) ->
    let args = List.map (lift env) args in
    let hd =
      match hd.e with
      | EQual (f, _) ->
        (match HashTable.try_find !extern_arity (string_of_name f) with
         | Some (n, _) when List.length args < n -> Some?.v (eta_extern hd)
         | _ -> hd)
      | _ -> lift env hd in
    (match hd.e with
     | EQual (f, _) ->
       (match HashTable.try_find !fn_tbl (string_of_name f) with
        | Some (bs, r) when List.length args > List.length bs ->
          let first, rest = List.splitAt (List.length bs) args in
          let inner = mk (EApp (hd, first)) r E_Impure in
          { e with e = EApp (inner, rest) }
        | _ -> { e with e = EApp (hd, args) })
     | _ -> { e with e = EApp (hd, args) })
  | _ -> map_children (lift env) e

and lift_branch (env:list (string & cty)) (st:cty) (br:branch) : ML branch =
  let p, g, b = br in
  let env = pat_binds_opt p st @ env in
  (p, (match g with Some g -> Some (lift env g) | None -> None), lift env b)

(* -------------------------------------------------------------------- *)
(* Coercions through any                                                *)
(* -------------------------------------------------------------------- *)

(* Where the ML extraction writes [Obj.magic], Custard leaves an [ECoerce].
   Under Cherry a [TAny] is a [dyn] (cherry.md, "The any type"), so a value
   enters one by [mkdyn] and leaves by [undyn], and a function is wrapped in
   one that converts its arguments and result.  Runs before lambda lifting,
   which turns the wrapper into a closure. *)
let rec mentions_any (t:cty) : ML bool =
  match t with
  | TAny -> true
  | TArrow (a, _, b) -> mentions_any a || mentions_any b
  | TApp (_, ts) | TTuple ts -> List.existsb mentions_any ts
  | TBuf c | TRef (_, c) | TInline c -> mentions_any c
  | _ -> false

let rec mentions_tvar (t:cty) : ML bool =
  match t with
  | TVar _ -> true
  | TArrow (a, _, b) -> mentions_tvar a || mentions_tvar b
  | TApp (_, ts) | TTuple ts -> List.existsb mentions_tvar ts
  | TBuf c | TRef (_, c) | TInline c -> mentions_tvar c
  | _ -> false

let co_counter : ref int = mk_ref 0
let co_fresh () : ML string =
  co_counter := !co_counter + 1;
  "cherry_co" ^ string_of_int !co_counter

let rec arrow_parts (t:cty) : list (cty & eff) & cty =
  match t with
  | TArrow (a, f, b) -> let (xs, r) = arrow_parts b in ((a, f) :: xs, r)
  | _ -> ([], t)

let uniform_arrow (t:cty) : ML cty =
  let ps, _ = arrow_parts t in
  List.fold_right (fun ((_:cty), (ef:eff)) r -> TArrow (TAny, ef, r)) ps TAny

(* A definition used as a value is a closure of its signature's type,
   whatever it was typed at. *)
let at_signature (a:expr) : ML expr =
  match a.e with
  | EQual (n, _) ->
    (match HashTable.try_find !fn_tbl (string_of_name n) with
     | Some (bs, r) ->
       { a with ty = List.fold_right (fun (b:binder) r -> TArrow (b.b_ty, E_Impure, r)) bs r }
     | None -> a)
  | _ -> a

let rec coerce_any (a:expr) (t:cty) : ML expr =
  let a = at_signature a in
  if a.ty = t then a else
  match a.e with
  | EOp ({ po_op = Dyn "mk" }, [x]) when x.ty = t -> x
  | _ ->
  match a.ty, t with
  (* A closure goes into any at its uniform type, every parameter and the
     result any, so that what takes it out knows what it holds. *)
  | TArrow _, TAny ->
    let u = uniform_arrow a.ty in
    let a = if a.ty = u then a else coerce_any a u in
    mk (EOp ({ po_op = Dyn "mk"; po_ty = None }, [a])) TAny a.eff
  | TAny, TArrow _ ->
    let u = uniform_arrow t in
    coerce_any (mk (EOp ({ po_op = Dyn "get"; po_ty = None }, [a])) u a.eff) t
  | s, TAny when not (mentions_any s) ->
    mk (EOp ({ po_op = Dyn "mk"; po_ty = None }, [a])) TAny a.eff
  | TAny, s when not (mentions_any s) ->
    mk (EOp ({ po_op = Dyn "get"; po_ty = None }, [a])) s a.eff
  | TArrow _, TArrow _ ->
    let (ss, sr) = arrow_parts a.ty in
    let (ts, tr) = arrow_parts t in
    if List.length ss < List.length ts then begin
      (* The source returns, after fewer arguments, what takes the rest. *)
      let f = co_fresh () in
      let fv = mk (EVar f) a.ty E_Pure in
      let bs = ts |> List.map (fun (ty, _) -> { b_name = co_fresh (); b_ty = ty }) in
      let first, rest = List.splitAt (List.length ss) bs in
      let args = List.map2 (fun (b:binder) ((s:cty), _) ->
                   coerce_any (mk (EVar b.b_name) b.b_ty E_Pure) s) first ss in
      let rest_ty = List.fold_right (fun ((x:cty), (ef:eff)) r -> TArrow (x, ef, r))
                      (snd (List.splitAt (List.length ss) ts)) tr in
      let g = coerce_any (mk (EApp (fv, args)) sr E_Impure) rest_ty in
      let call = mk (EApp (g, List.map (fun (b:binder) -> mk (EVar b.b_name) b.b_ty E_Pure) rest)) tr E_Impure in
      let lam = mk (EFun (bs, call)) t E_Pure in
      mk (ELet (f, a.ty, a, lam)) t a.eff
    end else
    if List.length ss > List.length ts then begin
      (* The source takes more arguments than the target: what the target
         returns after its own is a closure over the rest -- a curried
         constructor such as [Mktuple2] mapped into a monad, say, whose result
         type is an arrow that the dictionary passed at run time sees as any. *)
      let f = co_fresh () in
      let fv = mk (EVar f) a.ty E_Pure in
      let n = List.length ts in
      let ss1, ss2 = List.splitAt n ss in
      let bs1 = ts |> List.map (fun (ty, _) -> { b_name = co_fresh (); b_ty = ty }) in
      let bs2 = ss2 |> List.map (fun (ty, _) -> { b_name = co_fresh (); b_ty = ty }) in
      let args1 = List.map2 (fun (b:binder) ((s:cty), _) ->
                    coerce_any (mk (EVar b.b_name) b.b_ty E_Pure) s) bs1 ss1 in
      let args2 = bs2 |> List.map (fun (b:binder) -> mk (EVar b.b_name) b.b_ty E_Pure) in
      let rest_ty = List.fold_right (fun ((x:cty), (ef:eff)) r -> TArrow (x, ef, r)) ss2 sr in
      let inner = mk (EFun (bs2, mk (EApp (fv, args1 @ args2)) sr E_Impure)) rest_ty E_Pure in
      let lam = mk (EFun (bs1, coerce_any inner tr)) t E_Pure in
      mk (ELet (f, a.ty, a, lam)) t a.eff
    end else
    if List.length ss <> List.length ts then mk (ECoerce (a, t)) t a.eff else
    let f = co_fresh () in
    let fv = mk (EVar f) a.ty E_Pure in
    let bs = ts |> List.map (fun (ty, _) -> { b_name = co_fresh (); b_ty = ty }) in
    let args = List.map2 (fun (b:binder) ((s:cty), _) ->
                 coerce_any (mk (EVar b.b_name) b.b_ty E_Pure) s) bs ss in
    let call = mk (EApp (fv, args)) sr E_Impure in
    let lam = mk (EFun (bs, coerce_any call tr)) t E_Pure in
    mk (ELet (f, a.ty, a, lam)) t a.eff
  | _ -> mk (ECoerce (a, t)) t a.eff

(* A pattern variable's uses are typed at what the branch reads it as; one
   bound from a field of type any is retyped any, so that its coercion out of
   any is not mistaken for a no-op.  Conversely a use typed any of one bound
   from a concrete field is that variable put into any: a pattern variable of
   a generated projector has no sort, so extraction types it any, while the
   pattern binds it at the field's type. *)
let rec retype_vars (env:list (string & cty)) (e:expr) : ML expr =
  match e.e with
  | EVar x ->
    (match List.tryFind (fun (y, _) -> y = x) env with
     | Some (_, t) when mentions_any t -> { e with ty = t }
     | Some (_, t) when e.ty = TAny -> mk (ECoerce ({ e with ty = t }, TAny)) TAny e.eff
     | _ -> e)
  (* A binder shadows. *)
  | ELet (x, t, a, b) ->
    let env' = List.filter (fun (y, _) -> y <> x) env in
    { e with e = ELet (x, t, retype_vars env a, retype_vars env' b) }
  | EFun (bs, b) ->
    let env' = List.filter (fun (y, _) -> not (List.existsb (fun (c:binder) -> c.b_name = y) bs)) env in
    { e with e = EFun (bs, retype_vars env' b) }
  | EMatch (sc, brs) ->
    let sub (br:branch) : ML branch =
      let p, g, b = br in
      let vs = pat_vars p in
      let env' = List.filter (fun (y, _) -> not (List.mem y vs)) env in
      (p, (match g with Some g -> Some (retype_vars env' g) | None -> None), retype_vars env' b) in
    { e with e = EMatch (retype_vars env sc, List.map sub brs) }
  | _ -> map_children (retype_vars env) e

let retype_branch (st:cty) (br:branch) : ML branch =
  let p, g, b = br in
  let env = pat_binds_opt p st in
  if Nil? env then br
  else (p, (match g with Some g -> Some (retype_vars env g) | None -> None), retype_vars env b)

let rec lower_any (e:expr) : ML expr =
  let e = match e.e with
          | EMatch (sc, brs) -> { e with e = EMatch (sc, List.map (retype_branch sc.ty) brs) }
          | _ -> e in
  let e = map_children lower_any e in
  match e.e with
  | ECoerce (a, t) when a.ty <> t && (mentions_any a.ty || mentions_any t) ->
    coerce_any a t
  (* An application is typed by its head's arrow; where extraction typed it
     otherwise, through any, it is coerced back. *)
  | EApp (hd, args) ->
    let rec peel (n:int) (t:cty) : option cty =
      if n = 0 then Some t else
      match t with
      | TArrow (_, _, b) -> peel (n - 1) b
      | _ -> None in
    (* The head may have been coerced below, to the arrow extraction typed
       this call at: its parameters are then what the arguments must be.  A
       definition's are its signature's, whatever its name was typed at (a
       partial application's name may be typed at what remains). *)
    let ps, _ = arrow_parts (at_signature hd).ty in
    let args =
      if List.length ps < List.length args then args
      else List.map2 (fun (a:expr) ((p:cty), _) ->
             if a.ty <> p && (mentions_any a.ty || mentions_any p) && not (mentions_tvar p)
             then coerce_any a p else a) args (fst (List.splitAt (List.length args) ps)) in
    let e = { e with e = EApp (hd, args) } in
    (match peel (List.length args) hd.ty with
     | None -> e
     | Some r ->
       if r = e.ty then e
       else if mentions_any r then coerce_any { e with ty = r } e.ty
       (* Typed any where the head says what it is: what it is, for the
          consumer to coerce if it wants any. *)
       else if e.ty = TAny then { e with ty = r }
       else e)
  (* A match typed any whose every arm puts a value of one concrete type into
     any puts the match into any instead, once: what takes it out again at
     that type then cancels against it. *)
  | EMatch (sc, brs) when e.ty = TAny && Some? (common_mk brs) ->
    let t = Some?.v (common_mk brs) in
    let unmk (b:expr) : expr =
      match b.e with
      | EOp ({ po_op = Dyn "mk" }, [x]) -> x
      | _ -> { b with ty = t } in
    let m = { e with e = EMatch (sc, List.map (fun (p, g, b) -> (p, g, unmk b)) brs); ty = t } in
    mk (EOp ({ po_op = Dyn "mk"; po_ty = None }, [m])) TAny e.eff
  (* Arms typed otherwise than the conditional they belong to, through any,
     are coerced to it: when the conditional is typed through any, or when
     an arm is -- a nested conditional typed any under one that is not. *)
  | EIf (c, a, b) when mentions_any e.ty || mentions_any a.ty || mentions_any b.ty ->
    { e with e = EIf (c, arm_to e.ty a, arm_to e.ty b) }
  | EMatch (sc, brs)
    when mentions_any e.ty || List.existsb (fun (_, _, (b:expr)) -> mentions_any b.ty) brs ->
    { e with e = EMatch (sc, List.map (fun (p, g, b) -> (p, g, arm_to e.ty b)) brs) }
  | _ -> e

(* The concrete type every arm puts into any, when they all do (an arm that
   does not return does not count). *)
and common_mk (brs:list branch) : option cty =
  let rec go (acc:option cty) (brs:list branch) : option cty =
    match brs with
    | [] -> acc
    | (_, _, b) :: rest ->
      match b.e with
      | EAbort _ | EUnreachable _ | ERaise _ -> go acc rest
      | EOp ({ po_op = Dyn "mk" }, [x]) when not (mentions_any x.ty) ->
        (match acc with
         | None -> go (Some x.ty) rest
         | Some t -> if t = x.ty then go acc rest else None)
      | _ -> None in
  go None brs

and arm_to (t:cty) (a:expr) : ML expr =
  match a.e with
  | EAbort _ | EUnreachable _ | ERaise _ -> a
  | _ ->
    if a.ty <> t && (t = TAny || a.ty = TAny || (TArrow? t && TArrow? a.ty))
    then coerce_any a t else a

(* A guarded branch becomes an unguarded one.  The branches after it are
   reached both when the pattern does not match and when the guard fails, so
   the guard is tested on its own first, and those branches appear once
   (copying them into both places would double the size per guard):
   [match x with pre | p when g -> b | rest] is
   [match x with pre | _ -> if (match x with p -> g | _ -> false)
                             then (match x with p -> b) else (match x with rest)].
   The earlier branches [pre] have no guard and come first, so they keep
   their priority; [x] is a variable, so matching it again is cheap.

   A [try]'s handlers are a match on the exception, which the reference
   counting pass only builds later, so a guarded handler is made a match here:
   [try s with brs] is [try s with x -> (match x with brs | _ -> raise x)],
   whose guards are then removed as above. *)
let has_guard (brs:list branch) : ML bool = List.existsb (fun (_, g, _) -> Some? g) brs

let rec unguard (e:expr) : ML expr = unguard_node (map_children unguard e)

and unguard_node (e:expr) : ML expr =
  match e.e with
  | ETry (s, brs) when has_guard brs ->
    let x = co_fresh () in
    let xv = mk (EVar x) TExn E_Pure in
    let again = mk (ERaise xv) e.ty E_Impure in
    let h = unguard_node (mk (EMatch (xv, brs @ [(PWild, None, again)])) e.ty E_Impure) in
    { e with e = ETry (s, [(PVar x, None, h)]) }
  | EMatch (sc, brs) when has_guard brs ->
    let rec go (scv:expr) (brs:list branch) : ML expr =
      let rec split (pre:list branch) (brs:list branch) =
        match brs with
        | [] -> None
        | (p, Some g, b) :: rest -> Some (List.rev pre, p, g, b, rest)
        | br :: rest -> split (br :: pre) rest in
      match split [] brs with
      | None ->
        if Nil? brs then mk (EAbort "match failure") e.ty E_Impure
        else mk (EMatch (scv, brs)) e.ty e.eff
      | Some (pre, p, g, b, rest) ->
        let after = go scv rest in
        let irrefutable = (match p with PVar _ | PWild -> true | _ -> false) in
        let test =
          if irrefutable then mk (EMatch (scv, [(p, None, g)])) g.ty g.eff
          else mk (EMatch (scv, [(p, None, g);
                                 (PWild, None, mk (EConst (CBool false)) g.ty E_Pure)])) g.ty g.eff in
        let hit =
          if irrefutable then mk (EMatch (scv, [(p, None, b)])) e.ty b.eff
          else mk (EMatch (scv, [(p, None, b);
                                 (PWild, None, mk (EUnreachable "guard") e.ty E_Pure)])) e.ty b.eff in
        let k = mk (EIf (test, hit, after)) e.ty e.eff in
        if Nil? pre then k
        else mk (EMatch (scv, pre @ [(PWild, None, k)])) e.ty e.eff in
    (match sc.e with
     | EVar _ -> go sc brs
     | _ ->
       let x = co_fresh () in
       mk (ELet (x, sc.ty, sc, go (mk (EVar x) sc.ty E_Pure) brs)) e.ty e.eff)
  | _ -> e

let lower_any_decl (d:decl) : ML decl =
  match d with
  | DLet l ->
    let b = lower_any l.dl_body in
    let b = if b.ty <> l.dl_ret && (mentions_any b.ty || mentions_any l.dl_ret)
            then coerce_any b l.dl_ret else b in
    DLet { l with dl_body = b }
  | _ -> d

let lift_decl (d:decl) : ML (list decl) =
  match d with
  | DLet l ->
    current := string_of_name l.dl_name;
    lift_parent := Some l;
    lifted := [];
    let body = lift (List.map (fun b -> (b.b_name, b.b_ty)) l.dl_binders) l.dl_body in
    if Cons? !lifted && Cons? l.dl_typars then unsupported "a lambda in a polymorphic definition";
    List.rev !lifted @ [DLet { l with dl_body = body }]
  | _ -> [d]

(* -------------------------------------------------------------------- *)
(* Building blocks                                                      *)
(* -------------------------------------------------------------------- *)

type owned = list (string & cty)

let names (o:owned) : ML (list string) = List.map fst o

let var (x:string) (t:cty) : expr = mk (EVar x) t E_Pure

let rc_op (op:op) (x:string) (t:cty) : expr =
  mk (EOp ({ po_op = op; po_ty = None }, [var x t])) TUnit E_Impure

let seq (a b:expr) : expr = mk (ESeq (a, b)) b.ty (join_eff a.eff b.eff)

let decs (o:owned) (e:expr) : ML expr =
  List.fold_right (fun (x, t) e -> seq (rc_op RcDec x t) e) o e

let incs (o:owned) (e:expr) : ML expr =
  List.fold_right (fun (x, t) e -> seq (rc_op RcInc x t) e) o e

let let_ (x:string) (t:cty) (e1 e2:expr) : expr =
  mk (ELet (x, t, e1, e2)) e2.ty (join_eff e1.eff e2.eff)

(* An operand that can stay where it is: a variable, or something whose
   evaluation neither involves a counted value nor does anything. *)
let is_atom (a:expr) : ML bool =
  match a.e with
  | EConst _ | EVar _ | EQual _ -> true
  | _ -> not (touches a) && is_pure a.eff

(* The calling convention of each definition (cherry.md, "Borrow
   inference"): for each parameter, whether the callee takes it owned.  A
   plain parameter is neither, and is listed as owned. *)
let param_owned : ref (HashTable.t string (list bool)) = mk_ref (HashTable.create 0)

(* Which arguments a call takes ownership of: [None] for all of them.  An
   external borrows, except where the runtime says otherwise; a saturated
   call of a definition follows its inferred convention. *)
let call_owns (hd:expr) (args:list expr) : ML (option (list bool)) =
  match hd.e with
  | EQual (n, _) ->
    (match HashTable.try_find !extern_tbl (string_of_name n) with
     | Some fl -> Some fl
     | None ->
       (* A partial application is a closure, which takes what it is given. *)
       match HashTable.try_find !fn_tbl (string_of_name n), HashTable.try_find !param_owned (string_of_name n) with
       | Some (bs, _), Some fl when List.length args = List.length bs -> Some fl
       | _ -> None)
  | _ -> None

(* Borrow inference.  Every counted parameter starts out borrowed, and is
   made owned when the body passes it where something is taken owned: to an
   owned parameter of a call, as an argument of a closure call, or into a
   constructor, record, tuple or partial application (as in Lean: the value
   is usually consumed there, and an owned parameter saves the increment).
   A tail call passing an owned value to a borrowed parameter makes that
   parameter owned instead, which keeps the call a tail call: otherwise the
   value would be released after it -- and for the same reason a definition
   used as a closure takes the parameters the closure is applied to owned.
   The fields of a borrowed scrutinee are
   borrowed.  Iterated to a fixpoint over the whole program. *)
let same_boxed (a b:cty) : ML bool =
  match a, b with
  | TApp (m, []), TApp (n, []) ->
    string_of_name m = string_of_name n && HashTable.mem !boxed_tbl (string_of_name m)
  | _ -> false

(* Whether [e] builds a cell of the boxed type [t] outside a loop: a cell a
   dead scrutinee of type [t] could be reused for. *)
let rec builds (t:cty) (e:expr) : ML bool =
  let any (es:list expr) : ML bool = List.existsb (builds t) es in
  match e.e with
  | ECtor (_, args) -> (Cons? args && same_boxed e.ty t) || any args
  | ELet (_, _, a, b) | ESeq (a, b) -> builds t a || builds t b
  | EIf (c, a, b) -> any [c; a; b]
  | EMatch (sc, brs) -> builds t sc || brs |> List.existsb (fun (_, _, b) -> builds t b)
  | EApp (hd, args) -> any (hd :: args)
  | EOp (_, es) | ETuple es -> any es
  | ERecord (_, fs) -> any (List.map snd fs)
  | EProj (a, _, _) | EDiscrim (a, _) | ECast (a, _) | ECoerce (a, _) -> builds t a
  | _ -> false

(* Whether [y] dies somewhere in [e] before a cell of the boxed type [t] is
   built: either [e] no longer needs [y] and builds one, or a later part of it,
   or an arm of a conditional in it, does.  These are the places where the
   reference counting pass releases [y] just before the rest of the code, and
   where [reuse_at_death] can reuse it instead. *)
let rec dies_building (y:string) (t:cty) (e:expr) : ML bool =
  if not (List.mem y (fv e)) then builds t e else
  match e.e with
  | ELet (z, _, a, b) ->
    if List.mem y (without [z] (fv b)) then dies_building y t b else dies_building y t a
  | ESeq (a, b) ->
    if List.mem y (fv b) then dies_building y t b else dies_building y t a
  | EIf (_, a, b) -> dies_building y t a || dies_building y t b
  | EMatch (_, brs) -> brs |> List.existsb (fun (p, _, b) ->
                         not (List.mem y (pat_vars p)) && dies_building y t b)
  | _ -> false

(* A record type whose values are unboxed and counted. *)
let unboxed_record (t:cty) : ML bool =
  match t with
  | TApp (n, []) ->
    is_np t && not (HashTable.mem !boxed_tbl (string_of_name n)) &&
    HashTable.mem !record_tbl (string_of_name n)
  | _ -> false

let rec set_nth (i:int) (x:bool) (l:list bool) : ML (list bool) =
  match l with
  | [] -> []
  | y :: rest -> if i = 0 then x :: rest else y :: set_nth (i - 1) x rest

let infer_borrows (p:program) (pinned:dlet -> ML (option (list bool))) : ML unit =
  let tbl : HashTable.t string (list bool) = HashTable.create 50 in
  (* The parameters whose convention is given rather than inferred. *)
  let fixed : HashTable.t string (list bool) = HashTable.create 50 in
  let defs = p |> List.collect (fun d ->
    match d with
    | DLet l when Cons? l.dl_binders -> [l]
    | _ -> []) in
  defs |> List.iter (fun l ->
    let f = string_of_name l.dl_name in
    match pinned l with
    | Some fl when List.length fl = List.length l.dl_binders ->
      HashTable.add fixed f (List.map (fun _ -> true) fl); HashTable.add tbl f fl
    | Some _ -> unsupported ("an imported calling convention that does not match " ^ f)
    | None ->
      (* [[@@@cherry_owned]] and [[@@@cherry_borrowed]] on the leading
         parameters (Syntax.CherryMode). *)
      let modes = (match List.tryFind CherryMode? l.dl_flags with
                   | Some (CherryMode ms) -> ms
                   | _ -> []) in
      let mode (i:int) : option bool = if i < List.length modes then List.nth modes i else None in
      let bs = List.mapi (fun i b -> (i, b)) l.dl_binders in
      HashTable.add fixed f (bs |> List.map (fun (i, b) -> is_np b.b_ty && Some? (mode i)));
      HashTable.add tbl f (bs |> List.map (fun (i, b) ->
        not (is_np b.b_ty) || (match mode i with Some o -> o | None -> false))));
  let changed = mk_ref true in
  let own (f:string) (i:int) : ML unit =
    if (match HashTable.try_find fixed f with
        | Some fx -> i < List.length fx && List.nth fx i
        | None -> false) then () else
    match HashTable.try_find tbl f with
    | Some fl when i < List.length fl && not (List.nth fl i) ->
      HashTable.add tbl f (set_nth i true fl); changed := true
    | _ -> () in
  (* A closure of [f] given [k] of its [n] arguments calls [f] from its entry
     point, in tail position, with the rest -- which the entry point is given
     owned, so taking them owned keeps that call a tail call (cherry.md, "Tail
     calls") instead of one followed by their release. *)
  let rec own_from (f:string) (k n:int) : ML unit =
    if k < n then (own f k; own_from f (k + 1) n) in
  let visit (l:dlet) : ML unit =
    let me = string_of_name l.dl_name in
    let params = l.dl_binders |> List.mapi (fun i b -> (b.b_name, i)) in
    let param_ix (y:string) : ML (option int) =
      match List.tryFind (fun (x, _) -> x = y) params with
      | Some (_, i) -> Some i
      | None -> None in
    (* [bf]: the variables in scope that are fields of a borrowed value. *)
    let is_owned_var (bf:list string) (y:string) : ML bool =
      if List.mem y bf then false else
      match param_ix y with
      | None -> true
      | Some i -> (match HashTable.try_find tbl me with
                   | Some fl -> List.nth fl i
                   | None -> true) in
    (* The fields of an unboxed parameter that a flat pattern binds where
       the parameter dies, with the parameter's index: consuming one of them
       owns the parameter, so that the match moves the fields out of it
       instead of counting them again ([take_fields]). *)
    let fields_of : ref (list (string & int)) = mk_ref [] in
    let own_arg (a:expr) : ML unit =
      match a.e with
      | EVar y ->
        (match param_ix y with
         | Some i -> own me i
         | None ->
           match List.tryFind (fun (z, _) -> z = y) !fields_of with
           | Some (_, i) -> own me i
           | None -> ())
      | _ -> () in
    let rec go' (bf:list string) (tail:bool) (e:expr) : ML unit =
      let go = go' bf in
      match e.e with
      | EApp (hd, args) ->
        (match hd.e with
         | EQual (g, _) ->
           let gs = string_of_name g in
           (match HashTable.try_find !extern_tbl gs with
            | Some fl ->
              args |> List.iteri (fun i a -> if i < List.length fl && List.nth fl i then own_arg a)
            | None ->
              match HashTable.try_find !fn_tbl gs, HashTable.try_find tbl gs with
              | Some (bs, _), Some fl ->
                if List.length args = List.length bs then
                  args |> List.iteri (fun i (a:expr) ->
                    if List.nth fl i then own_arg a
                    else if tail && is_np a.ty then
                      (match a.e with
                       | EVar y -> if is_owned_var bf y then own gs i
                       | EQual _ -> ()
                       | _ -> own gs i))
                else begin
                  List.iter own_arg args;
                  own_from gs (List.length args) (List.length bs)
                end
              | _ ->
                (* A global holding a closure. *)
                if HashTable.mem !global_tbl gs then List.iter own_arg args)
         | _ -> List.iter own_arg args; go false hd);
        List.iter (go false) args
      | ELet (x, t, a, b) ->
        go false a;
        let bf = List.filter (fun y -> y <> x) bf in
        (* A field of a borrowed value is borrowed, as in [rc_live]. *)
        let rec root (a:expr) : option string =
          match a.e with
          | EProj (b, _, _) -> (match b.e with EVar y -> Some y | _ -> root b)
          | _ -> None in
        let bf = (match root a with
                  | Some y when is_np t && not (is_owned_var bf y) -> x :: bf
                  | _ -> bf) in
        (match a.e with
         | EProj ({ e = EVar y; ty = yt }, _, _) when is_np t && unboxed_record yt &&
                                                     not (List.mem y (fv b)) ->
           (match param_ix y with
            | Some i -> fields_of := (x, i) :: !fields_of
            | None -> ())
         | _ -> ());
        go' bf tail b
      | ESeq (a, b) -> go false a; go tail b
      | EIf (c, t, f) -> go false c; go tail t; go tail f
      | EMatch (sc, brs) ->
        go false sc;
        (* A parameter matched in a branch that stops needing it, there
           or further in, and then builds a cell of its type is owned, so
           that the cell can be reused. *)
        (match sc.e with
         | EVar y when Some? (param_ix y) && HashTable.mem !boxed_tbl
                         (match sc.ty with TApp (n, []) -> string_of_name n | _ -> "") ->
           if brs |> List.existsb (fun (p, _, b) ->
                (match p with PCtor (_, _ :: _) -> true | _ -> false) &&
                dies_building y sc.ty b)
           then own_arg sc
         | _ -> ());
        (match sc.e, sc.ty with
         | EVar y, TApp (n, []) when is_np sc.ty && not (HashTable.mem !boxed_tbl (string_of_name n))
                                     && not (is_ml_ref sc.ty) ->
           (match param_ix y with
            | Some i ->
              brs |> List.iter (fun (p, _, b) ->
                let flat = (match p with
                            | PCtor (_, ps) -> List.for_all (fun q -> PVar? q || PWild? q) ps
                            | PRecord (_, fps) -> List.for_all (fun (_, q) -> PVar? q || PWild? q) fps
                            | _ -> false) in
                if flat && not (List.mem y (fv b)) then
                  fields_of := List.map (fun v -> (v, i)) (pat_vars p) @ !fields_of)
            | None -> ())
         | _ -> ());
        let borrowed_sc = (match sc.e with
                           | EVar y -> is_np sc.ty && not (is_owned_var bf y)
                           | _ -> false) in
        brs |> List.iter (fun (p, g, b) ->
          let vs = pat_vars p in
          let bf = List.filter (fun y -> not (List.mem y vs)) bf in
          let bf = if borrowed_sc then vs @ bf else bf in
          (match g with Some g -> go' bf false g | None -> ()); go' bf tail b)
      | EWhile (a, b) -> go false a; go false b
      | EOp ({ po_op = IArr f }, es) | EOp ({ po_op = Dyn f }, es) ->
        let fl = (match e.e with EOp ({ po_op = Dyn _ }, _) -> dyn_owns f | _ -> iarr_owns f) in
        es |> List.iteri (fun i a -> if i < List.length fl && List.nth fl i then own_arg a);
        List.iter (go false) es
      | EOp ({ po_op = BufCreate _ }, v :: _)
      | EOp ({ po_op = BufWrite }, [_; _; v]) ->
        own_arg v;
        (match e.e with EOp (_, es) -> List.iter (go false) es | _ -> ())
      | EOp ({ po_op = Update _ }, es)
      | ECtor (_, es) | ETuple es -> List.iter own_arg es; List.iter (go false) es
      | EOp (_, es) -> List.iter (go false) es
      | ERecord (_, fs) -> fs |> List.iter (fun (_, x) -> own_arg x; go false x)
      | EProj (a, _, _) when tail && is_np e.ty && EVar? a.e && unboxed_record a.ty ->
        own_arg a
      | EProj (a, _, _) | EDiscrim (a, _) | ECast (a, _) | ECoerce (a, _) -> go false a
      | EFun (_, b) -> go false b
      | ETry (a, brs) -> go false a; brs |> List.iter (fun (_, _, b) -> go false b)
      | ERaise a -> go false a
      (* A definition used as a value is a closure too. *)
      | EQual (g, _) ->
        (match HashTable.try_find !fn_tbl (string_of_name g) with
         | Some (bs, _) -> own_from (string_of_name g) 0 (List.length bs)
         | None -> ())
      | EVar y when tail && List.existsb (fun (z, _) -> z = y) !fields_of -> own_arg e
      | _ -> () in
    go' [] true l.dl_body in
  let rec loop (fuel:int) : ML unit =
    if !changed && fuel > 0 then begin
      changed := false;
      List.iter visit defs;
      loop (fuel - 1)
    end in
  loop 10000;
  param_owned := tbl

(* The externals the runtime implements: the F* name, the C name, and which
   arguments are taken owned. *)
let runtime_externals : list (string & string & list bool) = [
  "Prims.op_Plus",           "cherry_int_add", [];
  "Prims.op_Minus",          "cherry_int_sub", [];
  "Prims.op_Star",           "cherry_int_mul", [];
  "Prims.op_Slash",          "cherry_int_div", [];
  "Prims.op_Percent",        "cherry_int_mod", [];
  "Prims.op_Tilde_Minus",    "cherry_int_neg", [];
  "Prims.op_Minus_Minus",    "cherry_int_neg", [];
  "Prims.op_Less",           "cherry_int_lt", [];
  "Prims.op_Less_Equals",    "cherry_int_le", [];
  "Prims.op_Greater",        "cherry_int_gt", [];
  "Prims.op_Greater_Equals", "cherry_int_ge", [];
  "Prims.strcat",            "cherry_str_append", [true];
  "Prims.string_of_int",     "cherry_string_of_int", [];
  "Prims.string_of_bool",    "cherry_string_of_bool", [];
  "FStar.String.strlen",     "cherry_str_length", [];
  "FStar.String.length",     "cherry_str_length", [];
  "FStar.String.index",      "cherry_str_index", [];
  "FStar.String.sub",        "cherry_str_sub", [];
  "FStar.String.compare",    "cherry_str_compare", [];
  "FStar.String.make",       "cherry_str_make", [];
  "FStar.Char.u32_of_char",  "cherry_u32_of_char", [];
  "FStar.Char.char_of_u32",  "cherry_char_of_u32", [];
  "FStar.Char.int_of_char",  "cherry_int_of_char", [];
  "FStar.Char.char_of_int",  "cherry_char_of_int", [];
  "FStar.Char.lowercase",    "cherry_char_lowercase", [];
  "FStar.Char.uppercase",    "cherry_char_uppercase", [];
  (* The byte-level primitives of FStar.Pprint-c.cherry.fst. *)
  "FStar.Pprint.byte_size",  "cherry_str_byte_size", [];
  "FStar.Pprint.byte_at",    "cherry_str_byte_at", [];
  "FStar.Pprint.byte_sub",   "cherry_str_byte_sub", [];
  "FStar.IO.print_string",   "cherry_print_string", [];
]


(* Bind the first operand that is not an atom, and hand the rest of the node
   back to [k] with that operand replaced by its name. *)
(* The type of [e], which for a call of a closure the IR may leave as [any]:
   it is then what the closure's type returns after the arguments. *)
let typ_of (e:expr) : ML cty =
  match e.e, e.ty with
  | EApp (hd, args), TAny ->
    let rec drop (n:int) (t:cty) : ML cty =
      if n = 0 then t else match t with TArrow (_, _, b) -> drop (n - 1) b | _ -> TAny in
    drop (List.length args) hd.ty
  | _ -> e.ty

let rec bind_first (args:list expr) : ML (option (string & expr & list expr)) =
  match args with
  | [] -> None
  | a :: rest ->
    let a = { a with ty = typ_of a } in
    if is_atom a then
      (match bind_first rest with
       | Some (x, b, rest') -> Some (x, b, a :: rest')
       | None -> None)
    else
      let x = fresh () in
      Some (x, a, var x a.ty :: rest)

(* -------------------------------------------------------------------- *)
(* Exceptions (cherry.md, "Exceptions")                                 *)
(* -------------------------------------------------------------------- *)

(* The fixpoint.  A definition raises if it raises or re-raises itself
   (a [try] re-raises what it does not catch), or makes a call that may.
   An imported definition with an effect is assumed to. *)
let infer_raises (p:program) : ML unit =
  let tbl : HashTable.t string bool = HashTable.create 50 in
  let rec raises (e:expr) : ML bool =
    match e.e with
    | ERaise _ | ETry _ -> true
    | EApp (_, args) when is_pap e -> List.existsb raises args
    | EApp (hd, args) -> may_raise_in tbl e hd || List.existsb raises args
    | _ -> exists_child raises e
  and may_raise_in (tbl:HashTable.t string bool) (e hd:expr) : ML bool =
    match hd.e with
    | EQual (f, _) when not (HashTable.mem !global_tbl (string_of_name f)) ->
      HashTable.mem tbl (string_of_name f)
    | _ -> not (is_pure e.eff) in
  p |> List.iter (fun d ->
    match d with
    | DLet l when List.existsb Imported? l.dl_flags && not (is_pure l.dl_eff) ->
      HashTable.add tbl (string_of_name l.dl_name) true
    | _ -> ());
  let rec settle () : ML unit =
    let changed = mk_ref false in
    p |> List.iter (fun d ->
      match d with
      (* Whatever its effect: a definition that raises (a [failwith], see
         [failure_of], in [Ex]) or calls one that does. *)
      | DLet l when not (HashTable.mem tbl (string_of_name l.dl_name)) && raises l.dl_body ->
        HashTable.add tbl (string_of_name l.dl_name) true; changed := true
      | _ -> ());
    if !changed then settle () in
  settle ();
  raise_tbl := tbl

(* [e] with every exit through which an exception leaves also freeing the
   reuse token [w]: the exits before the cell that reuses it. *)
let rec free_on_exit (w:string) (wt:cty) (e:expr) : ML expr =
  match e.e with
  | EOp ({ po_op = ExnExit }, []) ->
    seq (mk (EOp ({ po_op = ResetFree; po_ty = None }, [mk (EVar w) wt E_Pure])) TUnit E_Impure) e
  | _ -> map_children (free_on_exit w wt) e

(* -------------------------------------------------------------------- *)
(* Heap cell reuse                                                      *)
(* -------------------------------------------------------------------- *)

(* [e], with reference counting already made explicit, building its first
   cell of type [wt] on each path in the memory of token [w] (from a cell of
   constructor [old]), and freeing [w] on the paths that build none; [None]
   when no path builds one.  A loop is not entered: it builds any number. *)
let rec reuse_in (w:string) (wt:cty) (old:name) (e:expr) : ML (option expr) =
  let free_tok (b:expr) : expr =
    seq (mk (EOp ({ po_op = ResetFree; po_ty = None }, [var w wt])) TUnit E_Impure) b in
  match e.e with
  | ECtor (cn, args) when Cons? args && same_boxed e.ty wt ->
    Some { e with e = EOp ({ po_op = Reuse (old, cn); po_ty = None }, var w wt :: args);
                  eff = E_Impure }
  | ELet (y, t, e1, e2) ->
    (match reuse_in w wt old e1 with
     | Some e1' -> Some { e with e = ELet (y, t, e1', e2); eff = E_Impure }
     | None ->
       match reuse_in w wt old e2 with
       | Some e2' -> Some { e with e = ELet (y, t, free_on_exit w wt e1, e2'); eff = E_Impure }
       | None -> None)
  | ESeq (a, b) ->
    (match reuse_in w wt old a with
     | Some a' -> Some { e with e = ESeq (a', b); eff = E_Impure }
     | None ->
       match reuse_in w wt old b with
       | Some b' -> Some { e with e = ESeq (free_on_exit w wt a, b'); eff = E_Impure }
       | None -> None)
  | EIf (c, t, f) ->
    (match reuse_in w wt old t, reuse_in w wt old f with
     | None, None -> None
     | t', f' ->
       let t = (match t' with Some t -> t | None -> free_tok t) in
       let f = (match f' with Some f -> f | None -> free_tok f) in
       Some { e with e = EIf (c, t, f); eff = E_Impure })
  | EMatch (sc, brs) ->
    let rs = brs |> List.map (fun (p, g, b) -> (p, g, b, reuse_in w wt old b)) in
    if rs |> List.for_all (fun (_, _, _, r) -> None? r) then None else
    Some { e with e = EMatch (sc, rs |> List.map (fun (p, g, b, r) ->
                               match r with
                               | Some b' -> (p, g, b')
                               | None -> (p, g, free_tok b)));
                  eff = E_Impure }
  | _ -> None

(* [e], with reference counting already made explicit, in a branch of a
   match on the owned cell [x] (of constructor [old]) that still needs [x] at
   its start: where [x] is released just before code that builds a cell of
   its type, the release becomes a reset whose token that code reuses (Lean
   places the reset where the variable dies in the same way).  The fields the
   branch uses were counted at its start, so the reset keeps none of them.
   [None] when there is no such place. *)
let rec reuse_at_death (x:string) (wt:cty) (old:name) (ps:list pat) (e:expr) : ML (option expr) =
  let go = reuse_at_death x wt old ps in
  match e.e with
  | ESeq ({ e = EOp ({ po_op = RcDec }, [{ e = EVar y }]) }, rest) when y = x ->
    let w = fresh () in
    (match reuse_in w wt old rest with
     | Some rest' ->
       let kept = List.map (fun _ -> false) ps in
       let reset = mk (EOp ({ po_op = Reset (old, kept); po_ty = None }, [var x wt])) wt E_Impure in
       Some (let_ w wt reset rest')
     | None -> None)
  | ESeq (a, b) ->
    (match go b with
     | Some b' -> Some { e with e = ESeq (a, b'); eff = E_Impure }
     | None ->
       match go a with
       | Some a' -> Some { e with e = ESeq (a', b); eff = E_Impure }
       | None -> None)
  | ELet (y, t, a, b) ->
    (match go b with
     | Some b' -> Some { e with e = ELet (y, t, a, b'); eff = E_Impure }
     | None ->
       match go a with
       | Some a' -> Some { e with e = ELet (y, t, a', b); eff = E_Impure }
       | None -> None)
  | EIf (c, t, f) ->
    (match go t, go f with
     | None, None -> None
     | t', f' ->
       Some { e with e = EIf (c, (match t' with Some t -> t | None -> t),
                                 (match f' with Some f -> f | None -> f));
                     eff = E_Impure })
  | EMatch (sc, brs) ->
    let rs = brs |> List.map (fun (p, g, b) -> (p, g, b, go b)) in
    if rs |> List.for_all (fun (_, _, _, r) -> None? r) then None else
    Some { e with e = EMatch (sc, rs |> List.map (fun (p, g, b, r) ->
                               (p, g, (match r with Some b' -> b' | None -> b))));
                  eff = E_Impure }
  | _ -> None

(* -------------------------------------------------------------------- *)
(* The pass                                                             *)
(* -------------------------------------------------------------------- *)

(* Exceptions.  [held] are the owned references the enclosing
   continuations hold, which an exception leaving the function from inside
   the current expression has to release along with the ones [rc] is given;
   [tail] says that the current expression is the function's result, so that
   a call there needs no test: the caller tests. *)
let held : ref owned = mk_ref []
let tail : ref bool = mk_ref true

let exn_exit (o:owned) (t:cty) : ML expr =
  decs (o @ !held) (mk (EOp ({ po_op = ExnExit; po_ty = None }, [])) t E_Impure)

let exn_pending : expr =
  mk (EOp ({ po_op = ExnPending; po_ty = None }, []))
     (TApp ({ ns = ["Prims"]; id = "bool"; spec = None }, [])) E_Pure

(* Run [f] in a non-tail position, with [o] held by its continuation. *)
let inner (#a:Type) (o:owned) (f:unit -> ML a) : ML a =
  let h = !held in
  let t = !tail in
  held := o @ h;
  tail := false;
  let r = f () in
  held := h;
  tail := t;
  r

(* [rc o e]: [e] with reference counting made explicit.  [o] are the owned
   references live on entry; the result consumes each exactly once, and the
   value it returns is owned by its consumer.  Every other variable of
   non-plain type is borrowed. *)
let rec rc (o:owned) (e:expr) : ML expr =
  let live = fv e in
  let dead, o = List.partition (fun (x, _) -> not (List.mem x live)) o in
  decs dead (rc_live o e)

(* [rc] once the dead references are gone: every [o] is free in [e]. *)
and rc_live (o:owned) (e:expr) : ML expr =
  if Nil? o && not (touches e) then e else
  let owned_names = names o in
  let is_owned (x:string) : bool = List.mem x owned_names in
  match e.e with
  | EVar x ->
    if is_np e.ty && not (is_owned x) then seq (rc_op RcInc x e.ty) e else e
  (* A function's name, as a value, is a closure that is never freed, and a
     global's value is persistent once it is computed: neither is counted. *)
  | EQual (f, _) when TArrow? e.ty && HashTable.mem !fn_tbl (string_of_name f) -> e
  | EQual (g, _) when HashTable.mem !global_tbl (string_of_name g) -> e
  | EQual _ when is_np e.ty -> unsupported "a global of reference-counted type"
  | EConst _ | EQual _ | EAny | EAbort _ | EUnreachable _ -> e

  (* A Pulse stack reference or array of counted values (cherry.md,
     "References").  The cells are declared empty and filled by [PBuf "init"],
     which takes the value; their references are released when the scope
     ends.  Pulse code does not raise, so nothing leaves the scope early. *)
  | ELet (x, t, { e = EOp ({ po_op = BufCreate LStack }, [v; n]) }, e2) when is_pbuf t ->
    let e1 = (match e.e with ELet (_, _, e1, _) -> e1 | _ -> e) in
    let op = (match e1.e with EOp (op, _) -> op | _ -> { po_op = BufCreate LStack; po_ty = None }) in
    if EAny? v.e then unsupported "an uninitialized Pulse reference or array of reference-counted values" else
    if not (is_atom n) then
      let nx = fresh () in
      rc_live o (let_ nx n.ty n { e with e = ELet (x, t, { e1 with e = EOp (op, [v; var nx n.ty]) }, e2) })
    else
    let unit_ty = TUnit in
    let pop (f:string) (args:list expr) : expr =
      mk (EOp ({ po_op = PBuf f; po_ty = None }, args)) unit_ty E_Impure in
    let r = fresh () in
    let body =
      seq (pop "init" [var x t; v; n])
        (let_ r e2.ty e2 (seq (pop "drop" [var x t; n]) (var r e2.ty))) in
    let create = { e1 with e = EOp (op, [{ v with e = EAny }; n]) } in
    { e with e = ELet (x, t, create, rc o body) }

  (* A field of a borrowed value is borrowed for as long as the value, which
     outlives this scope, as the fields a match binds are. *)
  | ELet (x, t, { e = EProj ({ e = EVar y }, _, _) }, e2) when is_np t && not (is_owned y) ->
    let e1 = (match e.e with ELet (_, _, e1, _) -> e1 | _ -> e) in
    let_ x t e1 (rc o e2)
  | ELet (x, t, { e = EProj (a, tn, f) }, e2) when is_np t && EProj? a.e ->
    let e1 = (match e.e with ELet (_, _, e1, _) -> e1 | _ -> e) in
    let z = fresh () in
    rc_live o (let_ z a.ty a { e with e = ELet (x, t, { e1 with e = EProj (var z a.ty, tn, f) }, e2) })

  | ELet (x, t, e1, e2) ->
    let fv2 = without [x] (fv e2) in
    let fv1 = fv e1 in
    let o1, o2 = List.partition (fun (y, _) ->
                   List.mem y fv1 && not (List.mem y fv2)) o in
    let e1' = inner o2 (fun () -> rc o1 e1) in
    let o2 = if is_np t then (x, t) :: o2 else o2 in
    let_ x t e1' (rc o2 e2)

  | ESeq (a, b) when is_np a.ty -> rc_live o (let_ (fresh ()) a.ty a b)
  | ESeq (a, b) ->
    let fvb = fv b in
    let o1, o2 = List.partition (fun (y, _) -> not (List.mem y fvb)) o in
    let a' = inner o2 (fun () -> rc o1 a) in
    seq a' (rc o2 b)

  | EIf (c, t, f) when not (is_atom c) ->
    let x = fresh () in
    rc_live o (let_ x c.ty c { e with e = EIf (var x c.ty, t, f) })
  | EIf (c, t, f) ->
    let t' = rc o t in
    let f' = rc o f in
    { e with e = EIf (c, t', f'); eff = join_eff e.eff (join_eff t'.eff f'.eff) }

  (* Section 115's short circuit survives: the right operand runs only on the
     path where C would have evaluated it. *)
  | EOp ({ po_op = And }, [a; b]) when not (is_atom b) ->
    rc_live o { e with e = EIf (a, b, mk (EConst (CBool false)) e.ty E_Pure) }
  | EOp ({ po_op = Or }, [a; b]) when not (is_atom b) ->
    rc_live o { e with e = EIf (a, mk (EConst (CBool true)) e.ty E_Pure, b) }

  | EMatch (s, brs) when not (EVar? s.e) ->
    if is_atom s && not (is_np s.ty) then
      { e with e = EMatch (s, List.map (rc_branch o None s.ty) brs); eff = E_Impure }
    else
      let x = fresh () in
      rc_live o (let_ x s.ty s { e with e = EMatch (var x s.ty, brs) })
  | EMatch (s, brs) ->
    let x = (match s.e with EVar x -> x | _ -> "") in
    let sc = if is_np s.ty then Some (x, is_owned x) else None in
    { e with e = EMatch (s, List.map (rc_branch o sc s.ty) brs); eff = E_Impure }

  | EApp (hd, args) when EQual? hd.e ->
    (match bind_first args with
     | Some (x, a, args') -> rc_live o (let_ x a.ty a { e with e = EApp (hd, args') })
     | None ->
       call o (call_owns hd args) args e)
  (* A call of a closure borrows the closure and takes the arguments. *)
  | EApp (hd, args) ->
    (match bind_first (hd :: args) with
     | Some (x, a, hd' :: args') -> rc_live o (let_ x a.ty a { e with e = EApp (hd', args') })
     | _ -> call o (Some (false :: List.map (fun _ -> true) args)) (hd :: args) e)
  | ECtor (cn, args) ->
    (match bind_first args with
     | Some (x, a, args') -> rc_live o (let_ x a.ty a { e with e = ECtor (cn, args') })
     | None -> call o None args e)
  | ERecord (n, fs) ->
    (match bind_first (List.map snd fs) with
     | Some (x, a, vs) ->
       rc_live o (let_ x a.ty a { e with e = ERecord (n, List.zip (List.map fst fs) vs) })
     | None -> call o None (List.map snd fs) e)

  | EOp ({ po_op = RcInc }, _) | EOp ({ po_op = RcDec }, _) -> e

  (* An ML reference.  Allocating one takes the value; reading one borrows
     the reference and returns a counted copy; writing one borrows the
     reference and takes the value, releasing the one it replaces. *)
  | EOp ({ po_op = BufCreate _ }, [v; _]) when is_ml_ref e.ty ->
    rc_live o { e with e = EOp ({ po_op = RefNew; po_ty = None }, [v]) }
  | EOp ({ po_op = BufRead }, [r; _]) when is_ml_ref r.ty ->
    rc_live o { e with e = EOp ({ po_op = RefGet; po_ty = None }, [r]) }
  | EOp ({ po_op = BufWrite }, [r; _; v]) when is_ml_ref r.ty ->
    rc_live o { e with e = EOp ({ po_op = RefSet; po_ty = None }, [r; v]) }
  | EOp (op, args) when RefNew? op.po_op || RefGet? op.po_op || RefSet? op.po_op ->
    (match bind_first args with
     | Some (x, a, args') -> rc_live o (let_ x a.ty a { e with e = EOp (op, args') })
     | None ->
       let owns = (match op.po_op with
                   | RefNew -> [true] | RefGet -> [false] | _ -> [false; true]) in
       call o (Some owns) args { e with eff = E_Impure })
  (* An immutable array: the operations borrow the array, except the two
     that update it, which take it so that a unique one is changed in place
     (cherry.md, "Arrays"). *)
  (* [mkdyn] at [dyn] itself is the identity (cherry.md, "The any type"),
     and so is [undyn]: a [dyn] of a [dyn] is the [dyn]. *)
  | EOp ({ po_op = Dyn _ }, [a])
    when (match a.ty, e.ty with
          | TAny, TAny -> true
          | _ -> false) ->
    rc_live o a
  | EOp (op, args) when Dyn? op.po_op ->
    (match bind_first args with
     | Some (x, a, args') -> rc_live o (let_ x a.ty a { e with e = EOp (op, args') })
     | None -> call o (Some (dyn_owns (Dyn?._0 op.po_op))) args { e with eff = E_Impure })
  | EOp (op, args) when IArr? op.po_op ->
    (match bind_first args with
     | Some (x, a, args') -> rc_live o (let_ x a.ty a { e with e = EOp (op, args') })
     | None -> call o (Some (iarr_owns (IArr?._0 op.po_op))) args { e with eff = E_Impure })
  (* A Pulse reference or array of counted values (cherry.md,
     "References"). *)
  | EOp ({ po_op = BufCreate LStack }, _) when is_pbuf e.ty ->
    unsupported "a Pulse stack allocation of reference-counted values outside a let"
  | EOp ({ po_op = BufCreate _ }, [v; n]) when is_pbuf e.ty ->
    if EAny? v.e then unsupported "an uninitialized Pulse reference or array of reference-counted values" else
    rc_live o { e with e = EOp ({ po_op = PBuf "alloc"; po_ty = None }, [v; n]) }
  | EOp ({ po_op = BufRead }, [b; i]) when is_pbuf b.ty ->
    rc_live o { e with e = EOp ({ po_op = PBuf "read"; po_ty = None }, [b; i]) }
  | EOp ({ po_op = BufWrite }, [b; i; v]) when is_pbuf b.ty ->
    rc_live o { e with e = EOp ({ po_op = PBuf "write"; po_ty = None }, [b; i; v]) }
  | EOp ({ po_op = BufFree }, [b]) when is_pbuf b.ty ->
    rc_live o { e with e = EOp ({ po_op = PBuf "free"; po_ty = None }, [b]) }
  | EOp ({ po_op = BufBlit }, [s; si; d; di; n]) when is_pbuf s.ty ->
    rc_live o { e with e = EOp ({ po_op = PBuf "blit"; po_ty = None }, [s; si; d; di; n]) }
  | EOp ({ po_op = BufLit }, es) when List.existsb (fun (a:expr) -> is_np a.ty) es ->
    unsupported "a constant array of reference-counted values"
  | EOp (op, args) when PBuf? op.po_op ->
    (match bind_first args with
     | Some (x, a, args') -> rc_live o (let_ x a.ty a { e with e = EOp (op, args') })
     | None -> call o (Some (pbuf_owns (PBuf?._0 op.po_op))) args { e with eff = E_Impure })
  | EOp ({ po_op = ExnTake }, []) -> call o (Some []) [] { e with eff = E_Impure }
  (* A record update takes the record and the new values. *)
  | EOp (op, args) when Update? op.po_op ->
    (match bind_first args with
     | Some (x, a, args') -> rc_live o (let_ x a.ty a { e with e = EOp (op, args') })
     | None -> call o None args { e with eff = E_Impure })
  | EOp (_, _) when is_np e.ty ->
    unsupported "a primitive operation returning a reference-counted value"
  | EOp (op, args) ->
    (match bind_first args with
     | Some (x, a, args') -> rc_live o (let_ x a.ty a { e with e = EOp (op, args') })
     | None -> call o (Some []) args e)
  | EDiscrim (a, cn) ->
    (match bind_first [a] with
     | Some (x, a, [a']) -> rc_live o (let_ x a.ty a { e with e = EDiscrim (a', cn) })
     | _ -> call o (Some []) [a] e)
  | ECast (a, t) ->
    (match bind_first [a] with
     | Some (x, a, [a']) -> rc_live o (let_ x a.ty a { e with e = ECast (a', t) })
     | _ -> call o (Some []) [a] e)
  | ECoerce (a, t) ->
    let a' = rc_live o a in
    { e with e = ECoerce (a', t); eff = join_eff e.eff a'.eff }

  (* A field read borrows from its parent.  The field is taken a reference to
     before the parent can go, which is the order that keeps it alive. *)
  | EProj (a, tn, f) ->
    (match bind_first [a] with
     | Some (x, a, [a']) -> rc_live o (let_ x a.ty a { e with e = EProj (a', tn, f) })
     | _ ->
       if Nil? o && not (is_np e.ty) then e else
       (* An owned unboxed record that dies here gives up the field read
          and releases the others (cherry.md, "Calling convention"). *)
       let moved =
         (match a.e, a.ty with
          | EVar y, TApp (n, []) when is_np e.ty && is_owned y &&
                                      not (HashTable.mem !boxed_tbl (string_of_name n)) ->
            HashTable.try_find !record_tbl (string_of_name n)
            |> Option.map (fun fs -> (y, fs))
          | _ -> None) in
       match moved with
       | Some (y, fs) ->
         let r = fresh () in
         let rest = o |> List.filter (fun (z, _) -> z <> y) in
         let body = decs rest (var r e.ty) in
         let body = fs |> List.fold_left (fun body (g, gt) ->
           if g = f || not (is_np gt) then body else
           let z = fresh () in
           let_ z gt { e with e = EProj (a, tn, g); ty = gt } (seq (rc_op RcDec z gt) body)) body in
         let_ r e.ty e body
       | None ->
       let r = fresh () in
       let body = decs o (var r e.ty) in
       let body = if is_np e.ty then seq (rc_op RcInc r e.ty) body else body in
       let_ r e.ty e body)

  (* A loop runs its body any number of times, so it consumes nothing: what it
     reads it borrows, and what it allocates it releases before it goes round
     again.  The references it was given are released after it. *)
  | EWhile (c, b) ->
    let w = inner o (fun () -> { e with e = EWhile (rc [] c, rc [] b); eff = E_Impure }) in
    if Nil? o then w else
    let x = fresh () in
    let_ x e.ty w (decs o (var x e.ty))

  | EFun _ -> failwith "Cherry: a lambda survived lifting"
  | ETuple _ -> unsupported "an anonymous tuple of reference-counted values"
  (* [raise e] stores [e], releases everything held, and leaves. *)
  | ERaise a ->
    (match bind_first [a] with
     | Some (x, a, [a']) -> rc_live o (let_ x a.ty a { e with e = ERaise a' })
     | _ ->
       let set = mk (EOp ({ po_op = ExnRaise; po_ty = None }, [a])) TUnit E_Impure in
       let t = !tail in
       tail := true;
       let s = call o None [a] set in
       tail := t;
       seq s (exn_exit [] e.ty))
  (* [try s with brs], where [s] calls the body's function: the call, and
     then, if an exception is pending, a match on it, which raises it again
     when no branch takes it. *)
  | ETry (s, brs) ->
    let r = fresh () in
    let ex = fresh () in
    let exv = var ex TExn in
    let again = mk (ERaise exv) e.ty E_Impure in
    let handler = mk (EMatch (exv, brs @ [(PWild, None, again)])) e.ty E_Impure in
    let take = mk (EOp ({ po_op = ExnTake; po_ty = None }, [])) TExn E_Impure in
    let caught = let_ ex TExn take handler in
    (* The call itself is not tested like other calls: the test follows.
       On an exception its result is no value, so only the other branch
       owns it. *)
    let fvk = fv caught in
    let o1, o2 = List.partition (fun (y, _) -> not (List.mem y fvk)) o in
    let s' = inner o2 (fun () -> tail := true; rc o1 s) in
    let ro = if is_np e.ty then (r, e.ty) :: o2 else o2 in
    let_ r e.ty s'
      (mk (EIf (exn_pending, rc o2 caught, rc ro (var r e.ty))) e.ty E_Impure)

(* A node whose operands are all atoms.  [owns] says which operands it
   takes ownership of ([None]: every one).  An owned variable in an owned
   position is moved there, unless it also appears in a borrowed one, which
   needs it alive throughout; every other counted variable in an owned
   position is a new reference.  The owned variables not moved are released
   after the node. *)
and call (o:owned) (owns:option (list bool)) (args:list expr) (node:expr)
  : ML expr =
  let owned_at (i:int) : ML bool =
    match owns with
    | None -> true
    | Some fl -> i < List.length fl && List.nth fl i in
  let borrowed_vars = args |> List.mapi (fun i (a:expr) ->
    match a.e with
    | EVar y when not (owned_at i) -> [y]
    | _ -> []) |> List.flatten in
  let remaining = mk_ref (names o) in
  let extra = args |> List.mapi (fun i (a:expr) ->
    match a.e with
    | EVar y when is_np a.ty && owned_at i ->
      if List.mem y !remaining && not (List.mem y borrowed_vars)
      then (remaining := List.filter (fun z -> z <> y) !remaining; [])
      else [(y, a.ty)]
    | _ -> []) |> List.flatten in
  let left = o |> List.filter (fun (y, _) -> List.mem y !remaining) in
  let raises = may_raise node in
  let node = if owns = Some [] then node else { node with eff = E_Impure } in
  let call = incs extra node in
  (* A call that may raise is tested, unless it is the function's result,
     which its caller tests: on an exception what the call did not take is
     released, the result (which is no value) is not, and the function
     leaves. *)
  if raises && not !tail then
    let r = fresh () in
    let_ r node.ty call
      (mk (EIf (exn_pending, exn_exit left node.ty, decs left (var r node.ty)))
          node.ty E_Impure)
  else
  if Nil? left then call else
  let r = fresh () in
  let_ r node.ty call (decs left (var r node.ty))

(* A flat pattern on an unboxed value, rewritten to bind every counted
   field, with those fields: when the match owns the value and it dies, the
   fields are its references, moved out rather than counted again
   (cherry.md, "Calling convention").  [None] for any other pattern. *)
and take_fields (p:pat) : ML (option (pat & owned)) =
  let flat (q:pat) = PVar? q || PWild? q in
  let bind (q:pat) (t:cty) : ML (option (string & cty) & pat) =
    match q with
    | PVar v -> (if is_np t then Some (v, t) else None), q
    | _ -> if is_np t then let v = fresh () in Some (v, t), PVar v else None, q in
  match p with
  | PCtor (c, ps) when List.for_all flat ps ->
    (match HashTable.try_find !ctor_tbl (string_of_name c) with
     | Some fs when List.length fs = List.length ps ->
       let bs = List.map2 (fun (_, t) q -> bind q t) fs ps in
       Some (PCtor (c, List.map snd bs), List.collect (fun (b, _) -> match b with Some b -> [b] | None -> []) bs)
     | _ -> None)
  | PRecord (tn, fps) when List.for_all (fun (_, q) -> flat q) fps ->
    (match HashTable.try_find !record_tbl (string_of_name tn) with
     | Some fs ->
       let bs = fs |> List.map (fun (f, t) ->
         let q = match List.tryFind (fun (g, _) -> g = f) fps with Some (_, q) -> q | None -> PWild in
         let b, q = bind q t in
         b, (f, q)) in
       let fps = bs |> List.filter (fun (_, (_, q)) -> PVar? q) |> List.map snd in
       Some (PRecord (tn, fps), List.collect (fun (b, _) -> match b with Some b -> [b] | None -> []) bs)
     | None -> None)
  | _ -> None

(* One branch.  [sc] is the scrutinee when it is a counted variable, and
   whether this match owns it.  Every field the branch uses is given a
   reference of its own before an owned scrutinee is released; the fields of
   a borrowed one are borrowed. *)
and rc_branch (o:owned) (sc:option (string & bool)) (st:cty) (br:branch) : ML branch =
  let p, g, b = br in
  if Some? g then unsupported "a pattern guard" else
  let binds = pat_binds p st in
  let live = without (pat_vars p) (fv b) in
  let fvb = fv b in
  let dead = o |> List.filter (fun (y, _) -> not (List.mem y live)) in
  let keep = o |> List.filter (fun (y, _) -> List.mem y live) in
  let fields = binds |> List.filter (fun (v, t) -> is_np t && List.mem v fvb) in
  match sc with
  | None ->
    (p, g, decs dead (rc (keep @ fields) b))
  (* A borrowed scrutinee outlives the match, and so do its fields: they
     are borrowed too, and cost nothing. *)
  | Some (_, false) ->
    (p, g, decs dead (rc keep b))
  | Some (x, true) ->
    let dead_x, dead_other = List.partition (fun (y, _) -> y = x) dead in
    (* A constructor without fields of a boxed type is not a cell. *)
    let dead_x = (match p with
                  | PCtor (_, []) when HashTable.mem !boxed_tbl
                      (match st with TApp (n, []) -> string_of_name n | _ -> "") -> []
                  | _ -> dead_x) in
    let boxed_st = HashTable.mem !boxed_tbl (match st with
                                             | TApp (n, []) -> string_of_name n
                                             | _ -> "") in
    match (if Cons? dead_x && not boxed_st && TApp? st && not (is_ml_ref st)
           then take_fields p else None) with
    | Some (p', taken) -> (p', g, decs dead_other (rc (keep @ taken) b))
    | None ->
    let body = rc (keep @ fields) b in
    let body =
      (match p with
       | PCtor (c, ps) when Nil? dead_x && Cons? ps && boxed_st && List.mem x live ->
         (match reuse_at_death x st c ps body with
          | Some body' -> body'
          | None -> body)
       | _ -> body) in
    let plain () : ML branch = (p, g, decs dead_other (incs fields (decs dead_x body))) in
    (* The scrutinee dies here: a cell this branch builds can reuse its memory
       (cherry.md, "Heap cell reuse").  Each field is bound by a variable or
       by a pattern binding none, so that the reset can tell the kept ones
       apart. *)
    (match p with
     | PCtor (c, ps) when Cons? dead_x && Cons? ps &&
                          ps |> List.for_all (fun q -> PVar? q || Nil? (pat_vars q)) &&
                          HashTable.mem !boxed_tbl (match st with
                                                    | TApp (n, []) -> string_of_name n
                                                    | _ -> "") ->
       let w = fresh () in
       (match reuse_in w st c body with
        | Some body' ->
          let kept = ps |> List.map (fun q ->
                       match q with
                       | PVar v -> List.mem v (names fields)
                       | _ -> false) in
          let reset = mk (EOp ({ po_op = Reset (c, kept); po_ty = None }, [var x st])) st E_Impure in
          (p, g, decs dead_other (let_ w st reset body'))
        | None -> plain ())
     | _ -> plain ())

let run_let (l:dlet) : ML dlet =
  current := string_of_name l.dl_name;
  let fl = match HashTable.try_find !param_owned (string_of_name l.dl_name) with
           | Some fl -> fl
           | None -> List.map (fun _ -> true) l.dl_binders in
  let o = List.zip l.dl_binders fl
          |> List.filter (fun (b, ow) -> ow && is_np b.b_ty)
          |> List.map (fun (b, _) -> (b.b_name, b.b_ty)) in
  held := [];
  (* A global's initializer has no caller to test for it. *)
  tail := Cons? l.dl_binders;
  if Nil? o && not (touches l.dl_body) && not (HashTable.mem !raise_tbl (string_of_name l.dl_name)) then l else
  let body = rc o l.dl_body in
  { l with dl_body = body; dl_eff = join_eff l.dl_eff body.eff }

(* [failwith s] raises [Failure s] (cherry.md, "Exceptions"), so that it can
   be caught: the support modules' [failwith] is an external, and their
   [Failure] is declared beside it. *)
let failure_of (f:name) : option name =
  if f.id = "failwith" && (f.ns = ["FStar"; "All"] || f.ns = ["FStarC"; "Effect"])
  then Some { f with id = "Failure"; spec = None }
  else None

let is_effect_fn (f:name) (id:string) : bool =
  f.id = id && (f.ns = ["FStar"; "All"] || f.ns = ["FStarC"; "Effect"])

(* The runtime's [exit], which does not return: [exit n] at any type is a call
   of it followed by a [raise] that only gives the expression its type. *)
let cherry_exit_name : name = { ns = ["FStarC"; "Effect"]; id = "cherry_exit"; spec = None }

let raise_failures (p:program) : ML program =
  let used : ref (list (name & cty)) = mk_ref [] in
  let exit_ty : ref (option cty) = mk_ref None in
  let use (x:name) (t:cty) : ML unit =
    if not (List.existsb (fun (y, _) -> string_of_name y = string_of_name x) !used) then
      used := (x, t) :: !used in
  let rec go (e:expr) : ML expr =
    match e.e with
    | EApp ({ e = EQual (f, _) }, [s]) when Some? (failure_of f) ->
      let x = Some?.v (failure_of f) in
      let s = go s in
      use x s.ty;
      mk (ERaise (mk (ECtor (x, [s])) TExn E_Pure)) e.ty E_Impure
    (* [raise_notrace] differs from [raise] only in OCaml's backtraces. *)
    | EApp ({ e = EQual (f, _) }, [x]) when is_effect_fn f "raise_notrace" ->
      mk (ERaise (go x)) e.ty E_Impure
    | EApp ({ e = EQual (f, _) }, [n]) when is_effect_fn f "exit" ->
      let n = go n in
      exit_ty := Some n.ty;
      let failure = { ns = ["FStarC"; "Effect"]; id = "Failure"; spec = None } in
      let str = TApp ({ ns = ["Prims"]; id = "string"; spec = None }, []) in
      use failure str;
      let fty = TArrow (n.ty, E_Impure, TUnit) in
      let call = mk (EApp (mk (EQual (cherry_exit_name, [])) fty E_Pure, [n])) TUnit E_Impure in
      let msg = mk (EConst (CString "exit")) str E_Pure in
      mk (ESeq (call, mk (ERaise (mk (ECtor (failure, [msg])) TExn E_Pure)) e.ty E_Impure))
        e.ty E_Impure
    | _ -> map_children go e in
  let p = p |> List.map (fun d ->
    match d with
    | DLet l -> DLet { l with dl_body = go l.dl_body }
    | d -> d) in
  let declared (x:name) : ML bool =
    p |> List.existsb (fun d -> match d with
      | DExn y -> string_of_name y.de_name = string_of_name x
      | _ -> false) in
  let missing = !used |> List.filter (fun (x, _) -> not (declared x)) in
  let exit_decl =
    match !exit_ty with
    | None -> []
    | Some t ->
      [DExternal { dx_name = cherry_exit_name; dx_typars = []; dx_ty = TArrow (t, E_Impure, TUnit);
                   dx_target = Some "cherry_exit"; dx_header = Some "cherry.h"; dx_flags = [] }] in
  (missing |> List.map (fun (x, t) -> DExn { de_name = x; de_args = [t]; de_flags = [] })) @ exit_decl @ p

(* A recursive record is boxed, and is boxed the way a recursive variant is:
   as a variant of one constructor, [Mk_] and the type's name. *)
let derecord (bx:HashTable.t string bool) (p:program) : ML program =
  let recs = p |> List.collect (fun d ->
    match d with
    | DType ({ dt_name = n; dt_body = TRecord fs })
        when HashTable.mem bx (string_of_name n) -> [(string_of_name n, (n, fs))]
    | _ -> []) in
  if Nil? recs then p else
  let mkn (n:name) : name = { n with id = "Mk_" ^ n.id } in
  let find (n:name) = List.tryFind (fun (k, _) -> k = string_of_name n) recs in
  let rec rpat (q:pat) : ML pat =
    match q with
    | PRecord (n, fps) ->
      (match find n with
       | Some (_, (_, fs)) ->
         PCtor (mkn n, fs |> List.map (fun (f, _) ->
           match List.tryFind (fun (g, _) -> g = f) fps with
           | Some (_, q) -> rpat q
           | None -> PWild))
       | None -> PRecord (n, List.map (fun (f, q) -> (f, rpat q)) fps))
    | PCtor (c, qs) -> PCtor (c, List.map rpat qs)
    | PTuple qs -> PTuple (List.map rpat qs)
    | POr qs -> POr (List.map rpat qs)
    | q -> q in
  let br (x:branch) : ML branch = let (q, g, b) = x in (rpat q, g, b) in
  let rec go (e:expr) : ML expr =
    let e = map_children go e in
    match e.e with
    | ERecord (n, fes) ->
      (match find n with
       | Some (_, (_, fs)) ->
         { e with e = ECtor (mkn n, fs |> List.map (fun (f, _) ->
             match List.tryFind (fun (g, _) -> g = f) fes with
             | Some (_, x) -> x
             | None -> failwith ("Cherry: record field " ^ f ^ " missing"))) }
       | None -> e)
    | EMatch (sc, brs) -> { e with e = EMatch (sc, List.map br brs) }
    | ETry (b, brs) -> { e with e = ETry (b, List.map br brs) }
    | _ -> e in
  p |> List.map (fun d ->
    match d with
    | DType dt ->
      (match find dt.dt_name with
       | Some (_, (n, fs)) -> DType { dt with dt_body = TVariant [(mkn n, fs)] }
       | None -> d)
    | DLet l -> DLet { l with dl_body = go l.dl_body }
    | d -> d)

(* Record updates (cherry.md, "Record updates").  F* spells [{ x with f = v }]
   out as the constructor applied to [v] and to [x]'s other fields, read off
   [x].  When at least as many of a boxed constructor's arguments are the
   field at their own position of one variable [x] of the same type as are
   not, the constructor becomes an [Update] of [x], which changes [x] in
   place when it is unique instead of building a cell and counting every
   field it keeps. *)
let record_updates (p:program) : ML program =
  let rec go (e:expr) : ML expr =
    let e = map_children go e in
    match e.e with
    | ECtor (cn, args) when Cons? args ->
      (match HashTable.try_find !ctor_tbl (string_of_name cn) with
       | Some fs when List.length fs = List.length args && same_boxed e.ty e.ty ->
         let src (f:string) (a:expr) : option string =
           match a.e with
           | EProj ({ e = EVar x; ty = t }, _, g) when g = f && same_boxed t e.ty -> Some x
           | _ -> None in
         let srcs = List.map2 (fun (f, _) a -> src f a) fs args in
         (match List.tryFind Some? srcs with
          | Some (Some x) ->
            let kept = srcs |> List.map (fun s -> s = Some x) in
            let nk = List.length (List.filter (fun k -> k) kept) in
            if 2 * nk < List.length kept then e else
            let changed = List.zip (List.zip kept args) (List.mapi (fun i _ -> i) args)
                          |> List.filter (fun ((k, _), _) -> not k) in
            { e with e = EOp ({ po_op = Update (cn, List.map snd changed); po_ty = None },
                              mk (EVar x) e.ty E_Pure :: List.map (fun ((_, a), _) -> a) changed) }
          | _ -> e)
       | _ -> e)
    | _ -> e in
  p |> List.map (fun d ->
    match d with
    | DLet l -> DLet { l with dl_body = go l.dl_body }
    | d -> d)

(* A type variable monomorphization left standing -- a method polymorphic in
   its own right, say -- is a value whose type nobody here knows, and Cherry
   has a type for that: [any], as OCaml's uniform representation would. *)
let rec tv_any (t:cty) : ML cty =
  match t with
  | TVar _ -> TAny
  | TArrow (a, f, b) -> TArrow (tv_any a, f, tv_any b)
  | TApp (n, ts) -> TApp (n, List.map tv_any ts)
  | TTuple ts -> TTuple (List.map tv_any ts)
  | TBuf c -> TBuf (tv_any c)
  | TRef (k, c) -> TRef (k, tv_any c)
  | TInline c -> TInline (tv_any c)
  | t -> t

let rec has_tv (t:cty) : ML bool =
  match t with
  | TVar _ -> true
  | TArrow (a, _, b) -> has_tv a || has_tv b
  | TApp (_, ts) | TTuple ts -> List.existsb has_tv ts
  | TBuf c | TRef (_, c) | TInline c -> has_tv c
  | _ -> false

let rec tv_any_expr (e:expr) : ML expr =
  let e = map_children tv_any_expr e in
  let bnd (b:binder) : ML binder = { b with b_ty = tv_any b.b_ty } in
  let e' = match e.e with
           | ELet (x, t, a, b) -> ELet (x, tv_any t, a, b)
           | EFun (bs, b) -> EFun (List.map bnd bs, b)
           | ECoerce (a, t) -> ECoerce (a, tv_any t)
           | EQual (n, ts) -> EQual (n, List.map tv_any ts)
           | x -> x in
  { e with e = e'; ty = tv_any e.ty }

let tv_any_decl (d:decl) : ML decl =
  match d with
  (* The body too when the signature has none: a local binding or a type
     argument inside it may still mention one. *)
  | DLet l ->
    DLet { l with dl_ret = tv_any l.dl_ret;
                  dl_binders = List.map (fun (b:binder) -> { b with b_ty = tv_any b.b_ty }) l.dl_binders;
                  dl_body = tv_any_expr l.dl_body }
  | _ -> d

let run (p:program) : ML program =
  co_counter := 0;
  let p = raise_failures p in
  let p = List.map tv_any_decl p in
  let np = HashTable.create 50 in
  nonplain_types p |> List.iter (fun k -> HashTable.add np k true);
  np_tbl := np;
  let bx = HashTable.create 50 in
  boxed_types p |> List.iter (fun k -> HashTable.add bx k true);
  boxed_tbl := bx;
  let p = derecord bx p in
  let ct = HashTable.create 50 in
  let rt = HashTable.create 50 in
  let xt = HashTable.create 50 in
  p |> List.iter (fun d ->
    match d with
    | DType ({ dt_body = TVariant cs }) ->
      cs |> List.iter (fun (c, fs) -> HashTable.add ct (string_of_name c) fs)
    | DExn x ->
      HashTable.add ct (string_of_name x.de_name)
        (x.de_args |> List.mapi (fun i t -> ("f" ^ string_of_int i, t)))
    | DType ({ dt_name = n; dt_body = TRecord fs }) ->
      HashTable.add rt (string_of_name n) fs
    | DExternal x ->
      let owns = match List.tryFind (fun (n, _, _) -> n = string_of_name x.dx_name)
                                    runtime_externals with
                 | Some (_, _, fl) -> fl
                 | None ->
                   (* An external borrows its arguments unless a binder says
                      [[@@@cherry_owned]] (Syntax.CherryMode). *)
                   match List.tryFind CherryMode? x.dx_flags with
                   | Some (CherryMode ms) -> ms |> List.map (fun m -> m = Some true)
                   | _ -> [] in
      HashTable.add xt (string_of_name x.dx_name) owns
    | _ -> ());
  ctor_tbl := ct; record_tbl := rt; extern_tbl := xt;
  let p = record_updates p in
  let ft = HashTable.create 50 in
  p |> List.iter (fun d ->
    match d with
    | DLet l when Cons? l.dl_binders ->
      HashTable.add ft (string_of_name l.dl_name) (l.dl_binders, l.dl_ret)
    | _ -> ());
  fn_tbl := ft;
  let gt = HashTable.create 50 in
  p |> List.iter (fun d ->
    match d with
    | DLet l when Nil? l.dl_binders -> HashTable.add gt (string_of_name l.dl_name) true
    | _ -> ());
  global_tbl := gt;
  let xa = HashTable.create 50 in
  p |> List.iter (fun d ->
    match d with
    | DExternal x ->
      let rec count (t:cty) : ML int = match t with TArrow (_, _, b) -> 1 + count b | _ -> 0 in
      HashTable.add xa (string_of_name x.dx_name)
        (count x.dx_ty, (if Nil? x.dx_typars then Some x.dx_ty else None))
    | _ -> ());
  extern_arity := xa;
  counter := 0;
  let p = p |> List.map (fun d -> match d with
                                  | DLet l -> DLet { l with dl_body = unguard l.dl_body }
                                  | _ -> d) in
  let p = List.map lower_any_decl p in
  let p = List.collect lift_decl p in
  (* An imported definition is called the way its unit compiled it, which
     its interface records (Syntax.CherryConv); one without the record owns
     every parameter.  The definitions this unit exports are inferred like
     any other, and {!conventions} records theirs for its interface. *)
  let pinned (l:dlet) : ML (option (list bool)) =
    if not (List.existsb Imported? l.dl_flags) then None else
    match List.tryFind CherryConv? l.dl_flags with
    | Some (CherryConv fl) -> Some fl
    | _ -> Some (List.map (fun _ -> true) l.dl_binders) in
  infer_borrows p pinned;
  infer_raises p;
  counter := 0;
  p |> List.map (fun d ->
    match d with
    | DLet l -> DLet (run_let l)
    | DExternal x ->
      (match List.tryFind (fun (n, _, _) -> n = string_of_name x.dx_name)
                          runtime_externals with
       | Some (_, c, _) -> DExternal { x with dx_target = Some c; dx_header = Some "cherry.h" }
       | None -> d)
    | _ -> d)

let record_conventions (p:program) : ML program =
  p |> List.map (fun d ->
    match d with
    | DLet l when Cons? l.dl_binders ->
      (match HashTable.try_find !param_owned (string_of_name l.dl_name) with
       | Some fl ->
         DLet { l with dl_flags = CherryConv fl :: List.filter (fun f -> not (CherryConv? f)) l.dl_flags }
       | None -> d)
    | _ -> d)
