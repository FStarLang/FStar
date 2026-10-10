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

(* The type names a value of [t] holds by value.  A pointer is a size, and
   what it reaches is not part of the value. *)
let rec by_value (t:cty) : ML (list string) =
  match t with
  | TApp (n, args) -> string_of_name n :: List.collect by_value args
  | TTuple ts -> List.collect by_value ts
  | TArrow _ -> [arrow_key]
  | _ -> []

(* Does a value of [t] contain a value of [target], through any number of
   by-value fields? *)
let rec reaches (tbl:HashTable.t string dtype) (target:string) (fuel:int) (t:cty)
  : ML bool =
  fuel > 0 &&
  (by_value t |> List.existsb (fun n ->
     n = target ||
     (match HashTable.try_find tbl n with
      | Some d -> field_types d.dt_body |> List.existsb (reaches tbl target (fuel - 1))
      | None -> false)))

let boxed_types (p:program) : ML (list string) =
  let tbl = type_table p in
  p |> List.collect (fun d ->
    match d with
    | DType dt when (TVariant? dt.dt_body || TRecord? dt.dt_body) ->
      let k = string_of_name dt.dt_name in
      if field_types dt.dt_body |> List.existsb (reaches tbl k 100) then [k] else []
    | _ -> [])

(* The types the runtime (ulib/c/cherry.h) represents as counted cells. *)
let runtime_types : list string = ["Prims.int"; "Prims.string"]

let nonplain_types (p:program) : ML (list string) =
  let tbl = type_table p in
  let np : HashTable.t string bool = HashTable.create 50 in
  runtime_types |> List.iter (fun k -> HashTable.add np k true);
  HashTable.add np arrow_key true;
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
  | TArrow _ -> true
  | _ -> false

(* Does evaluating [e] involve a non-plain value anywhere?  The function a
   direct call names is not a value. *)
let rec touches (e:expr) : ML bool =
  is_np e.ty ||
  (match e.e with
   | ELet (_, t, _, _) when is_np t -> true
   | EApp ({ e = EQual _ }, args) -> List.existsb touches args
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
  | ETry (s, brs) ->
    { e with e = ETry (lift env s, List.map (lift_branch env TUnit) brs) }
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

(* An integer literal too large to be a small integer on a 32-bit target is
   a cell, allocated where it is evaluated. *)
let small_int_bound : int = 1073741824

let is_big_literal (c:constant) : bool =
  match c with
  | CInt (v, _, None) -> v >= small_int_bound || v <= - small_int_bound
  | _ -> false

(* An operand that can stay where it is: a variable, or something whose
   evaluation neither involves a counted value nor does anything. *)
let is_atom (a:expr) : ML bool =
  match a.e with
  | EConst c -> not (is_big_literal c)
  | EVar _ | EQual _ -> true
  | _ -> not (touches a) && is_pure a.eff

(* Which arguments a call takes ownership of: [None] for all of them, which
   is what a definition of this program does.  An external borrows, except
   where the runtime says otherwise. *)
let call_owns (hd:expr) : ML (option (list bool)) =
  match hd.e with
  | EQual (n, _) -> HashTable.try_find !extern_tbl (string_of_name n)
  | _ -> None

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
  "FStar.String.strlen",     "cherry_str_length", [];
  "FStar.String.index",      "cherry_str_index", [];
  "FStar.String.sub",        "cherry_str_sub", [];
  "FStar.String.compare",    "cherry_str_compare", [];
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
(* The pass                                                             *)
(* -------------------------------------------------------------------- *)

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
  | EConst _ | EQual _ | EAny | EAbort _ -> e

  | ELet (x, t, e1, e2) ->
    let fv2 = without [x] (fv e2) in
    let fv1 = fv e1 in
    let o1, o2 = List.partition (fun (y, _) ->
                   List.mem y fv1 && not (List.mem y fv2)) o in
    let e1' = rc o1 e1 in
    let o2 = if is_np t then (x, t) :: o2 else o2 in
    let_ x t e1' (rc o2 e2)

  | ESeq (a, b) when is_np a.ty -> rc_live o (let_ (fresh ()) a.ty a b)
  | ESeq (a, b) ->
    let fvb = fv b in
    let o1, o2 = List.partition (fun (y, _) -> not (List.mem y fvb)) o in
    seq (rc o1 a) (rc o2 b)

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
       call o (call_owns hd) args e)
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
       let r = fresh () in
       let body = decs o (var r e.ty) in
       let body = if is_np e.ty then seq (rc_op RcInc r e.ty) body else body in
       let_ r e.ty e body)

  (* A loop runs its body any number of times, so it consumes nothing: what it
     reads it borrows, and what it allocates it releases before it goes round
     again.  The references it was given are released after it. *)
  | EWhile (c, b) ->
    let w = { e with e = EWhile (rc [] c, rc [] b); eff = E_Impure } in
    if Nil? o then w else
    let x = fresh () in
    let_ x e.ty w (decs o (var x e.ty))

  | EFun _ -> failwith "Cherry: a lambda survived lifting"
  | ETuple _ -> unsupported "an anonymous tuple of reference-counted values"
  | ERaise _ | ETry _ -> unsupported "an exception"

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
  let node = if owns = Some [] then node else { node with eff = E_Impure } in
  let call = incs extra node in
  if Nil? left then call else
  let r = fresh () in
  let_ r node.ty call (decs left (var r node.ty))

(* One branch.  [sc] is the scrutinee when it is a counted variable, and
   whether this match owns it.  Every field the branch uses is given a
   reference of its own before an owned scrutinee is released. *)
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
  | Some (x, _) ->
    let dead_x, dead_other = List.partition (fun (y, _) -> y = x) dead in
    let body = rc (keep @ fields) b in
    (p, g, decs dead_other (incs fields (decs dead_x body)))

let run_let (l:dlet) : ML dlet =
  current := string_of_name l.dl_name;
  let o = l.dl_binders |> List.filter (fun b -> is_np b.b_ty)
                       |> List.map (fun b -> (b.b_name, b.b_ty)) in
  if Nil? o && not (touches l.dl_body) then l else
  let body = rc o l.dl_body in
  { l with dl_body = body; dl_eff = join_eff l.dl_eff body.eff }

let run (p:program) : ML program =
  let np = HashTable.create 50 in
  nonplain_types p |> List.iter (fun k -> HashTable.add np k true);
  np_tbl := np;
  let ct = HashTable.create 50 in
  let rt = HashTable.create 50 in
  let xt = HashTable.create 50 in
  p |> List.iter (fun d ->
    match d with
    | DType ({ dt_body = TVariant cs }) ->
      cs |> List.iter (fun (c, fs) -> HashTable.add ct (string_of_name c) fs)
    | DType ({ dt_name = n; dt_body = TRecord fs }) ->
      HashTable.add rt (string_of_name n) fs
    | DExternal x ->
      let owns = match List.tryFind (fun (n, _, _) -> n = string_of_name x.dx_name)
                                    runtime_externals with
                 | Some (_, _, fl) -> fl
                 | None -> [] in
      HashTable.add xt (string_of_name x.dx_name) owns
    | _ -> ());
  ctor_tbl := ct; record_tbl := rt; extern_tbl := xt;
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
  let p = List.collect lift_decl p in
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
