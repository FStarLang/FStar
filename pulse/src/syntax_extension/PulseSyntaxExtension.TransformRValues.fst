(*
   Copyright 2023 Microsoft Research

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

module PulseSyntaxExtension.TransformRValues
open FStar.Compiler.Effect
module Sugar = PulseSyntaxExtension.Sugar
module SW = PulseSyntaxExtension.SyntaxWrapper
module A = FStar.Parser.AST
module D = FStar.Syntax.DsEnv
module S = FStar.Syntax.Syntax
module L = FStar.Compiler.List
module U = FStar.Syntax.Util
module TcEnv = FStar.TypeChecker.Env
module SS = FStar.Syntax.Subst
module R = FStar.Compiler.Range
module BU = FStar.Compiler.Util
module P =  FStar.Syntax.Print
open FStar.Class.Show
open FStar.Class.HasRange
open FStar.Class.Monad
open FStar.Ident
open FStar.List.Tot
open PulseSyntaxExtension.Err
open PulseSyntaxExtension.Env

(* Local mutable variables are implicitly dereferenced *)


let mutvar_entry = (ident & S.bv & option ident)

type menv = {
  //Maps local mutable variables to an
  //immutable variable storing their current value
  map:list mutvar_entry;
  env:env_t
}

let menv_push_ns (m:menv) (ns:lid) = 
  { m with env = push_namespace m.env ns }

//
// auto_deref is not applicable for mutable local arrays
//
let menv_push_bv (m:menv) (x:ident) (q:option Sugar.mut_or_ref) (auto_deref_applicable:bool) =
  let env, bv = push_bv m.env x in
  let m = { m with env } in
  if q = Some Sugar.MUT && auto_deref_applicable
  then { m with map=(x, bv, None)::m.map }
  else m

let menv_push_bvs (m:menv) (xs:_) =
  { m with env = fst (push_bvs m.env xs) }

let is_mut (m:menv) (x:S.bv) : option (option ident) =
    match L.tryFind (fun (_, y, _) -> S.bv_eq x y) m.map with
    | None -> None
    | Some (_, _, curval) -> Some curval

let needs_derefs = list (ident & ident)

let fresh_var (nm:ident)
  : err ident
  = let! ctr = next_ctr in
    let s = show nm ^ "@" ^ show ctr in
    return (Ident.mk_ident (s, Ident.range_of_id nm))

let bind_curval (m:menv) (x:ident) (curval:ident) = 
  match L.tryFind (fun (y, _, _) -> Ident.ident_equals x y) m.map with
  | None -> failwith "Impossible 1"
  | Some (x, bv, _) -> { m with map=(x, bv, Some curval)::m.map }

let clear_curval (m:menv) (x:ident) =
  match L.tryFind (fun (y, _, _) -> Ident.ident_equals x y) m.map with
  | None -> failwith "Impossible 2"
  | Some (x, bv, _) -> { m with map=(x, bv, None)::m.map }

let bind_curvals (m:menv) (l:needs_derefs) = 
  L.fold_left 
    (fun m (x, y) -> bind_curval m x y)
    m l


let resolve_mut (m:menv) (e:A.term)
  : option mutvar_entry
  = let open A in
    match e.tm with
    | Var l -> (
      let topt = FStar.Syntax.DsEnv.try_lookup_lid m.env.tcenv.dsenv l in
      match topt with
      | Some {n=S.Tm_name x} -> 
        L.tryFind (fun (_, y, _) -> S.bv_eq x y) m.map 
      | _ -> None
    )
    | _ -> None

let maybe_clear_curval (m:menv) (x:A.term)
  : menv
  = match resolve_mut m x with
    | None -> m
    | Some (x, y, _) -> { m with map = (x, y, None)::m.map }


let read (x:ident) = 
  let open A in
  let range = Ident.range_of_id x in
  let level = Un in
  let head : A.term = {tm = Var op_bang_lid; range; level} in
  let arg = {tm = Var (Ident.lid_of_ids [x]); range; level} in
  {tm = App (head, arg, Nothing); range; level}

let add_derefs_in_scope (n:needs_derefs) (p:Sugar.stmt)
  : Sugar.stmt
  = L.fold_right
       (fun (x, y) (p:Sugar.stmt) ->
         let lb : Sugar.stmt =
           { s=Sugar.LetBinding { qualifier=None; id=y; typ=None;
                                  init=Some (Sugar.Default_initializer (read x)) };
             range=p.range } in
         { s=Sugar.Sequence { s1=lb; s2=p }; range=p.range})
       n p

let term'_of_id (y:ident) = A.Var (Ident.lid_of_ids [y])

let rec transform_term (m:menv) (e:A.term) 
  : err (A.term & needs_derefs & menv)
  = let open A in
    match e.tm with
    | Var _ -> (
      match resolve_mut m e with
      | None -> return (e, [], m)
      | Some (x, _, None) ->
        let! y = fresh_var x in
        return ({e with tm=Var (Ident.lid_of_ids [y])}, [x, y], bind_curval m x y)
      | Some (_, _, Some y) ->
        return ({e with tm=Var (Ident.lid_of_ids [y])}, [], m)
    )
    | Op(id, tms) ->
      let! tms, needs, m =
        tms |> 
        foldM_left
          (fun (tms, needs, m) tm ->
            let! tm, needs', m' = transform_term m tm in
            return (tm::tms, needs@needs', m'))
          ([], [], m)
      in
      let e = { e with tm = Op(id, L.rev tms) } in
      return (e, needs, m)

    | App (head, arg, imp) ->
      let! head, needs, m = transform_term m head in
      let! arg, needs', m = transform_term m arg in
      let e = { e with tm = App (head, arg, imp) } in
      return (e, needs@needs', m)
      
    | Ascribed (e, t, topt, b) ->
      let! e, needs, m = transform_term m e in
      let e = { e with tm = Ascribed (e, t, topt, b) } in
      return (e, needs, m)

    | Paren e ->
      let! e, needs, m = transform_term m e in
      let e = { e with tm = Paren e } in
      return (e, needs, m)    
    
    | Construct (lid, tms) ->
      let! tms, needs, m =
        tms |>
        foldM_left
          (fun (tms, needs, m) (tm, imp) ->
            let! tm, needs', m' = transform_term m tm in
            return ((tm, imp)::tms, needs@needs', m'))
          ([], [], m)
      in
      let e = { e with tm = Construct(lid, L.rev tms) } in
      return (e, needs, m)

    | LetOpen (l, t) ->
      let m = menv_push_ns m l in
      let! p, needs, _ = transform_term m t in
      return (p, needs, bind_curvals m needs)
    
    | _ -> return (e, [], m)
    

let rec transform_stmt_with_reads (m:menv) (p:Sugar.stmt)
  : err (Sugar.stmt & needs_derefs & menv)
  = let open Sugar in
    match p.s with
    | Sequence { s1; s2 } -> (
      let! (s1, needs, m) = transform_stmt_with_reads m s1 in
      let! s2 = transform_stmt m s2 in
      let p = { p with s=Sequence { s1; s2 }} in      
      return (p, needs, m)
    )
    
    | Open l ->
      return (p, [], menv_push_ns m l)

    | Expr { e } -> 
      let! e, needs, _ = transform_term m e in
      let p = { p with s = Expr { e }} in
      return (p, needs, m)

    | Assignment { lhs; value } ->
      let! value, needs, m = transform_term m value in
      let m = maybe_clear_curval m lhs in
      let s1 = { p with s = Assignment {lhs; value} } in
      return (s1, needs, m)

    | ArrayAssignment { arr; index; value } ->
      let! arr, arr_needs, m = transform_term m arr in
      let! index, index_needs, m = transform_term m index in
      let! value, value_needs, m = transform_term m value in
      let p = { p with s=ArrayAssignment {arr;index;value} } in
      return (p, arr_needs@index_needs@value_needs, m)

    | LetBinding { qualifier; id; typ; init } -> (
      let! init, needs, m =
          match init with
          | None -> return (None, [], m)
          | Some (Default_initializer e) -> (
            let mk_init e = Some (Default_initializer e) in
            match e.tm with
            | A.Var zlid -> (
              match qualifier, Ident.ids_of_lid zlid with
              | None, [z] -> (
                match resolve_mut m e with
                | None -> return (mk_init e, [], m)
                | Some (_, _, Some y) ->
                  return (mk_init { e with A.tm =term'_of_id y }, [], m)
                | Some (x, _, None) ->
                  return (mk_init (read x), [], bind_curval m x z)
              )
              | _ ->
                let! init, needs, m = transform_term m e in
                return (mk_init init, needs, m)
            )
            | _ ->
              let! init, needs, m = transform_term m e in
              return (mk_init init, needs, m)
            )
          | Some (Array_initializer {init; len}) ->
            let! init, needs, m = transform_term m init in
            let! len, len_needs, m = transform_term m len in
            return (Some (Array_initializer {init; len}), needs@len_needs, m)
          | Some (Lambda_initializer { range }) ->
            fail "Lambdas are not yet supported" range
      in
      let auto_deref_applicable =
        match init with
        | Some (Array_initializer _) -> false
        | _ -> true in
      let m = menv_push_bv m id qualifier auto_deref_applicable in
      let p = { p with s=LetBinding { qualifier; id; typ; init } } in
      return (p, needs, m)
      )

    | Block { stmt } ->
      let! stmt = transform_stmt m stmt in
      let p = { p with s=Block { stmt } } in
      return (p, [], m)

    | If { head; join_slprop; then_; else_opt } ->
      let! head, needs, m = transform_term m head in
      let! then_ = transform_stmt m then_ in
      let! else_opt =
        match else_opt with
        | None ->
          return None
        | Some else_ ->
          let! else_ = transform_stmt m else_ in
          return (Some else_)
      in
      let p = { p with s=If {head;join_slprop;then_;else_opt} } in
      return (p, needs, m)

    | Match { head; returns_annot; branches } ->
      let! head, needs, m = transform_term m head in
      let! branches = 
        branches |>
        mapM
          (fun (p, s) ->
            let! vs = pat_vars p in
            let m = menv_push_bvs m vs in
            let! s = transform_stmt m s in
            return (p, s))
      in
      let p = { p with s = Match { head; returns_annot; branches } } in
      return (p, needs, m)

    | While { guard; id; invariant; body } ->
      let! guard = transform_stmt m guard in
      let! body = transform_stmt m body in
      let p = { p with s = While { guard; id; invariant; body } } in
      return (p, [], m)


    | Parallel { p1; p2; q1; q2; b1; b2} ->
      let! b1 = transform_stmt m b1 in
      let! b2 = transform_stmt m b2 in
      let p = { p with s = Parallel { p1; p2; q1; q2; b1; b2 } } in
      return (p, [], m)    
    
    | Introduce _ 
    | ProofHintWithBinders _ ->
      //This is a proof step; no implicit dereference
      return (p, [], m)


and transform_stmt (m:menv) (p:Sugar.stmt)
  : err Sugar.stmt
  = let open Sugar in
    let! p, needs, m = transform_stmt_with_reads m p in
    return (add_derefs_in_scope needs p)      

let transform e p = transform_stmt { map=[]; env=e } p