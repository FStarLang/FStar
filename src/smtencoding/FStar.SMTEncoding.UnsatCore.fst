module FStar.SMTEncoding.UnsatCore
open FStar.Compiler.Effect
open FStar
open FStar.Compiler
open FStar.SMTEncoding.Term
module BU = FStar.Compiler.Util

let filter (core:unsat_core) (decls:list decl)
: list decl
= let rec aux theory =
    //so that we can use the tail-recursive fold_left
    let theory_rev = List.rev theory in
    let keep, n_retained, n_pruned =
        List.fold_left 
        (fun (keep, n_retained, n_pruned) d ->
          match d with
          | Assume a ->
              if List.contains a.assumption_name core
              then d::keep, n_retained+1, n_pruned
              else if BU.starts_with a.assumption_name "@"
              then d::keep, n_retained, n_pruned
              else keep, n_retained, n_pruned+1
          | Module (name, decls) ->
              let keep', n, m = aux decls in
              Module(name, keep')::keep, n_retained + n, n_pruned + m
          | _ -> d::keep, n_retained, n_pruned)
        ([Caption ("UNSAT CORE USED: " ^ (core |> String.concat ", "))],//start with the unsat core caption at the end
        0,
        0)
        theory_rev
    in
    keep, n_retained, n_pruned
  in
  let keep, _, _ = aux decls in
  keep
