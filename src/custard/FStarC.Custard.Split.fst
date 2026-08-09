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

module FStarC.Custard.Split

open FStarC
open FStarC.Effect
open FStarC.Custard.Syntax

module BU  = FStarC.Util
module Builtins = FStarC.Custard.Builtins
module Dep = FStarC.Parser.Dep
module SMap = FStarC.SMap

let module_of (n:name) : ML string =
  match n.ns with
  | [] -> "Custard"
  | ns -> String.concat "." ns

(* F\*'s own module order, as a rank per module: [m] follows everything it
   depends on.  Post-order depth-first search over [Dep.deps_of_modul], which
   is the same graph the driver loaded the checked files from, so a module
   Custard reached is a module this can rank.  One it did not reach -- a
   namespace that is not a module, or a realization whose dependencies were
   never collected -- ranks 0, which places it before everything and is
   exactly what a leaf deserves.

   The graph is acyclic, so no cycle detection is needed; the [busy] marker is
   there only to keep a malformed graph from looping. *)
let module_ranks (deps:Dep.deps) (ms : list string) : ML (SMap.t int) =
  let rank : SMap.t int = SMap.create 100 in
  let busy : SMap.t unit = SMap.create 100 in
  let next : ref int = mk_ref 1 in
  let rec visit (m:string) : ML int =
    match SMap.try_find rank m with
    | Some r -> r
    | None ->
      if Some? (SMap.try_find busy m) then 0
      else begin
        SMap.add busy m ();
        let _ = Dep.deps_of_modul deps m |> List.iter (fun d -> let _ = visit d in ()) in
        (* Assigned on the way *out*, so a module's rank exceeds every rank
           handed out while its dependencies were being visited. *)
        let r = !next in
        next := r + 1;
        SMap.add rank m r;
        r
      end in
  let _ = ms |> List.iter (fun m -> let _ = visit m in ()) in
  rank

(* The members of a recursive group have to stay together -- they are printed
   as one [let rec ... and ...] -- and they refer to each other, so the "every
   reference is already earlier in the list" invariant does not hold inside
   one.  [Simplify.scc] has already made them adjacent and tagged each with
   the group's members, so grouping is a matter of cutting the list where the
   tag changes. *)
let group_of (d:decl) : ML (option (list string)) =
  match decl_flags d |> List.tryFind Rec? with
  | Some (Rec ns) -> Some (List.map string_of_name ns)
  | _ -> None

let groups (prog:program) : ML (list (list decl)) =
  let rec go (acc : list decl) (g : option (list string)) (ds : list decl)
      : ML (list (list decl)) =
    match ds with
    | [] -> if acc = [] then [] else [List.rev acc]
    | d :: rest ->
      let g' = group_of d in
      if acc <> [] && Some? g' && g' = g
      then go (d :: acc) g' rest
      else (if acc = [] then [] else [List.rev acc]) @ go [d] g' rest in
  go [] None prog

(* Whether a declaration turns into target code.  A reference is not a
   definition: an external resolves to a hand-written realization and a
   realized type to the realization's own, so neither constrains where
   anything can go, and neither may pull a relocated declaration into a file
   that the realization already occupies. *)
let emits (d:decl) : ML bool =
  None? (imported_unit d) &&
  (match d with
   | DExternal _ -> false
   | DType t -> not (has_flag t.dt_flags Realized)
   | _ -> true)

(* A realized module already has a [.ml], and a few of its symbols are
   compiled anyway: [Prims.pow2] and [FStar.List.Tot.Base.map] have F* bodies
   and no rule claiming them, so Custard emits its own copies.  They cannot go
   in the file the realization occupies, and they are not what anything else
   refers to that module by, so they go in a file of their own -- under
   mangled names, since nothing there is at home. *)
let file_of (m:string) : ML string =
  if Builtins.is_realized_module (String.split ['.'] m)
  then "Custard." ^ m else m

let run (deps:Dep.deps) (prog:program) : ML (list (string & program)) =
  let gs = groups prog in
  let mods = prog |> List.map (fun d -> module_of (name_of_decl d)) in
  let rank = module_ranks deps mods in
  let rank_of (m:string) : ML int =
    match SMap.try_find rank m with Some r -> r | None -> 0 in
  (* A reference to a constructor is a reference to its declaration. *)
  let own = Simplify.ctor_owners prog in
  let resolve (n:string) : ML string =
    match SMap.try_find own n with Some o -> o | None -> n in
  (* The file each declaration ended up in, by [string_of_name] key. *)
  let home : SMap.t string = SMap.create 100 in
  let chunks : SMap.t (ref (list decl)) = SMap.create 100 in
  let emit (m:string) (ds : list decl) : ML unit =
    let r = match SMap.try_find chunks m with
            | Some r -> r
            | None -> let r = mk_ref [] in SMap.add chunks m r; r in
    r := List.rev ds @ !r in
  gs |> List.iter (fun (g : list decl) ->
    (* The group's own module, and the home of everything it references.
       References inside the group resolve to nothing yet, which is right:
       they impose no constraint the members do not already impose jointly. *)
    let cands =
      (g |> List.collect (fun d ->
             if emits d then [module_of (name_of_decl d)] else [])) @
      (g |> List.collect (fun d ->
             Simplify.decl_deps d |> List.collect (fun n ->
               match SMap.try_find home (resolve n) with
               | Some m -> [m]
               | None -> []))) in
    let seed = match cands with
               | m :: _ -> m
               | [] -> module_of (name_of_decl (List.hd g)) in
    let best = cands |> List.fold_left (fun acc m ->
                 if rank_of m > rank_of acc then m else acc) seed in
    let _ = g |> List.iter (fun d ->
              if emits d then SMap.add home (string_of_name (name_of_decl d)) best) in
    emit best g);
  (* Emitting in rank order is what makes every cross-file reference point
     backwards; within a file the extraction order is preserved untouched. *)
  let names = SMap.keys chunks in
  let names = BU.sort_with (fun a b -> rank_of a - rank_of b) names in
  names |> List.collect (fun m ->
    let ds = match SMap.try_find chunks m with
             | Some r -> List.rev !r
             | None -> [] in
    if ds = [] then [] else [(file_of m, ds)])
