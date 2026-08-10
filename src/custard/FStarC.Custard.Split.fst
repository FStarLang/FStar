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

(* The key a module ranks under.  Stub and counterpart share a slot:
   [Extract.unstub_lid] answers a request for [FStar.Stubs.Tactics.Types] with
   [FStarC.Tactics.Types], so as far as placement is concerned a dependency on
   the one is a dependency on the other.  Lowercased because that is how the
   dependency graph spells module names; spelled out rather than routed
   through {!Builtins.no_fstar_stubs}, which matches on the capitalised form. *)
let rank_key (m:string) : ML string =
  match String.split ['.'] (String.lowercase m) with
  | "fstar" :: "normsteps" :: rest -> String.concat "." ("fstarc" :: "normsteps" :: rest)
  | "fstar" :: "stubs" :: rest -> String.concat "." ("fstarc" :: rest)
  | _ -> String.lowercase m

(* F*'s own module order, as a rank per module.  This is only a tie-break: it
   decides the order of two modules that do not refer to each other, which the
   reference graph leaves free but which still matters, because the target
   modules are laid out in one flat directory and a hand-written realization
   may sit anywhere among them. *)
let source_ranks (deps:Dep.deps) : ML (SMap.t int) =
  let rank : SMap.t int = SMap.create 100 in
  let n : ref int = mk_ref 0 in
  Dep.topological_order deps rank_key |> List.iter (fun m ->
    n := !n + 1;
    SMap.add rank m !n);
  rank

(* Tarjan, iterative in the sense that matters: the components come out in
   dependency order, each after every component it refers to, which is exactly
   the order the files have to be emitted in.  A component with more than one
   member is a genuine cycle between modules; its members cannot be separate
   files and have to be merged. *)
let sccs (nodes : list string) (succ : string -> ML (list string))
  : ML (list (list string)) =
  let index : SMap.t int = SMap.create 100 in
  let low : SMap.t int = SMap.create 100 in
  let onstack : SMap.t bool = SMap.create 100 in
  let stack : ref (list string) = mk_ref [] in
  let next : ref int = mk_ref 0 in
  let out : ref (list (list string)) = mk_ref [] in
  let get (m:SMap.t int) (k:string) : ML int =
    match SMap.try_find m k with Some v -> v | None -> 0 in
  let rec go (v:string) : ML unit =
    SMap.add index v !next; SMap.add low v !next; next := !next + 1;
    stack := v :: !stack; SMap.add onstack v true;
    succ v |> List.iter (fun w ->
      if None? (SMap.try_find index w)
      then (go w; if get low w < get low v then SMap.add low v (get low w))
      else if Some true = SMap.try_find onstack w
      then (if get index w < get low v then SMap.add low v (get index w)));
    if get low v = get index v
    then begin
      let rec pop (acc : list string) : ML (list string) =
        match !stack with
        | [] -> acc
        | w :: rest ->
          stack := rest; SMap.add onstack w false;
          if w = v then w :: acc else pop (w :: acc) in
      out := pop [] :: !out
    end in
  nodes |> List.iter (fun v -> if None? (SMap.try_find index v) then go v);
  List.rev !out

(* Where each module sits in the output, and which module a cycle of modules
   collapses to.

   The order comes from the program's *own* reference graph, not from F*'s
   dependency graph.  The two agree wherever both say anything, but the source
   graph says nothing about a great deal that matters here: it records a
   dependency on an interface where the code that comes out refers to the
   implementation's contents, it does not know that [FStar.Stubs.X] and
   [FStarC.X] have become one module, and it has no opinion at all about the
   modules Custard synthesises.  Ranking by the references that are actually
   emitted makes the invariant the split relies on -- every reference points at
   an earlier file -- true by construction, so a declaration only ever has to
   leave its own module when it is caught in a real cycle between modules.

   [source_ranks] survives as the tie-break, and as the fallback for a module
   that emits nothing. *)
let module_ranks (deps:Dep.deps) (prog:program) : ML (SMap.t int) =
  let src = source_ranks deps in
  let src_of (m:string) : ML int =
    match SMap.try_find src (rank_key m) with Some r -> r | None -> 0 in
  (* Which module each declaration came from, constructors included. *)
  let owner : SMap.t string = SMap.create 100 in
  let ctors = Simplify.ctor_owners prog in
  let _ = prog |> List.iter (fun d ->
            SMap.add owner (string_of_name (name_of_decl d))
                           (module_of (name_of_decl d))) in
  let owner_of (n:string) : ML (option string) =
    let n = match SMap.try_find ctors n with Some o -> o | None -> n in
    SMap.try_find owner n in
  (* One node per module, edges to every module it refers to. *)
  let succ : SMap.t (list string) = SMap.create 100 in
  let seen : SMap.t bool = SMap.create 100 in
  let node (m:string) : ML unit =
    if None? (SMap.try_find seen m) then (SMap.add seen m true; SMap.add succ m []) in
  let _ = prog |> List.iter (fun d ->
            let m = module_of (name_of_decl d) in
            node m;
            Simplify.decl_deps d |> List.iter (fun n ->
              match owner_of n with
              | Some m' ->
                if m' <> m
                then begin
                  node m';
                  let es = match SMap.try_find succ m with Some es -> es | None -> [] in
                  if not (List.mem m' es) then SMap.add succ m (m' :: es)
                end
              | None -> ())) in
  (* Deterministic, and as close to F*'s order as the reference graph allows:
     visit the roots in source order, and each node's successors likewise. *)
  let by_source (a:string) (b:string) : ML int = src_of a - src_of b in
  let nodes = BU.sort_with by_source (SMap.keys succ) in
  let succ_of (m:string) : ML (list string) =
    match SMap.try_find succ m with
    | Some es -> BU.sort_with by_source es
    | None -> [] in
  let rank : SMap.t int = SMap.create 100 in
  let n : ref int = mk_ref 0 in
  (* Inside a component the modules do refer to each other in a cycle, so no
     order of them is right and one has to be picked: source order, which is
     the one the declarations are least likely to have to leave.  Whatever
     order it is, the declarations that would point forwards under it get
     relocated by {!run}, exactly as they did when every module was ranked this
     way.  Between components the order is forced, and nothing moves. *)
  let _ = sccs nodes succ_of |> List.iter (fun comp ->
            BU.sort_with by_source comp |> List.iter (fun m ->
              n := !n + 1; SMap.add rank m !n)) in
  (* A module that emits nothing is never a destination, but [rank_of] is
     still asked about it; put it after everything, in source order. *)
  let _ = BU.sort_with by_source (SMap.keys src) |> List.iter (fun m ->
            if None? (SMap.try_find rank m)
            then (n := !n + 1; SMap.add rank m !n)) in
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
  let rank = module_ranks deps prog in
  let rank_of (m:string) : ML int =
    match SMap.try_find rank m with
    | Some r -> r
    | None -> (match SMap.try_find rank (rank_key m) with Some r -> r | None -> 0) in
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
    let own = match cands with
              | m :: _ -> m
              | [] -> module_of (name_of_decl (List.hd g)) in
    let top = cands |> List.fold_left (fun acc m ->
                if rank_of m > rank_of acc then m else acc) own in
    (* Stay at home unless something forces the move.  Relocation exists for
       the declarations that cannot live in the module their name comes from
       -- a specialization of [show] at a type declared later, say -- and for
       nothing else: a declaration that has moved is reached under a mangled
       name in a foreign module, which is both unreadable and, for anything a
       hand-written realization calls by its plain name, wrong.  So the module
       the declaration came from wins whenever it is late enough to host every
       reference the group makes, and the highest-ranked candidate is a
       fallback rather than the rule. *)
    let best = if rank_of own >= rank_of top then own else top in
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
