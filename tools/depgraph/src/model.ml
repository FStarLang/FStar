(* Whole-program model: load the transitive closure of checked files from a
   set of roots, merge interface/implementation views of each definition,
   build the dependence graphs and run the unused-definition analysis. *)

open Types

let ( ^/ ) = Filename.concat

type config = {
  c_roots       : string list;      (* module names as given by the user *)
  c_includes    : string list;
  c_sources     : string list;
  c_outdir      : string;
  c_include_generated : bool;
  c_quiet       : bool;
}

type def_rec = {
  mutable dr_lid       : string;
  mutable dr_module    : string;
  mutable dr_kind      : string;
  mutable dr_quals     : string list;
  mutable dr_impl_loc  : loc option;
  mutable dr_decl_loc  : loc option;
  mutable dr_refs      : (string, unit) Hashtbl.t;
  mutable dr_children  : string list;
  mutable dr_generated : bool;
  mutable dr_attrs     : string list;
  mutable dr_order     : int;          (* source order within the module *)
  mutable dr_reachable : bool;
  mutable dr_indeg     : int;          (* number of distinct syntactic callers *)
  mutable dr_hints     : string list;
}

type mod_rec = {
  mutable mr_name     : string;
  mutable mr_lname    : string;
  mutable mr_defs     : string list;   (* lids, source order *)
  mutable mr_decl_deps: string list;   (* lowercase module names *)
  mutable mr_impl_src : string option; (* resolved path to .fst  *)
  mutable mr_iface_src: string option; (* resolved path to .fsti *)
  mutable mr_impl_file: string option; (* file name as in checked file *)
  mutable mr_iface_file: string option;
  mutable mr_is_root  : bool;
  mutable mr_missing  : bool;          (* no checked file found *)
}

type model = {
  defs   : (string, def_rec) Hashtbl.t;
  mods   : (string, mod_rec) Hashtbl.t;  (* keyed by lowercase module name *)
  order  : string list ref;              (* module load order (lowercase) *)
}

let new_model () = { defs = Hashtbl.create 4096; mods = Hashtbl.create 256; order = ref [] }

let lc = String.lowercase_ascii

let short_name (lid : string) : string =
  match String.rindex_opt lid '.' with
  | Some i -> String.sub lid (i + 1) (String.length lid - i - 1)
  | None -> lid

let module_of_lid (lid : string) : string =
  match String.rindex_opt lid '.' with
  | Some i -> String.sub lid 0 i
  | None -> ""

(* ------------------------------------------------------------------ *)
(* loading                                                             *)
(* ------------------------------------------------------------------ *)

let get_mod (m : model) (lname : string) : mod_rec =
  match Hashtbl.find_opt m.mods lname with
  | Some r -> r
  | None ->
    let r = { mr_name = lname; mr_lname = lname; mr_defs = []; mr_decl_deps = [];
              mr_impl_src = None; mr_iface_src = None; mr_impl_file = None;
              mr_iface_file = None; mr_is_root = false; mr_missing = false } in
    Hashtbl.add m.mods lname r;
    m.order := lname :: !(m.order);
    r

let add_entry (m : model) (mr : mod_rec) (order : int ref) (e : Analyze.raw_entry) : unit =
  List.iter (fun lid ->
    let is_iface_loc =
      match e.Analyze.r_loc with
      | Some l -> Filename.check_suffix l.l_file ".fsti"
      | None -> false
    in
    match Hashtbl.find_opt m.defs lid with
    | Some d ->
      (* Merge: a `val` in the interface and a `let` in the implementation
         describe the same definition. *)
      List.iter (fun r -> if not (Hashtbl.mem d.dr_refs r) then Hashtbl.add d.dr_refs r ())
        e.Analyze.r_refs;
      d.dr_children <- d.dr_children @ e.Analyze.r_children;
      d.dr_quals <- List.sort_uniq compare (d.dr_quals @ e.Analyze.r_quals);
      d.dr_attrs <- List.sort_uniq compare (d.dr_attrs @ e.Analyze.r_attr_lids);
      d.dr_generated <- d.dr_generated || e.Analyze.r_generated;
      (match e.Analyze.r_loc with
       | Some _ when is_iface_loc -> if d.dr_decl_loc = None then d.dr_decl_loc <- e.Analyze.r_loc
       | Some _ -> if d.dr_impl_loc = None then d.dr_impl_loc <- e.Analyze.r_loc
       | None -> ());
      (* a real definition wins over a bare declaration *)
      if d.dr_kind = "val" && e.Analyze.r_kind <> "val" then d.dr_kind <- e.Analyze.r_kind
    | None ->
      let tbl = Hashtbl.create (List.length e.Analyze.r_refs) in
      List.iter (fun r -> if not (Hashtbl.mem tbl r) then Hashtbl.add tbl r ()) e.Analyze.r_refs;
      let d = { dr_lid = lid;
                dr_module = mr.mr_name;
                dr_kind = e.Analyze.r_kind;
                dr_quals = e.Analyze.r_quals;
                dr_impl_loc = (if is_iface_loc then None else e.Analyze.r_loc);
                dr_decl_loc = (if is_iface_loc then e.Analyze.r_loc else None);
                dr_refs = tbl;
                dr_children = e.Analyze.r_children;
                dr_generated = e.Analyze.r_generated;
                dr_attrs = e.Analyze.r_attr_lids;
                dr_order = !order;
                dr_reachable = false;
                dr_indeg = 0;
                dr_hints = [] } in
      incr order;
      Hashtbl.add m.defs lid d;
      mr.mr_defs <- lid :: mr.mr_defs)
    e.Analyze.r_lids

let load_module (m : model) (ix : Analyze.index) (lname : string) : string list =
  let mr = get_mod m lname in
  let impl = Hashtbl.find_opt ix.Analyze.impl_checked lname in
  let iface = Hashtbl.find_opt ix.Analyze.iface_checked lname in
  (* The implementation's checked file already contains the interface's
     declarations, so it is enough on its own.  Interface-only modules are
     loaded from their .fsti.checked. *)
  let to_load = match impl with Some p -> [p] | None -> (match iface with Some p -> [p] | None -> []) in
  if to_load = [] then (mr.mr_missing <- true; [])
  else begin
    let order = ref 0 in
    let deps = ref [] in
    List.iter (fun path ->
      match Analyze.load_checked path with
      | None -> mr.mr_missing <- true
      | Some lo ->
        mr.mr_name <- lo.Analyze.lo_name;
        deps := lo.Analyze.lo_deps @ !deps;
        List.iter (add_entry m mr order) lo.Analyze.lo_entries)
      to_load;
    mr.mr_defs <- List.rev mr.mr_defs;
    mr.mr_decl_deps <- List.sort_uniq compare (List.filter (fun d -> d <> lname) !deps);
    (* Resolve source files by scanning the recorded ranges. *)
    List.iter (fun lid ->
      match Hashtbl.find_opt m.defs lid with
      | None -> ()
      | Some d ->
        (match d.dr_impl_loc with
         | Some l when mr.mr_impl_file = None -> mr.mr_impl_file <- Some l.l_file
         | _ -> ());
        (match d.dr_decl_loc with
         | Some l when mr.mr_iface_file = None -> mr.mr_iface_file <- Some l.l_file
         | _ -> ()))
      mr.mr_defs;
    mr.mr_impl_src <- (match mr.mr_impl_file with Some f -> Analyze.find_source ix f | None -> None);
    mr.mr_iface_src <- (match mr.mr_iface_file with Some f -> Analyze.find_source ix f | None -> None);
    mr.mr_decl_deps
  end

let load_all (cfg : config) (ix : Analyze.index) : model =
  let m = new_model () in
  let seen = Hashtbl.create 256 in
  let queue = Queue.create () in
  List.iter (fun r ->
    let l = lc r in
    if not (Hashtbl.mem seen l) then (Hashtbl.add seen l (); Queue.add l queue)) cfg.c_roots;
  let roots = List.map lc cfg.c_roots in
  let n = ref 0 in
  while not (Queue.is_empty queue) do
    let l = Queue.pop queue in
    incr n;
    if not cfg.c_quiet && !n mod 50 = 0 then
      (Printf.eprintf "\r  loaded %d modules..." !n; flush stderr);
    let deps = load_module m ix l in
    (get_mod m l).mr_is_root <- List.mem l roots;
    List.iter (fun d ->
      if not (Hashtbl.mem seen d) then (Hashtbl.add seen d (); Queue.add d queue)) deps
  done;
  if not cfg.c_quiet then (Printf.eprintf "\r  loaded %d modules.        \n" !n; flush stderr);
  m.order := List.rev !(m.order);
  m

(* ------------------------------------------------------------------ *)
(* liveness hints and reachability                                     *)
(* ------------------------------------------------------------------ *)

let has_attr (d : def_rec) (a : string) = List.mem a d.dr_attrs

let is_anon_toplevel (lid : string) =
  let n = short_name lid in
  String.length n >= 5 && String.sub n 0 5 = "uu___"

let compute_hints (m : model) : unit =
  Hashtbl.iter (fun _ (d : def_rec) ->
    let hints = ref [] in
    let add h = if not (List.mem h !hints) then hints := h :: !hints in
    (match Hashtbl.find_opt m.mods (lc d.dr_module) with
     | Some mr when mr.mr_is_root -> add "root"
     | _ -> ());
    if List.exists (fun p -> Hashtbl.mem d.dr_refs p) Analyze.smtpat_lids then add "smtpat";
    if has_attr d Analyze.tcinstance_lid then add "instance";
    if has_attr d Analyze.plugin_lid then add "plugin";
    if List.exists (fun a -> a = Analyze.tcresolve_lid) d.dr_attrs then add "instance";
    (match d.dr_kind with
     | "splice" -> add "splice"
     | "effect" | "sub_effect" | "effect_abbrev" -> add "effect"
     | _ -> ());
    if List.mem "action" d.dr_quals then add "effect";
    if is_anon_toplevel d.dr_lid then add "toplevel-effect";
    if d.dr_generated then add "generated";
    if List.mem "assume" d.dr_quals && not d.dr_generated
       && d.dr_kind = "assume" then add "axiom";
    d.dr_hints <- List.sort compare !hints)
    m.defs

(* A definition is an implicit root if something outside the syntactic
   dependence graph can reach it. *)
let is_implicit_root (d : def_rec) : bool =
  List.exists (fun h ->
    match h with
    | "root" | "smtpat" | "instance" | "plugin" | "splice" | "effect"
    | "toplevel-effect" | "axiom" -> true
    | _ -> false) d.dr_hints

let compute_reachability (m : model) : unit =
  let stack = ref [] in
  Hashtbl.iter (fun lid (d : def_rec) ->
    if is_implicit_root d then (d.dr_reachable <- true; stack := lid :: !stack)) m.defs;
  let rec loop () =
    match !stack with
    | [] -> ()
    | lid :: rest ->
      stack := rest;
      (match Hashtbl.find_opt m.defs lid with
       | None -> ()
       | Some d ->
         let visit r =
           match Hashtbl.find_opt m.defs r with
           | Some d' when not d'.dr_reachable -> d'.dr_reachable <- true; stack := r :: !stack
           | _ -> ()
         in
         Hashtbl.iter (fun r () -> visit r) d.dr_refs;
         (* A live inductive type keeps its constructors and projectors alive
            only if they are separately referenced, so `children` is *not*
            followed here.  Constructors do keep their type alive (recorded as
            an ordinary reference during extraction). *)
         ());
      loop ()
  in
  loop ()

let compute_indegrees (m : model) : unit =
  Hashtbl.iter (fun lid (d : def_rec) ->
    Hashtbl.iter (fun r () ->
      if r <> lid then
        match Hashtbl.find_opt m.defs r with
        | Some d' -> d'.dr_indeg <- d'.dr_indeg + 1
        | None -> ())
      d.dr_refs)
    m.defs

(* ------------------------------------------------------------------ *)
(* the unused report                                                   *)
(* ------------------------------------------------------------------ *)

type unused_entry = {
  u_lid    : string;
  u_module : string;
  u_kind   : string;
  u_quals  : string list;
  u_loc    : loc option;
  u_class  : string;   (* "dead" | "implicit" *)
  u_why    : string list;
}

let report (cfg : config) (m : model) : unused_entry list =
  let out = ref [] in
  Hashtbl.iter (fun _ (d : def_rec) ->
    let noisy = d.dr_generated || List.mem "generated" d.dr_hints in
    if noisy && not cfg.c_include_generated then ()
    else begin
      let loc = match d.dr_impl_loc with Some _ as l -> l | None -> d.dr_decl_loc in
      let mk cls why =
        out := { u_lid = d.dr_lid; u_module = d.dr_module; u_kind = d.dr_kind;
                 u_quals = d.dr_quals; u_loc = loc; u_class = cls; u_why = why } :: !out
      in
      if not d.dr_reachable then mk "dead" []
      else if d.dr_indeg = 0 && not (List.mem "root" d.dr_hints) then
        mk "implicit" (List.filter (fun h -> h <> "generated") d.dr_hints)
    end)
    m.defs;
  List.sort (fun a b ->
    let c = compare a.u_class b.u_class in
    if c <> 0 then c else
    let c = compare a.u_module b.u_module in
    if c <> 0 then c else
    match a.u_loc, b.u_loc with
    | Some x, Some y -> compare x.l_line y.l_line
    | _ -> compare a.u_lid b.u_lid) !out

let build (cfg : config) : model * unused_entry list =
  let ix = Analyze.new_index () in
  List.iter (Analyze.index_checked_dir ix) cfg.c_includes;
  List.iter (Analyze.index_source_dir ix) cfg.c_sources;
  if not cfg.c_quiet then
    Printf.eprintf "Indexed %d implementations, %d interfaces, %d source files.\n%!"
      (Hashtbl.length ix.Analyze.impl_checked)
      (Hashtbl.length ix.Analyze.iface_checked)
      (Hashtbl.length ix.Analyze.sources);
  let m = load_all cfg ix in
  compute_hints m;
  compute_reachability m;
  compute_indegrees m;
  (m, report cfg m)
