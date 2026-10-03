(* fstar-depgraph: a zoomable dependence viewer for F* projects. *)

let usage = {|
fstar-depgraph -- dependence viewer and unused-definition report for F* projects

Usage:
  fstar-depgraph --root MODULE [--root MODULE ...]
                 --include DIR  [--include DIR ...]
                 [--source DIR  [--source DIR ...]]
                 [--out DIR] [--package [FILE]] [--include-generated] [--quiet]

  --root M            a root module (e.g. FStarC.Main).  May be repeated.
  --include DIR       directory holding .checked files (searched recursively).
  --source DIR        directory holding .fst/.fsti sources (searched recursively).
                      Needed for source cross-linking; may be repeated.
  --out DIR           output directory (default: fstar-depgraph-out).
  --package [FILE]    also produce a self-contained .tar.gz of the viewer
                      (default: <out>.tar.gz).
  --include-generated report auto-generated projectors/discriminators too.
  --quiet             less chatter.
|}

let () =
  let roots = ref [] and incs = ref [] and srcs = ref [] in
  let out = ref "fstar-depgraph-out" in
  let package = ref None in
  let inc_gen = ref false and quiet = ref false in
  let args = Array.to_list Sys.argv in
  let rec parse = function
    | [] -> ()
    | "--root" :: v :: r -> roots := v :: !roots; parse r
    | "--include" :: v :: r -> incs := v :: !incs; parse r
    | "--source" :: v :: r -> srcs := v :: !srcs; parse r
    | "--out" :: v :: r -> out := v; parse r
    | "--package" :: v :: r when String.length v > 0 && v.[0] <> '-' ->
      package := Some (Some v); parse r
    | "--package" :: r -> package := Some None; parse r
    | "--include-generated" :: r -> inc_gen := true; parse r
    | "--quiet" :: r -> quiet := true; parse r
    | ("-h" | "--help") :: _ -> print_string usage; exit 0
    | a :: _ -> Printf.eprintf "Unrecognised argument: %s\n%s" a usage; exit 1
  in
  parse (List.tl args);
  if !roots = [] || !incs = [] then (print_string usage; exit 1);
  let cfg = { Model.c_roots = List.rev !roots;
              c_includes = List.rev !incs;
              c_sources = List.rev !srcs;
              c_outdir = !out;
              c_include_generated = !inc_gen;
              c_quiet = !quiet } in
  let (m, unused) = Model.build cfg in
  Emit.run cfg m unused;
  (match !package with
   | None -> ()
   | Some f ->
     let f = match f with Some f -> f | None -> !out ^ ".tar.gz" in
     Emit.package cfg f)
