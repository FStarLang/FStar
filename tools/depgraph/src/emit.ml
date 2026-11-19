(* Emission of the self-contained viewer package. *)

open Types

let ( ^/ ) = Filename.concat

(* ------------------------------------------------------------------ *)
(* JSON-ish serialisation (we only ever emit strings, ints and arrays) *)
(* ------------------------------------------------------------------ *)

let json_string (b : Buffer.t) (s : string) : unit =
  Buffer.add_char b '"';
  String.iter (fun c ->
    match c with
    | '"' -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | '\n' -> Buffer.add_string b "\\n"
    | '\r' -> Buffer.add_string b "\\r"
    | '\t' -> Buffer.add_string b "\\t"
    | '\b' -> Buffer.add_string b "\\b"
    | '\012' -> Buffer.add_string b "\\f"
    | c when Char.code c < 0x20 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
    (* U+2028/U+2029 are valid JSON but break JavaScript string literals *)
    | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"'

let jstr s = let b = Buffer.create (String.length s + 8) in json_string b s; Buffer.contents b

let jlist f l = "[" ^ String.concat "," (List.map f l) ^ "]"
let jstrs l = jlist jstr l

let mkdir_p (d : string) : unit =
  let rec go d =
    if d = "" || d = "/" || Sys.file_exists d then ()
    else (go (Filename.dirname d); try Unix.mkdir d 0o755 with _ -> ())
  in
  go d

let write_file (path : string) (contents : string) : unit =
  mkdir_p (Filename.dirname path);
  let oc = open_out_bin path in
  output_string oc contents;
  close_out oc

let read_file (path : string) : string option =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = really_input_string ic n in
    close_in ic; Some s
  with _ -> None

(* ------------------------------------------------------------------ *)

type ids = {
  mid   : (string, int) Hashtbl.t;    (* lowercase module name -> index *)
  mods  : Model.mod_rec array;
  did   : (string, int * int) Hashtbl.t;  (* lid -> (module index, def index) *)
  dlist : string array array;         (* module index -> lids in order *)
  fid   : (string, int) Hashtbl.t;    (* resolved source path -> file index *)
  files : (string * string) array;    (* (display name, path) *)
}

let unused_code (d : Model.def_rec) : int =
  if not d.Model.dr_reachable then 1
  else if d.Model.dr_indeg = 0 && not (List.mem "root" d.Model.dr_hints) then 2
  else 0

let build_ids (m : Model.model) : ids =
  let names = Hashtbl.fold (fun k _ acc -> k :: acc) m.Model.mods [] in
  let names = List.sort (fun a b ->
    let ra = (Hashtbl.find m.Model.mods a).Model.mr_name
    and rb = (Hashtbl.find m.Model.mods b).Model.mr_name in
    compare ra rb) names in
  let mid = Hashtbl.create 512 in
  List.iteri (fun i n -> Hashtbl.add mid n i) names;
  let mods = Array.of_list (List.map (Hashtbl.find m.Model.mods) names) in
  let dlist = Array.map (fun (mr : Model.mod_rec) -> Array.of_list mr.Model.mr_defs) mods in
  let did = Hashtbl.create 65536 in
  Array.iteri (fun i lids -> Array.iteri (fun j lid ->
    if not (Hashtbl.mem did lid) then Hashtbl.add did lid (i, j)) lids) dlist;
  (* source files *)
  let fid = Hashtbl.create 512 in
  let files = ref [] in
  let nfiles = ref 0 in
  let reg p =
    match Hashtbl.find_opt fid p with
    | Some i -> i
    | None ->
      let i = !nfiles in
      Hashtbl.add fid p i;
      files := (Filename.basename p, p) :: !files;
      incr nfiles; i
  in
  Array.iter (fun (mr : Model.mod_rec) ->
    (match mr.Model.mr_iface_src with Some p -> ignore (reg p) | None -> ());
    (match mr.Model.mr_impl_src with Some p -> ignore (reg p) | None -> ())) mods;
  { mid; mods; did; dlist; fid; files = Array.of_list (List.rev !files) }

let file_index (ids : ids) (p : string option) : int =
  match p with None -> -1 | Some p -> (match Hashtbl.find_opt ids.fid p with Some i -> i | None -> -1)

(* ------------------------------------------------------------------ *)
(* module-level edges induced by definition-level references           *)
(* ------------------------------------------------------------------ *)

let module_edges (m : Model.model) (ids : ids) : (int * int * int) list * (int * int) list =
  let tbl = Hashtbl.create 8192 in
  Hashtbl.iter (fun _ (d : Model.def_rec) ->
    match Hashtbl.find_opt ids.did d.Model.dr_lid with
    | None -> ()
    | Some (a, _) ->
      Hashtbl.iter (fun r () ->
        match Hashtbl.find_opt ids.did r with
        | Some (b, _) when b <> a ->
          let k = (a, b) in
          Hashtbl.replace tbl k (1 + (try Hashtbl.find tbl k with Not_found -> 0))
        | _ -> ()) d.Model.dr_refs)
    m.Model.defs;
  let used = Hashtbl.create 8192 in
  let edges = Hashtbl.fold (fun (a, b) w acc -> Hashtbl.replace used (a, b) (); (a, b, w) :: acc) tbl [] in
  (* declared dependencies that no definition actually uses *)
  let unused = ref [] in
  Array.iteri (fun i (mr : Model.mod_rec) ->
    List.iter (fun dep ->
      match Hashtbl.find_opt ids.mid dep with
      | Some j when j <> i && not (Hashtbl.mem used (i, j)) -> unused := (i, j) :: !unused
      | _ -> ()) mr.Model.mr_decl_deps) ids.mods;
  (List.sort compare edges, List.sort compare !unused)

(* ------------------------------------------------------------------ *)
(* emission                                                            *)
(* ------------------------------------------------------------------ *)

let now () =
  let t = Unix.localtime (Unix.time ()) in
  Printf.sprintf "%04d-%02d-%02d %02d:%02d"
    (t.Unix.tm_year + 1900) (t.Unix.tm_mon + 1) t.Unix.tm_mday t.Unix.tm_hour t.Unix.tm_min

let emit_module (m : Model.model) (ids : ids) (out : string) (i : int) : unit =
  let lids = ids.dlist.(i) in
  let idx_of = Hashtbl.create (Array.length lids) in
  Array.iteri (fun j l -> Hashtbl.replace idx_of l j) lids;
  let b = Buffer.create 65536 in
  Buffer.add_string b (Printf.sprintf "DG.setModule(%d,{defs:[" i);
  Array.iteri (fun j lid ->
    if j > 0 then Buffer.add_char b ',';
    let d = Hashtbl.find m.Model.defs lid in
    let line l = match l with Some (l : loc) -> l.l_line | None -> 0 in
    let eline l = match l with Some (l : loc) -> l.l_end_line | None -> 0 in
    Buffer.add_string b
      (Printf.sprintf "{n:%s,f:%s,k:%s,q:%s,h:%s,g:%d,l:%d,e:%d,il:%d,ie:%d,u:%d}"
         (jstr (Model.short_name lid)) (jstr lid) (jstr d.Model.dr_kind)
         (jstrs d.Model.dr_quals) (jstrs d.Model.dr_hints)
         (if d.Model.dr_generated then 1 else 0)
         (line d.Model.dr_impl_loc) (eline d.Model.dr_impl_loc)
         (line d.Model.dr_decl_loc) (eline d.Model.dr_decl_loc)
         (unused_code d))) lids;
  Buffer.add_string b "],e:[";
  let first = ref true in
  let out_edges = ref [] in
  Array.iteri (fun j lid ->
    let d = Hashtbl.find m.Model.defs lid in
    let seen = Hashtbl.create 16 in
    Hashtbl.iter (fun r () ->
      if not (Hashtbl.mem seen r) then begin
        Hashtbl.add seen r ();
        match Hashtbl.find_opt idx_of r with
        | Some k when k <> j ->
          if !first then first := false else Buffer.add_char b ',';
          Buffer.add_string b (Printf.sprintf "[%d,%d]" j k)
        | Some _ -> ()
        | None ->
          (match Hashtbl.find_opt ids.did r with
           | Some (mi, di) when mi <> i -> out_edges := (j, mi, di) :: !out_edges
           | _ -> ())
      end) d.Model.dr_refs) lids;
  Buffer.add_string b "],o:[";
  List.iteri (fun k (j, mi, di) ->
    if k > 0 then Buffer.add_char b ',';
    Buffer.add_string b (Printf.sprintf "[%d,%d,%d]" j mi di)) (List.rev !out_edges);
  Buffer.add_string b "],in:[";
  Buffer.add_string b "IN_PLACEHOLDER";
  Buffer.add_string b "]});\n";
  write_file (out ^/ "data" ^/ "m" ^/ (string_of_int i ^ ".js")) (Buffer.contents b)

(* Incoming cross-module edges have to be gathered globally, so modules are
   emitted in two passes. *)
let compute_incoming (m : Model.model) (ids : ids) : (int, (int * int * int) list ref) Hashtbl.t =
  let tbl = Hashtbl.create (Array.length ids.mods) in
  Array.iteri (fun i _ -> Hashtbl.add tbl i (ref [])) ids.mods;
  Array.iteri (fun i lids ->
    Array.iteri (fun j lid ->
      let d = Hashtbl.find m.Model.defs lid in
      let seen = Hashtbl.create 16 in
      Hashtbl.iter (fun r () ->
        if not (Hashtbl.mem seen r) then begin
          Hashtbl.add seen r ();
          match Hashtbl.find_opt ids.did r with
          | Some (mi, di) when mi <> i ->
            let l = Hashtbl.find tbl mi in
            l := (i, j, di) :: !l
          | _ -> ()
        end) d.Model.dr_refs) lids) ids.dlist;
  tbl

let emit_modules (m : Model.model) (ids : ids) (out : string) : unit =
  let incoming = compute_incoming m ids in
  Array.iteri (fun i _ ->
    emit_module m ids out i;
    let path = out ^/ "data" ^/ "m" ^/ (string_of_int i ^ ".js") in
    match read_file path with
    | None -> ()
    | Some s ->
      let inc = !(Hashtbl.find incoming i) in
      let bb = Buffer.create 1024 in
      List.iteri (fun k (mi, dj, di) ->
        if k > 0 then Buffer.add_char bb ',';
        Buffer.add_string bb (Printf.sprintf "[%d,%d,%d]" mi dj di)) inc;
      let idx = ref 0 in
      let pat = "IN_PLACEHOLDER" in
      let plen = String.length pat in
      let slen = String.length s in
      let found = ref (-1) in
      while !found < 0 && !idx + plen <= slen do
        if String.sub s !idx plen = pat then found := !idx else incr idx
      done;
      if !found >= 0 then
        write_file path
          (String.sub s 0 !found ^ Buffer.contents bb ^
           String.sub s (!found + plen) (slen - !found - plen)))
    ids.mods

let emit_index (cfg : Model.config) (m : Model.model) (ids : ids)
    (medges : (int * int * int) list) (unused_deps : (int * int) list)
    (unused : Model.unused_entry list) (out : string) : unit =
  let b = Buffer.create 262144 in
  Buffer.add_string b "DG.setIndex({v:1,generated:";
  Buffer.add_string b (jstr (now ()));
  Buffer.add_string b ",roots:";
  Buffer.add_string b (jstrs cfg.Model.c_roots);
  Buffer.add_string b ",mods:[";
  Array.iteri (fun i (mr : Model.mod_rec) ->
    if i > 0 then Buffer.add_char b ',';
    let nd = Array.length ids.dlist.(i) in
    let nu = Array.fold_left (fun acc lid ->
      let d = Hashtbl.find m.Model.defs lid in
      if unused_code d = 1 && not d.Model.dr_generated then acc + 1 else acc) 0 ids.dlist.(i) in
    Buffer.add_string b
      (Printf.sprintf "{n:%s,nd:%d,nu:%d,r:%d,s:%d,i:%d}"
         (jstr mr.Model.mr_name) nd nu (if mr.Model.mr_is_root then 1 else 0)
         (file_index ids mr.Model.mr_impl_src) (file_index ids mr.Model.mr_iface_src)))
    ids.mods;
  Buffer.add_string b "],medges:[";
  List.iteri (fun k (a, b', w) ->
    if k > 0 then Buffer.add_char b ',';
    Buffer.add_string b (Printf.sprintf "[%d,%d,%d]" a b' w)) medges;
  Buffer.add_string b "],unusedDeps:[";
  List.iteri (fun k (a, b') ->
    if k > 0 then Buffer.add_char b ',';
    Buffer.add_string b (Printf.sprintf "[%d,%d]" a b')) unused_deps;
  Buffer.add_string b "],files:[";
  Array.iteri (fun i (n, _) ->
    if i > 0 then Buffer.add_char b ',';
    Buffer.add_string b (Printf.sprintf "{n:%s}" (jstr n))) ids.files;
  let ndefs = Hashtbl.length m.Model.defs in
  let ndead = List.length (List.filter (fun (u : Model.unused_entry) -> u.Model.u_class = "dead") unused) in
  let nimp = List.length unused - ndead in
  Buffer.add_string b (Printf.sprintf "],stats:{modules:%d,defs:%d,dead:%d,implicit:%d,medges:%d}});\n"
    (Array.length ids.mods) ndefs ndead nimp (List.length medges));
  write_file (out ^/ "data" ^/ "index.js") (Buffer.contents b)

let emit_search (ids : ids) (m : Model.model) (out : string) : unit =
  let b = Buffer.create 1048576 in
  Buffer.add_string b "DG.setSearch([";
  let first = ref true in
  Array.iteri (fun i lids ->
    Array.iteri (fun j lid ->
      let d = Hashtbl.find m.Model.defs lid in
      if d.Model.dr_generated then () else begin
        if !first then first := false else Buffer.add_char b ',';
        Buffer.add_string b (Printf.sprintf "[%s,%d,%d,%s]" (jstr lid) i j (jstr d.Model.dr_kind))
      end) lids) ids.dlist;
  Buffer.add_string b "]);\n";
  write_file (out ^/ "data" ^/ "search.js") (Buffer.contents b)

let emit_unused_js (ids : ids) (unused : Model.unused_entry list) (out : string) : unit =
  let b = Buffer.create 262144 in
  let row (u : Model.unused_entry) with_why =
    match Hashtbl.find_opt ids.did u.Model.u_lid with
    | None -> None
    | Some (mi, di) ->
      let line = match u.Model.u_loc with Some (l : loc) -> l.l_line | None -> 0 in
      Some (Printf.sprintf "[%s,%d,%d,%s,%d%s]"
              (jstr (Model.short_name u.Model.u_lid)) mi di (jstr u.Model.u_kind) line
              (if with_why then "," ^ jstrs u.Model.u_why else ""))
  in
  let dead = List.filter_map (fun u -> if u.Model.u_class = "dead" then row u false else None) unused in
  let imp = List.filter_map (fun u -> if u.Model.u_class <> "dead" then row u true else None) unused in
  Buffer.add_string b "DG.setUnused({dead:[";
  Buffer.add_string b (String.concat "," dead);
  Buffer.add_string b "],implicit:[";
  Buffer.add_string b (String.concat "," imp);
  Buffer.add_string b "]});\n";
  write_file (out ^/ "data" ^/ "unused.js") (Buffer.contents b)

let emit_sources (ids : ids) (out : string) : int =
  let n = ref 0 in
  Array.iteri (fun i (name, path) ->
    match read_file path with
    | None -> ()
    | Some text ->
      incr n;
      let b = Buffer.create (String.length text + 64) in
      Buffer.add_string b (Printf.sprintf "DG.setSource(%d," i);
      json_string b text;
      Buffer.add_string b ");\n";
      write_file (out ^/ "data" ^/ "s" ^/ (string_of_int i ^ ".js")) (Buffer.contents b);
      ignore name) ids.files;
  !n

let emit_text_report (cfg : Model.config) (m : Model.model) (unused : Model.unused_entry list)
    (out : string) : unit =
  let b = Buffer.create 262144 in
  Buffer.add_string b "Unused definitions report\n";
  Buffer.add_string b "=========================\n\n";
  Buffer.add_string b (Printf.sprintf "generated : %s\n" (now ()));
  Buffer.add_string b (Printf.sprintf "roots     : %s\n" (String.concat ", " cfg.Model.c_roots));
  Buffer.add_string b (Printf.sprintf "modules   : %d\n" (Hashtbl.length m.Model.mods));
  Buffer.add_string b (Printf.sprintf "definitions: %d\n\n" (Hashtbl.length m.Model.defs));
  let show (u : Model.unused_entry) =
    let l = match u.Model.u_loc with
      | Some (l : loc) -> Printf.sprintf "%s:%d:%d" l.l_file l.l_line l.l_col
      | None -> "<no location>" in
    Printf.sprintf "  %-70s %-12s %s%s\n" u.Model.u_lid u.Model.u_kind l
      (if u.Model.u_why = [] then "" else "   [" ^ String.concat "," u.Model.u_why ^ "]")
  in
  let dead = List.filter (fun (u : Model.unused_entry) -> u.Model.u_class = "dead") unused in
  let imp = List.filter (fun (u : Model.unused_entry) -> u.Model.u_class <> "dead") unused in
  Buffer.add_string b (Printf.sprintf
    "1. Unreachable from the roots (%d)\n\
    \   These definitions cannot be reached from the root modules, nor from any\n\
    \   SMT-pattern lemma, typeclass instance, plugin, splice or top-level effect.\n\n"
    (List.length dead));
  List.iter (fun u -> Buffer.add_string b (show u)) dead;
  Buffer.add_string b (Printf.sprintf
    "\n2. Reachable only implicitly (%d)\n\
    \   Nothing refers to these syntactically; they survive only because of the\n\
    \   reason listed in brackets. Review them by hand.\n\n"
    (List.length imp));
  List.iter (fun u -> Buffer.add_string b (show u)) imp;
  write_file (out ^/ "unused-report.txt") (Buffer.contents b)

let readme (cfg : Model.config) (m : Model.model) (unused : Model.unused_entry list) : string =
  let dead = List.length (List.filter (fun (u : Model.unused_entry) -> u.Model.u_class = "dead") unused) in
  Printf.sprintf
"# F* dependence viewer

Generated on %s from roots: %s

* modules analysed  : %d
* definitions       : %d
* unreachable defs  : %d

## Viewing

Open `index.html` in any browser. The package is completely self-contained:
no network access and no web server are required, so it also works when the
files are opened directly from disk (the `file://` scheme).

If your browser is configured to forbid loading local scripts, run

    python3 serve.py

and open the printed URL instead.

## Contents

    index.html          the viewer
    assets/             stylesheet, layout engine, viewer code
    data/index.js       module list and module-level dependence graph
    data/m/<n>.js       per-module definitions and definition-level edges
    data/s/<n>.js       bundled source files
    data/search.js      search index over all definitions
    data/unused.js      the unused-definition report
    unused-report.txt   the same report as plain text

## Reading the graph

Edges point from a definition (or module) to what it uses. Start at the
namespace overview, double-click to descend into a namespace, then a module,
then a definition. Selecting a definition opens its source at the right line.
"
    (now ()) (String.concat ", " cfg.Model.c_roots)
    (Hashtbl.length m.Model.mods) (Hashtbl.length m.Model.defs) dead

let serve_py = "#!/usr/bin/env python3\n\
\"\"\"Serve this directory over http, for browsers that block local scripts.\"\"\"\n\
import http.server, socketserver, os, functools\n\
os.chdir(os.path.dirname(os.path.abspath(__file__)))\n\
h = functools.partial(http.server.SimpleHTTPRequestHandler)\n\
with socketserver.TCPServer((\"127.0.0.1\", 0), h) as httpd:\n\
    print(\"serving at http://127.0.0.1:%d/index.html\" % httpd.server_address[1])\n\
    httpd.serve_forever()\n"

let run (cfg : Model.config) (m : Model.model) (unused : Model.unused_entry list) : unit =
  let out = cfg.Model.c_outdir in
  mkdir_p out;
  let ids = build_ids m in
  let (medges, unused_deps) = module_edges m ids in
  if not cfg.Model.c_quiet then Printf.eprintf "Writing viewer to %s ...\n%!" out;
  write_file (out ^/ "index.html") Assets.index_html;
  write_file (out ^/ "assets" ^/ "viewer.css") Assets.viewer_css;
  write_file (out ^/ "assets" ^/ "layout.js") Assets.layout_js;
  write_file (out ^/ "assets" ^/ "viewer.js") Assets.viewer_js;
  write_file (out ^/ "serve.py") serve_py;
  emit_index cfg m ids medges unused_deps unused out;
  emit_modules m ids out;
  emit_search ids m out;
  emit_unused_js ids unused out;
  let nsrc = emit_sources ids out in
  emit_text_report cfg m unused out;
  write_file (out ^/ "README.md") (readme cfg m unused);
  if not cfg.Model.c_quiet then begin
    let dead = List.length (List.filter (fun (u : Model.unused_entry) -> u.Model.u_class = "dead") unused) in
    Printf.eprintf
      "  %d modules, %d definitions, %d module edges\n  %d unreachable, %d implicitly-live definitions\n  %d/%d source files bundled\n%!"
      (Array.length ids.mods) (Hashtbl.length m.Model.defs) (List.length medges)
      dead (List.length unused - dead) nsrc (Array.length ids.files)
  end

let package (cfg : Model.config) (file : string) : unit =
  let dir = Filename.dirname cfg.Model.c_outdir in
  let base = Filename.basename cfg.Model.c_outdir in
  let file = if Filename.is_relative file then Sys.getcwd () ^/ file else file in
  let cmd = Printf.sprintf "tar -czf %s -C %s %s"
      (Filename.quote file) (Filename.quote dir) (Filename.quote base) in
  if not cfg.Model.c_quiet then Printf.eprintf "Packaging: %s\n%!" cmd;
  match Sys.command cmd with
  | 0 -> Printf.eprintf "Wrote %s\n%!" file
  | n -> Printf.eprintf "tar failed with exit code %d; the viewer is still available in %s\n%!" n cfg.Model.c_outdir
