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
module FStarC.Custard.Driver

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Custard.Syntax
open FStarC.Errors.Msg
open FStarC.Class.Show

module SMap  = FStarC.SMap
module BU    = FStarC.Util
module E     = FStarC.Errors
module Dep     = FStarC.Parser.Dep
module UF      = FStarC.Syntax.Unionfind
module C       = FStarC.Custard.PrintC
module Krml    = FStarC.Custard.PrintKrml
module Extract = FStarC.Custard.Extract
module Find    = FStarC.Find
module Layout  = FStarC.Custard.Layout
module Monomorphize = FStarC.Custard.Monomorphize
module OCaml   = FStarC.Custard.PrintOCaml
module Loader  = FStarC.Custard.Loader
module RegEmb  = FStarC.Custard.RegEmb
module Rename  = FStarC.Custard.Rename
module Simplify = FStarC.Custard.Simplify
module Split    = FStarC.Custard.Split
module Ident   = FStarC.Ident
module TcEnv   = FStarC.TypeChecker.Env
module Unit    = FStarC.Custard.Unit
module Prof    = FStarC.Custard.Prof

(* The roots.  Section 4.4: Custard compiles what is reachable from these and
   nothing else, so anything a *hand-written* file calls has to be named,
   since no request Custard can see reaches it.  [--custard_entry] names one;
   [--custard_entrypoints] names a file of them, which is how a plugin ships
   the list of compiler symbols its own realizations call (section 12.13). *)
let entrypoints_of_file (f:string) : ML (list string) =
  if not (FStarC.Filepath.file_exists f) then
    E.raise_error0 E.Error_CustardEntryNotFound [
      text ("Custard cannot read the entry-point file " ^ f ^ ".")
    ]
  else
    BU.file_get_lines f |> List.collect (fun line ->
      let line = BU.trim_string (List.hd (BU.split line "#")) in
      if line = "" then [] else [line])

let entrypoints () =
  (Options.custard_entrypoint_files () |> List.collect entrypoints_of_file)
  @ Options.custard_entries ()
  |> List.map Ident.lid_of_str

let main_entry () : ML (option Ident.lident) =
  match Options.custard_main () with
  | Some s -> Some (Ident.lid_of_str s)
  | None -> None

(* -------------------------------------------------------------------- *)
(* --custard_warn_any (sections 3 and 5.4)                              *)
(* -------------------------------------------------------------------- *)

(* The two ways Custard can lose track of what a value looks like at runtime.

   [TAny] is the analogue of the ML extraction's [MLTY_Top]: a type Custard
   could not work out.  Because the program is whole and monomorphic there is
   almost always an answer, so each occurrence is a place where something went
   wrong upstream -- and, unlike the ML extraction's [Obj.magic] sprinkles,
   one that can be pointed at.

   A surviving [ECoerce] is the other half.  Section 5.4 eliminates a coercion
   when the two sides have the same layout, and fuses nested ones; what is left
   is a coercion between representations Custard believes are genuinely
   different, which in OCaml is an [Obj.magic] and in C a reinterpretation.

   An [ECast] is never reported: it is not lost information at all but the
   width conversion the source asked for, a real call into [FStar.Int.Cast].
   Keeping the two apart in the IR is what makes that a matter of which node
   this is rather than of inspecting the types on either side.

   A coercion to or from [TAny] is not reported either.  It is the
   *consequence* of a [TAny], inserted by
   {!FStarC.Custard.Simplify.coerce_prog} at exactly the boundary where one
   meets a concrete type; the [TAny] itself is reported at the binder, field
   or result carrying it, and repeating the complaint once per use would bury
   it. *)
let lost_cast (e:expr) (t:cty) : bool =
  match e.ty, t with
  | TAny, _ | _, TAny -> false
  | _ -> true

let warn_any (prog:program) : ML unit =
  let sites : ref (list string) = mk_ref [] in
  let note (s:string) : ML unit = sites := s :: !sites in
  let rec any_cty (c:cty) : ML bool =
    match c with
    | TAny -> true
    | TArrow (a, _, b) -> any_cty a || any_cty b
    | TApp (_, args) -> args |> List.existsb any_cty
    | TTuple cs -> cs |> List.existsb any_cty
    | TBuf c | TRef c | TInline c -> any_cty c
    | TVar _ | TInt _ | TFloat _ | TUnit | TExn -> false in
  let at (where:string) (c:cty) : ML unit =
    if any_cty c then note ("the " ^ where ^ " has type " ^ show c) in
  let rec go (x:expr) : ML unit =
    (match x.e with
     | ECoerce (e1, t) when lost_cast e1 t ->
       note ("a coercion from " ^ show e1.ty ^ " to " ^ show t)
     | _ -> ());
    let sub (es:list expr) : ML unit = es |> List.iter go in
    match x.e with
    | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> ()
    | ELet (v, t, e1, e2) -> at ("binding of '" ^ v ^ "'") t; sub [e1; e2]
    | EApp (h, es) -> sub (h :: es)
    | EFun (bs, b) ->
      bs |> List.iter (fun (b:binder) -> at ("binder '" ^ b.b_name ^ "'") b.b_ty);
      go b
    | EMatch (sc, brs) -> go sc; brs |> List.iter go_branch
    | ETry (e, brs) -> go e; brs |> List.iter go_branch
    | EIf (c, a, b) -> sub [c; a; b]
    | ESeq (a, b) -> sub [a; b]
    | ECtor (_, es) | ETuple es | EOp (_, es) -> sub es
    | ERaise e1 -> go e1
    | ERecord (_, fs) -> sub (fs |> List.map snd)
    | EProj (e, _, _) | EDiscrim (e, _) -> go e
    | ECast (e, _) | ECoerce (e, _) -> go e
    | EWhile (c, b) -> sub [c; b]
  and go_branch (br:branch) : ML unit =
    let _, g, b = br in
    (match g with Some g -> go g | None -> ());
    go b in
  prog |> List.iter (fun d ->
    sites := [];
    (match d with
     | DLet l ->
       l.dl_binders |> List.iter (fun (b:binder) ->
         at ("binder '" ^ b.b_name ^ "'") b.b_ty);
       at "result" l.dl_ret;
       go l.dl_body
     | DType t ->
       let fields (owner:string) (fs:list (string & cty)) : ML unit =
         fs |> List.iter (fun (f, c) -> at ("field '" ^ owner ^ "." ^ f ^ "'") c) in
       (match t.dt_body with
        | TAbbrev c -> at "definition" c
        | TRecord fs -> fields (string_of_name t.dt_name) fs
        | TVariant cs ->
          cs |> List.iter (fun (cn, fs) -> fields (string_of_name cn) fs)
        | TAbstract -> ())
     | DExternal x -> at "declaration" x.dx_ty
     | DExn e -> e.de_args |> List.iter (at "exception argument"));
    (* Section 51.2.  An external with a type parameter is a particular and
       recognizable case of this, and the generic message did not say so: the
       reader is told the declaration's type has an [any] in it and left to
       work out that the reason is polymorphism.  It is worth naming because
       the answer is unusual -- monomorphization does not reach an external,
       and cannot, since one C symbol has one prototype -- and because the
       workaround is not obvious from the generic text. *)
    let extra =
      match d with
      | DExternal x when Cons? x.dx_typars ->
        [text ("'" ^ string_of_name x.dx_name ^ "' is external and \
                polymorphic, in " ^ show (List.length x.dx_typars) ^
               " type parameter(s): " ^ String.concat ", " x.dx_typars ^ ".");
         text "An external is never specialized.  Specialization works by \
               substituting into a body and an external has none, and its C \
               declaration is a single fixed symbol with a single prototype, \
               so there is nothing for a per-instantiation copy to be named. \
               Each type parameter therefore becomes [any].";
         text "Give the parameter a concrete type.  If the C target really \
               does accept several types -- a variadic macro, say -- declare \
               one external per type vector, all with the same \
               [@@custard_extern] target name."]
      | _ -> [] in
    match List.rev !sites with
    | [] -> ()
    | ss ->
      E.log_issue0 E.Warning_CustardLostRepresentation
        (text ("Custard lost the representation of " ^
               show (List.length ss) ^ " value(s) in '" ^
               string_of_name (name_of_decl d) ^ "':")
         :: (ss |> List.map (fun s -> text ("- " ^ s)))
         @ extra
         @ [text "A whole, monomorphic program mostly should not need these: \
                  each one is a place where the code generated to cross into \
                  and out of it is unchecked -- an Obj.magic in OCaml, a \
                  reinterpretation in C. Some are unavoidable, notably a class \
                  over a type constructor, which no OCaml type can name."]))

(* Check that every requested entry point actually resolves to a definition we
   can see.  Getting this wrong is by far the most likely user error, and the
   resulting "empty program" would otherwise be silent. *)
let check_entrypoints (deps:Dep.deps) (env:TcEnv.env) (roots:list Ident.lident) : ML unit =
  (* The extraction loop loads a module when it first reaches one of its
     definitions ({!FStarC.Custard.Loader}), so at this point the environment
     holds only what the driver happened to load: an entry in a module that is
     not loaded yet is not an error, and loading it here would clash with the
     interface the driver already has.  Those entries are checked after the
     fact instead, by {!Extract.run}, which reports one that produced no
     declaration.  What is worth catching early is a typo in a module the
     driver *did* load, which is the common case. *)
  roots |> List.iter (fun l ->
    (* A root may name a *module* rather than a definition (section 13.3), and
       then there is nothing to look up.  Checked first, because a module name
       need not have a namespace at all and [Ident.lid_of_ids] rejects the
       empty list. *)
    if Loader.module_is_loaded deps env (Ident.string_of_lid l) then () else
    let m = match Ident.ns_of_lid l with
            | [] -> ""
            | ns -> Ident.string_of_lid (Ident.lid_of_ids ns) in
    if m = "" || Loader.module_is_loaded deps env m then
      match TcEnv.lookup_sigelt env l with
      | Some _ -> ()
      | None ->
        E.log_issue0 E.Error_CustardEntryNotFound [
          text ("Custard entry point " ^ Ident.string_of_lid l ^ " is not in scope.");
          text "Make sure the module defining it is among the input files."
        ])

(* -------------------------------------------------------------------- *)
(* Unit interfaces (section 12)                                         *)
(* -------------------------------------------------------------------- *)

let imported_type_infos (imports:list (decl & option type_info))
  : ML (list (dtype & type_info)) =
  imports |> List.collect (fun (d, ti) ->
    match d, ti with
    | DType dt, Some ti -> [(dt, ti)]
    | _ -> [])

(* The imported declarations, which [Simplify] reads but never rewrites: a
   type's representation is settled and reaches it in the [verdicts], and a
   value's declared type is a boundary that a coercion may have to be inserted
   at (section 5.4). *)
let imported_decls (imports:list (decl & option type_info)) : ML (list decl) =
  imports |> List.map fst

(* What a unit exports.  Everything it emits, so that a downstream unit never
   has to compile any of it again -- including the re-specializations it made
   of *its* upstream's definitions, which are just as much this unit's code as
   anything else it emitted (section 12.6).

   [Inline] declarations are the exception, and are excluded rather than
   forgotten: they are the projectors and discriminators that are substituted
   at their uses and never emitted at all, so exporting one would name a symbol
   that does not exist.  A downstream unit re-derives them, which costs
   nothing.

   A [DLet]'s body is dropped.  A `.cui` is an interface: what a downstream
   unit needs is the name to call and the signature to call it at.  Keeping the
   body would invite exactly the thing separate compilation is here to prevent. *)
let unit_entries (keys:list (string & string)) (homes:SMap.t string)
                 (prog:program) (infos:list (name & type_info))
  : ML (list Unit.entry) =
  (* Both lookups are once per declaration over a list as long as the program,
     which is quadratic in it and was the second-largest phase of extracting
     the compiler (section 12.14).  Indexing them first makes it linear. *)
  let key_map : SMap.t string = SMap.create 100 in
  (* [tryPick] takes the first match, so a later duplicate must not win. *)
  keys |> List.iter (fun (n', k) ->
    if None? (SMap.try_find key_map n') then SMap.add key_map n' k);
  let info_map : SMap.t type_info = SMap.create 100 in
  infos |> List.iter (fun (n', ti) ->
    let k = string_of_name n' in
    if None? (SMap.try_find info_map k) then SMap.add info_map k ti);
  let key_of (n:name) : ML (option string) =
    SMap.try_find key_map (string_of_name n) in
  let info_of (n:name) : ML (option type_info) =
    SMap.try_find info_map (string_of_name n) in
  prog |> List.collect (fun d ->
    if has_flag (decl_flags d) Inline || Some? (imported_unit d) then [] else
    (* An external is a hole this unit *leaves*, not a symbol it provides: a
       hand-written realization defines it, or -- as with Pulse's checker,
       whose copy of [PulseSyntaxExtension.ASTBuilder.fsti] has no [.fst] --
       another Custard unit does.  Exporting it would tell a downstream unit
       the symbol is already compiled, and that unit would then skip the very
       definition it was there to contribute; the link would come out with a
       reference and nothing to resolve it against.  A downstream unit derives
       an external's signature from the source anyway, exactly as this one
       did, so nothing is lost by leaving it out. *)
    if DExternal? d then [] else
    (* Section 42.1.  A C unit's interface is its linking interface: what the
       header declares and nothing else.  A [static] definition offered here
       would be a symbol the consumer cannot name.  Types are all kept, since
       the header carries the whole type language -- and because that is what
       keeps two headers from defining one [struct] twice (section 42.2). *)
    if Options.custard_backend () = "C"
       && (match d with DLet dl -> not (C.is_public dl) | _ -> false)
    then [] else
    let d, ti =
      match d with
      | DLet dl -> DLet { dl with dl_body = unit_expr }, None
      | DType dt -> d, info_of dt.dt_name
      | _ -> d, None in
    match key_of (name_of_decl d) with
    (* A declaration no request created -- a lambda-lifted local function, say
       -- has no key for a downstream unit to recognize it by, and so cannot be
       exported.  It is still emitted; it is just not reusable. *)
    | None -> []
    | Some k -> [{ Unit.ue_key = k; Unit.ue_decl = d; Unit.ue_type = ti;
                   Unit.ue_home =
                     SMap.try_find homes (string_of_name (name_of_decl d)) }])

let write_unit_iface (st:Extract.state) (homes:SMap.t string)
                     (hdr_file:option string) (init:option string)
                     (prog:program) (infos:list (name & type_info))
  : ML unit =
  match Options.custard_unit () with
  | None -> ()
  | Some u ->
    let i = {
      Unit.ui_header = {
        Unit.uh_version = Unit.current_version;
        Unit.uh_name    = u;
        Unit.uh_backend = Options.custard_backend ();
        Unit.uh_options = Unit.layout_options ();
        Unit.uh_digests = Extract.loaded_digests st;
        Unit.uh_header  = hdr_file;
        Unit.uh_init    = init;
      };
      Unit.ui_entries = unit_entries (Extract.exported_keys st) homes prog infos;
    } in
    if Options.custard_dump_cui () then
      Format.print_string (Unit.iface_to_string i);
    Unit.write_iface (Find.prepend_output_dir (u ^ ".cui")) i

(* Every phase of section 1.1 is a counter, so that
   [--profile_component FStarC.Custard] answers "where did the time go" for a
   whole-program extraction without a rebuild.  See section 12.14. *)
let phase (name:string) (f : unit -> ML 'a) : ML 'a = Prof.timed name f

let run_phases (deps:Dep.deps) (env:TcEnv.env) : ML unit =
  let main = main_entry () in
  (* [--custard_main] is a root too, so that the common case needs only one
     option. *)
  let roots = entrypoints () @ (match main with Some l -> [l] | None -> []) in
  if Nil? roots && Nil? (Options.custard_entry_modules ()) then
    E.raise_error0 E.Fatal_OptionsNotCompatible [
      text "--codegen Custard requires at least one --custard_entry, \
            --custard_entry_module or --custard_main.";
      text "Custard is a whole-program compiler: it extracts exactly the \
                   definitions reachable from the entry points."
    ];
  phase "entrypoints" (fun () -> check_entrypoints deps env roots);
  (* Section 42.5.  The C backend links now; karamel does its own bundling and
     has its own opinion about what a compilation unit is, so wiring a `.cui`
     into it would be answering a question nobody has asked.  Failing here is
     better than emitting a file that refers to symbols nothing declares. *)
  if (Some? (Options.custard_unit ()) || Cons? (Options.custard_links ()))
     && Options.custard_backend_krml () then
    E.raise_error0 E.Fatal_OptionsNotCompatible [
      text "Separate compilation (--custard_unit, --custard_link) is not \
            implemented for the karamel backends.";
      text "Use --custard_backend OCaml or --custard_backend C, or compile \
            the whole program at once."
    ];
  (* Looking definitions up in the environment instantiates their universes,
     which needs the union-find; by the time a backend runs it has been put in
     read-only mode.  The ML extraction does the same thing. *)
  let st = Extract.init deps env in
  Extract.install_chain_reporter st;
  let prog = phase "extract" (fun () ->
               UF.with_uf_enabled (fun () ->
                 (* A module named by --custard_entry_module is requested by
                    name just as one named by --custard_entry is, so its
                    plugins are wanted too. *)
                 let requested =
                   roots @ (Options.custard_entry_modules ()
                            |> List.map Ident.lid_of_str) in
                 Extract.run st roots main (RegEmb.handle_module st requested))) in
  (* Section 12.4: what a linked unit already compiled.  These never enter the
     program -- renaming or emitting them would defeat the purpose -- but the
     layout analysis has to adopt their verdicts and the backends have to know
     where they live. *)
  let imports = Extract.imports st in
  (* Phase 4 pass 1: let-normalization, before anything that moves a subterm
     (section 6). *)
  let prog = phase "anf" (fun () -> Simplify.anf prog) in
  (* Section 5.0: one type declaration per instantiation.  Before the layout
     analysis, so that with no type variables left it may be precise per
     instantiation rather than uniform. *)
  let prog = if Options.custard_monomorphize_types ()
             then phase "monomorphize" (fun () -> Monomorphize.run prog)
             else prog in
  (* Phase 3/4: erasure, newtype collapse and cast elimination (section 5). *)
  let prog, infos, vd =
    phase "layout" (fun () -> Layout.run (imported_type_infos imports) prog) in
  (* Effect-guarded simplification (sections 6 and 7.3).  [vd] is the
     representation the analysis above settled on; nothing below decides one. *)
  let prog = phase "simplify" (fun () ->
               Simplify.run (imported_decls imports) vd prog) in
  (* Last: the passes above invent names, and the whole point is that what a
     reader sees is stable under everything that happened before. *)
  let prog, infos = phase "rename" (fun () -> Rename.run infos prog) in
  (* Section 12.9: where each declaration ends up, when the output is split.
     Computed before the interface is written, because the interface has to
     record it: a downstream unit qualifies a reference by the *file* the
     declaration was emitted into, not by the unit's name. *)
  let files = if Options.custard_split () && Options.custard_backend () = "OCaml"
              then Some (phase "split" (fun () ->
                     Split.run deps (Extract.link_homes st)
                               (List.map fst imports @ prog)))
              else None in
  let homes : SMap.t string = SMap.create 100 in
  let _ = match files with
          | None -> ()
          | Some fs -> fs |> List.iter (fun (m, ds) ->
                         ds |> List.iter (fun d ->
                           SMap.add homes (string_of_name (name_of_decl d)) m)) in
  (* Custard emits one file for the whole program, so -o is unambiguous here,
     unlike in the per-module backends.  Settled before the interface is
     written, because a C unit's interface has to record the *name* of the
     header a downstream unit includes, and [-o] is what decides it
     (section 42.2). *)
  let backend = Options.custard_backend () in
  let ofile =
    match Options.output_to () with
    | Some fn -> fn
    | None ->
      (* A named unit's file has to be named after the unit: that is what makes
         its OCaml module name the one downstream units qualify with.  In C
         the unit name is used as written, since nothing capitalizes a C file
         and the header is what a human types into an [#include]. *)
      let base = match Options.custard_unit () with
                 | Some u -> if backend = "C" then u
                             else OCaml.module_name_of_unit u
                 | None -> "Custard" in
      Find.prepend_output_dir
        (if Options.custard_backend_krml () then base ^ ".krml"
         else match backend with
         | "C" -> base ^ ".c"
         | _ -> base ^ ".ml")
  in
  (* The header is named after the source, and the source includes it by that
     name, so the two travel together and a caller has something to include
     (section 24). *)
  let stem =
    let b = FStarC.Filepath.basename ofile in
    (* The suite writes [-o Foo.dc], the default is [Foo.c]: drop whatever the
       extension is rather than matching on one of them. *)
    let parts = FStarC.String.split ['.'] b in
    if List.length parts <= 1 then b
    else FStarC.String.concat "." (List.rev (List.tl (List.rev parts))) in
  (* Section 42.  Empty unless this run was told it is a unit or given one to
     link against; [no_unit] is then exactly the whole-program behaviour. *)
  let cu : C.unit_info =
    if backend <> "C" then C.no_unit
    else { C.cu_name    = Options.custard_unit ();
           C.cu_headers = Extract.link_headers st;
           C.cu_inits   = Extract.link_inits st } in
  (* After [Rename], because the names a `.cui` exports are the names the
     generated source actually spells. *)
  phase "iface" (fun () ->
    let hdr_file, init =
      if backend = "C"
      then Some (stem ^ ".h"), C.init_globals_name cu (List.map fst imports @ prog)
      else None, None in
    write_unit_iface st homes hdr_file init prog infos);
  if Options.custard_dump_ir () then
    Format.print_string (program_to_string prog ^ "\n");
  if Options.custard_warn_any () then warn_any prog;
  match backend with
  | "OCaml" when Some? files ->
    (* Section 12.9.  One whole-program run, one file per F* source module:
       the hand-written realizations reference modules Custard compiles, and
       OCaml compilation units have to form a DAG. *)
    phase "print" (fun () ->
      OCaml.print_split (Some?.v files) |> List.iter (fun (m, src) ->
        BU.write_file (Find.prepend_output_dir (m ^ ".ml")) src))
  | "KrmlC" | "KrmlRust" -> Krml.write_program ofile prog
  | "C" ->
    let hdr, src = C.print_program stem cu (List.map fst imports @ prog) in
    BU.write_file (FStarC.Filepath.join_paths (FStarC.Filepath.dirname ofile)
                     (stem ^ ".h")) hdr;
    BU.write_file ofile src
  | "OCaml" -> BU.write_file ofile (OCaml.print_program (List.map fst imports @ prog))
  | b ->
    E.raise_error0 E.Fatal_OptionsNotCompatible [
      text ("Unknown --custard_backend " ^ b ^ ".");
      text "The backends are OCaml (the default), KrmlC, KrmlRust and C."
    ]

(* [--profile_component FStarC.Custard] prints the phase breakdown.  Custard
   runs after the last module is checked, so nothing else would report these
   counters; the report is here rather than in [Universal] for that reason. *)
(* Reported on the way out whichever way we leave.  [Universal] calls
   [Profiling.report_and_clear] only after a file type-checks, so an
   extraction that raises would report nothing -- and a run that fails, or one
   that has to be interrupted, is precisely the one worth profiling.  Round 31
   could not get a breakdown out of any CDDL entry for this reason. *)
let run (deps:Dep.deps) (env:TcEnv.env) : ML unit =
  try
    phase "driver" (fun () -> run_phases deps env);
    Prof.report ()
  with e -> (Prof.report (); raise e)
