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
module Rename  = FStarC.Custard.Rename
module Simplify = FStarC.Custard.Simplify
module Ident   = FStarC.Ident
module TcEnv   = FStarC.TypeChecker.Env
module Unit    = FStarC.Custard.Unit

let entrypoints () =
  Options.custard_entries () |> List.map Ident.lid_of_str

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

   A surviving [ECast] is the other half.  Section 5.4 eliminates a coercion
   when the two sides have the same layout, and fuses nested ones; what is left
   is a coercion between representations Custard believes are genuinely
   different, which in OCaml is an [Obj.magic] and in C a reinterpretation.
   The exception is a cast between two machine integers, which is not lost
   information at all but the conversion the source asked for -- a real call
   into [FStar.Int.Cast] -- so it is not reported. *)
let lost_cast (e:expr) (t:cty) : bool =
  match e.ty, t with
  | TInt _, TInt _ -> false
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
    | TVar _ | TInt _ | TUnit | TExn -> false in
  let at (where:string) (c:cty) : ML unit =
    if any_cty c then note ("the " ^ where ^ " has type " ^ show c) in
  let rec go (x:expr) : ML unit =
    (match x.e with
     | ECast (e1, t) when lost_cast e1 t ->
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
    | ECast (e, _) -> go e
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
    match List.rev !sites with
    | [] -> ()
    | ss ->
      E.log_issue0 E.Warning_CustardLostRepresentation
        (text ("Custard lost the representation of " ^
               show (List.length ss) ^ " value(s) in '" ^
               string_of_name (name_of_decl d) ^ "':")
         :: (ss |> List.map (fun s -> text ("- " ^ s)))
         @ [text "A whole, monomorphic program should not need these. The \
                  generated code for them is unchecked: an Obj.magic in OCaml, \
                  a reinterpretation in C."]))

(* Check that every requested entry point actually resolves to a definition we
   can see.  Getting this wrong is by far the most likely user error, and the
   resulting "empty program" would otherwise be silent. *)
let check_entrypoints (env:TcEnv.env) (roots:list Ident.lident) : ML unit =
  roots |> List.iter (fun l ->
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
  : ML (list (name & type_info)) =
  imports |> List.collect (fun (d, ti) ->
    match d, ti with
    | DType dt, Some ti -> [(dt.dt_name, ti)]
    | _ -> [])

(* What [Simplify] needs to know about an imported type: the declaration as the
   *layout analysis* left it, the declaration the interface finally carries,
   and the record verdict its home unit reached.  A type whose interface predates
   [ti_pre] contributes nothing, which costs a re-derivation and not
   correctness -- the export side refuses to export such a type in the first
   place. *)
let imported_shapes (imports:list (decl & option type_info))
  : ML (list (dtype & dtype & bool)) =
  imports |> List.collect (fun (d, ti) ->
    match d, ti with
    | DType fin, Some ti ->
      (match ti.ti_pre with
       | Some pre -> [(pre, fin, ti.ti_record)]
       | None -> [])
    | _ -> [])

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
(* Which types a unit may export.

   [Simplify] reshapes types as well as terms, and a downstream unit has to
   reach the same conclusions.  Two of the three decisions travel: an imported
   declaration's pre-[Simplify] shape and its record verdict go in the
   interface, and [Simplify.run] takes them, so [inline_fields], [depat] and
   [records] all see what the upstream unit saw.

   [unused_params] is the one that does not.  Dropping a type parameter nothing
   uses is a fact about the whole program, and an imported type is pessimized
   rather than pinned (section 12.4 rule 4) -- so a unit that *did* drop a
   parameter cannot export that type, because a downstream unit would spell it
   with the parameter still there.  Nor can it export anything whose signature
   mentions one; those get compiled downstream, which costs duplication and
   nothing else. *)
let stable_types (before:list (name & tydef & int)) (prog:program) : ML (SMap.t unit) =
  let ok = SMap.create 50 in
  let final = SMap.create 50 in
  prog |> List.iter (fun d ->
    match d with
    | DType t -> SMap.add final (string_of_name t.dt_name) (List.length t.dt_params)
    | _ -> ());
  before |> List.iter (fun (n, _, nparams) ->
    match SMap.try_find final (string_of_name n) with
    | Some nparams' when nparams = nparams' -> SMap.add ok (string_of_name n) ()
    | _ -> ());
  (* Close downwards: a type is only usable across the boundary if every type
     it is built out of is too. *)
  let rec settle (fuel:int) : ML unit =
    if fuel <= 0 then () else
    let changed = mk_ref false in
    prog |> List.iter (fun d ->
      match d with
      | DType t when Some? (SMap.try_find ok (string_of_name t.dt_name)) ->
        if type_names_of_decl d |> List.existsb (fun k ->
             None? (SMap.try_find ok k) && Some? (SMap.try_find final k))
        then (SMap.remove ok (string_of_name t.dt_name); changed := true)
      | _ -> ());
    if !changed then settle (fuel - 1) in
  settle (List.length prog + 1);
  ok

let unit_entries (keys:list (string & string)) (stable:SMap.t unit)
                 (pre:list (string & dtype))
                 (prog:program) (infos:list (name & type_info))
  : ML (list Unit.entry) =
  let key_of (n:name) : ML (option string) =
    keys |> List.tryPick (fun (n', k) ->
      if n' = string_of_name n then Some k else None) in
  let is_record (n:name) : ML bool =
    prog |> List.existsb (fun d ->
      match d with
      | DType t -> string_of_name t.dt_name = string_of_name n && TRecord? t.dt_body
      | _ -> false) in
  let info_of (n:name) : ML (option type_info) =
    infos |> List.tryPick (fun (n', ti) ->
      if string_of_name n' = string_of_name n
      then Some { ti with
                  ti_pre = pre |> List.tryPick (fun (k, dt) ->
                             if k = string_of_name n then Some dt else None);
                  ti_record = is_record n }
      else None) in
  prog |> List.collect (fun d ->
    if has_flag (decl_flags d) Inline || Some? (imported_unit d) then [] else
    (* A declaration whose signature names a type this unit cannot export
       cannot be exported either: a downstream unit would have no way to spell
       its argument. *)
    if type_names_of_decl d |> List.existsb (fun k ->
         None? (SMap.try_find stable k)
         && prog |> List.existsb (fun d' -> DType? d' && string_of_name (name_of_decl d') = k))
    then [] else
    if DType? d && None? (SMap.try_find stable (string_of_name (name_of_decl d))) then [] else
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
    | Some k -> [{ Unit.ue_key = k; Unit.ue_decl = d; Unit.ue_type = ti }])

let write_unit_iface (st:Extract.state) (stable:SMap.t unit)
                     (pre:list (string & dtype))
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
      };
      Unit.ui_entries = unit_entries (Extract.exported_keys st) stable pre prog infos;
    } in
    if Options.custard_dump_cui () then
      Format.print_string (Unit.iface_to_string i);
    Unit.write_iface (Find.prepend_output_dir (u ^ ".cui")) i

let run (deps:Dep.deps) (env:TcEnv.env) : ML unit =
  let main = main_entry () in
  (* [--custard_main] is a root too, so that the common case needs only one
     option. *)
  let roots = entrypoints () @ (match main with Some l -> [l] | None -> []) in
  if Nil? roots then
    E.raise_error0 E.Fatal_OptionsNotCompatible [
      text "--codegen Custard requires at least one --custard_entry or \
            --custard_main.";
      text "Custard is a whole-program compiler: it extracts exactly the \
                   definitions reachable from the entry points."
    ];
  check_entrypoints env roots;
  (* Section 12 is specified for the OCaml backend.  The C and karamel
     backends need a header and a linker story of their own, which they do not
     have yet; failing here is better than emitting a file that refers to
     symbols nothing declares. *)
  if (Some? (Options.custard_unit ()) || Cons? (Options.custard_links ()))
     && Options.custard_backend () <> "OCaml" then
    E.raise_error0 E.Fatal_OptionsNotCompatible [
      text "Separate compilation (--custard_unit, --custard_link) is \
            implemented for --custard_backend OCaml only.";
      text "The C and karamel backends still compile a whole program at once."
    ];
  (* Looking definitions up in the environment instantiates their universes,
     which needs the union-find; by the time a backend runs it has been put in
     read-only mode.  The ML extraction does the same thing. *)
  let st = Extract.init deps env in
  let prog = UF.with_uf_enabled (fun () -> Extract.run st roots main) in
  (* Section 12.4: what a linked unit already compiled.  These never enter the
     program -- renaming or emitting them would defeat the purpose -- but the
     layout analysis has to adopt their verdicts and the backends have to know
     where they live. *)
  let imports = Extract.imports st in
  (* Phase 4 pass 1: let-normalization, before anything that moves a subterm
     (section 6). *)
  let prog = Simplify.anf prog in
  (* Section 5.0: one type declaration per instantiation.  Before the layout
     analysis, so that with no type variables left it may be precise per
     instantiation rather than uniform. *)
  let prog = if Options.custard_monomorphize_types ()
             then Monomorphize.run prog else prog in
  (* Phase 3/4: erasure, newtype collapse and cast elimination (section 5). *)
  let prog, infos = Layout.run (imported_type_infos imports) prog in
  (* The shape of every type as the layout analysis left it, so that the
     interface can tell which ones the passes below went on to change. *)
  let shapes_before = prog |> List.collect (fun d ->
    match d with
    | DType t -> [(t.dt_name, t.dt_body, List.length t.dt_params)]
    | _ -> []) in
  (* [Simplify] is about to reshape these, and the interface has to carry the
     shape it saw rather than the one it left behind: a downstream unit runs
     the same passes and must be asking the same questions. *)
  let pre_decls = prog |> List.collect (fun d ->
    match d with DType t -> [(string_of_name t.dt_name, t)] | _ -> []) in
  (* Effect-guarded simplification (sections 6 and 7.3). *)
  let prog = Simplify.run (imported_shapes imports) prog in
  (* Compared here rather than after [Rename], whose renamings are recorded in
     the exported declaration itself and so cross the boundary intact. *)
  let stable = stable_types shapes_before prog in
  (* Last: the passes above invent names, and the whole point is that what a
     reader sees is stable under everything that happened before. *)
  let prog, infos = Rename.run infos prog in
  (* After [Rename], because the names a `.cui` exports are the names the
     generated source actually spells. *)
  write_unit_iface st stable pre_decls prog infos;
  if Options.custard_dump_ir () then
    Format.print_string (program_to_string prog ^ "\n");
  if Options.custard_warn_any () then warn_any prog;
  (* Custard emits one file for the whole program, so -o is unambiguous here,
     unlike in the per-module backends. *)
  let backend = Options.custard_backend () in
  let ofile =
    match Options.output_to () with
    | Some fn -> fn
    | None ->
      (* A named unit's file has to be named after the unit: that is what makes
         its OCaml module name the one downstream units qualify with. *)
      let base = match Options.custard_unit () with
                 | Some u -> OCaml.module_name_of_unit u
                 | None -> "Custard" in
      Find.prepend_output_dir
        (match backend with
         | "Krml" -> base ^ ".krml"
         | "C" -> base ^ ".c"
         | _ -> base ^ ".ml")
  in
  match backend with
  | "Krml" -> Krml.write_program ofile prog
  | "C" -> BU.write_file ofile (C.print_program (List.map fst imports @ prog))
  | "OCaml" -> BU.write_file ofile (OCaml.print_program (List.map fst imports @ prog))
  | b ->
    E.raise_error0 E.Fatal_OptionsNotCompatible [
      text ("Unknown --custard_backend " ^ b ^ ".");
      text "The backends are OCaml (the default), Krml and C."
    ]
