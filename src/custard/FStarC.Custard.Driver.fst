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

module BU    = FStarC.Util
module E     = FStarC.Errors
module Dep     = FStarC.Parser.Dep
module UF      = FStarC.Syntax.Unionfind
module Krml    = FStarC.Custard.PrintKrml
module Extract = FStarC.Custard.Extract
module Find    = FStarC.Find
module Layout  = FStarC.Custard.Layout
module OCaml   = FStarC.Custard.PrintOCaml
module Rename  = FStarC.Custard.Rename
module Simplify = FStarC.Custard.Simplify
module Ident   = FStarC.Ident
module TcEnv   = FStarC.TypeChecker.Env

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
    | TBuf c -> any_cty c
    | TVar _ | TInt _ | TUnit -> false in
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
    | ECtor (_, es) | ERaise (_, es) | ETuple es | EOp (_, es) -> sub es
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
  (* Looking definitions up in the environment instantiates their universes,
     which needs the union-find; by the time a backend runs it has been put in
     read-only mode.  The ML extraction does the same thing. *)
  let prog = UF.with_uf_enabled (fun () -> Extract.run (Extract.init deps env) roots main) in
  (* Phase 4 pass 1: let-normalization, before anything that moves a subterm
     (section 6). *)
  let prog = Simplify.anf prog in
  (* Phase 3/4: erasure, newtype collapse and cast elimination (section 5). *)
  let prog = Layout.run prog in
  (* Effect-guarded simplification (sections 6 and 7.3). *)
  let prog = Simplify.run prog in
  (* Last: the passes above invent names, and the whole point is that what a
     reader sees is stable under everything that happened before. *)
  let prog = Rename.run prog in
  if Options.custard_dump_ir () then
    Format.print_string (program_to_string prog ^ "\n");
  if Options.custard_warn_any () then warn_any prog;
  (* Custard emits one file for the whole program, so -o is unambiguous here,
     unlike in the per-module backends. *)
  let krml = Options.custard_backend () = "Krml" in
  let ofile =
    match Options.output_to () with
    | Some fn -> fn
    | None -> Find.prepend_output_dir (if krml then "Custard.krml" else "Custard.ml")
  in
  if krml
  then Krml.write_program ofile prog
  else BU.write_file ofile (OCaml.print_program prog)
