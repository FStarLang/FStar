(*
  Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStarC.ToSyntax.Interleave
open FStarC.Effect
open FStarC.List
//Reorders the top-level definitions/declarations in a file
//in a proper order for consistent type-checking

open FStar open FStarC
open FStarC
open FStarC.Ident
open FStarC.Errors
open FStarC.Syntax.Syntax
open FStarC.Parser.AST
open FStarC.Class.Show
open FStarC.Pprint
open FStarC.Class.PP

module BU = FStarC.Util

(* Some basic utilities *)
let id_eq_lid i (l:lident) = (string_of_id i) = (string_of_id (ident_of_lid l))

let is_val x d = match d.d with
    | Val(y, _) -> (string_of_id x) = (string_of_id y)
    | _ -> false

let is_type x d = match d.d with
    | Tycon(_, _, tys) ->
        tys |> Util.for_some (fun t -> id_of_tycon t = (string_of_id x))
    | _ -> false

//
//is d of of the form 'let x = ...' or 'type x = ...' or 'splice[..., x, ...] tac'
// returns unqualified lids
//
let definition_lids d =
    match d.d with
    | TopLevelLet(_, defs) ->
        lids_of_let defs
    | Tycon(_, _, tys) ->
        tys |> List.collect (function
                | TyconAbbrev (id, _, _, _)
                | TyconRecord (id, _, _, _, _)
                | TyconVariant(id, _, _, _) ->
                  [Ident.lid_of_ids [id]]
                | _ -> [])
    | Splice (_, ids, _)
    | DeclToBeDesugared { idents=ids } -> List.map (fun id -> Ident.lid_of_ids [id]) ids
    
    | DeclSyntaxExtension (extension_name, code, _, range) -> begin
      let ext_parser = FStarC.Parser.AST.Util.lookup_extension_parser extension_name in
      match ext_parser with
      | None ->
        raise_error d Errors.Fatal_SyntaxError
           (BU.format1 "Unknown syntax extension %s" extension_name)
       | Some parser ->
         match parser.parse_decl_name code range with
         | Inl error ->
           raise_error error.range Errors.Fatal_SyntaxError error.message
         | Inr id ->
           [Ident.lid_of_ids [id]]
      end
    | _ -> []

let is_definition_of x d =
    Util.for_some (id_eq_lid x) (definition_lids d)



(* The basic idea of interleaving is governed by the following:

   Ordering rule
       If a val-declaration for 'a' precedes a val-declaration for 'b',
       then the let-definition for 'a' must precede the let-definition for 'b'.

   In effect, this means that

      val a
      let x0
      val b
      let x1

      let a
      let b

   Is effectively ordered as:

      val a
      let x0
      let x1
      let a

      val b
      let b

   Essentially, we need to check that the definition of `a` matches
   its signature in `val a : ta` before we allow `a` to be used
   in the signature `val b : tb` and its corresponding definition
   `let b : eb`.

   One wrinkle to deal with is mutual recursion.

   Given:

      val a1
      val a2
      let x0
      val b
      let x1

      let rec a1
      and a2
      let b

    Interleaving produces:

      val a1 : ta1
      val a2 : ta2
      let x0
      let x1

      let rec a1
      and a2

      val b
      let b

    I.e, the vals and the let-recs "move together"

    One consequence of interleaving is that a program is type-checked
    in an order different from the sequential order of the text the
    programmer wrote. This may result in potentially unintuitive error
    message ordering.

 *)

let rec prefix_with_iface_decls
        (iface:list decl)
        (impl:decl)
   : list decl  //remaining iface decls
   & list decl =  //d prefixed with relevant bits from iface
   let qualify_karamel_private impl =
       let karamel_private =
           FStarC.Parser.AST.mk_term
                 (Const (FStarC.Const.Const_string ("KrmlPrivate", impl.drange)))
                 impl.drange
                 FStarC.Parser.AST.Expr
       in
       {impl with attrs=karamel_private::impl.attrs}
   in
   match iface with
   | [] -> [], [qualify_karamel_private impl]
   | iface_hd::iface_tl -> begin
     match iface_hd.d with
     | Tycon(_, _, tys) when (tys |> Util.for_some (function (TyconAbstract _)  -> true | _ -> false)) ->
        raise_error impl Errors.Fatal_AbstractTypeDeclarationInInterface [
          text "Interface contains an abstract 'type' declaration; use 'val' instead."
        ]

     | Splice (_, [x], _)
     | Val(x, _) ->
       //we have a 'val x' in the interface
       //take impl as is, unless it is a
       //       let x (or a `type abbreviation x`)
       //or an  inductive type x
       //or a splice that defines x
       //in which case prefix it with iface_hd
       let def_ids = definition_lids impl in
       let defines_x = Util.for_some (id_eq_lid x) def_ids in
       if not defines_x then (
         if def_ids |> Util.for_some (fun y ->
               iface_tl |> Util.for_some (is_val (ident_of_lid y)))
         then
           raise_error impl Errors.Fatal_WrongDefinitionOrder [
               text "Expected the definition of" ^/^ pp x ^/^ text "to precede"
               ^/^ (pp def_ids)
             ];
         iface, [qualify_karamel_private impl]
       ) else (
         let mutually_defined_with_x = def_ids |> List.filter (fun y -> not (id_eq_lid x y)) in
         let rec aux mutuals iface =
           match mutuals, iface with
           | [], _ -> [], iface
           | _::_, [] -> [], []
           | y::ys, iface_hd::iface_tl when is_val (ident_of_lid y) iface_hd ->
             let val_ys, iface = aux ys iface_tl in
             iface_hd::val_ys, iface

           | y::ys, iface_hd::iface_tl when Option.isSome <| List.tryFind (is_val (ident_of_lid y)) iface_tl ->
             raise_error iface_hd Errors.Fatal_WrongDefinitionOrder [
                 text (Util.format2 "%s is out of order with the definition of %s"
                                         (show iface_hd)
                                         (Ident.string_of_lid y))
               ]
           | y::ys, iface_hd::iface_tl ->
             aux ys iface //no val given for 'y'; ok
         in
         let take_iface, rest_iface = aux mutually_defined_with_x iface_tl in
         rest_iface, iface_hd::take_iface@[impl]
       )

     | Pragma _ ->
        (* Don't interleave pragmas on interface into implementation *)
        prefix_with_iface_decls iface_tl impl

     | _ ->
       let iface, ds = prefix_with_iface_decls iface_tl impl in
       iface, iface_hd::ds
    end

let check_initial_interface (iface:list decl) =
    let rec aux iface =
        match iface with
        | [] -> ()
        | hd::tl -> begin
            match hd.d with
            | Tycon(_, _, tys) when (tys |> Util.for_some (function (TyconAbstract _)  -> true | _ -> false)) ->
              raise_error hd Errors.Fatal_AbstractTypeDeclarationInInterface
                "Interface contains an abstract 'type' declaration; use 'val' instead"

            | Val(x, t) ->  //we have a 'val x' in the interface
              if Util.for_some (is_definition_of x) tl
              then raise_error hd Errors.Fatal_BothValAndLetInInterface 
                     (Util.format2 "'val %s' and 'let %s' cannot both be provided in an interface" (string_of_id x) (string_of_id x))
              else if hd.quals |> List.contains Assumption
              then raise_error hd Errors.Fatal_AssumeValInInterface
                     "Interfaces cannot use `assume val x : t`; just write `val x : t` instead"
              else ()

            | _ -> ()
          end
    in
    aux iface;
    iface |> List.filter (fun d -> match d.d with TopLevelModule _ -> false | _ -> true)

//////////////////////////////////////////////////////////////////////
//A weaker variant, for use only in --MLish mode
//////////////////////////////////////////////////////////////////////
//in --MLish mode: the interleaving rules are WAY more lax
//      this is basically only in support of bootstrapping the compiler
//      Here, if you have a `let x = e` in the implementation
//      Then prefix it with `val x : t`, if any in the interface
//      Don't enforce any ordering constraints
let ml_mode_prefix_with_iface_decls
        (iface:list decl)
        (impl:decl)
   : list decl    //remaining iface decls
   & list decl =  //impl prefixed with relevant bits from iface


   match impl.d with
   | TopLevelModule _
   | Open _
   | Friend _
   | Include _
   | ModuleAbbrev _ ->
     let iface_prefix_opens, iface =
       List.span (fun d -> match d.d with | Open _ | ModuleAbbrev _ -> true | _ -> false) iface     
     in
     let iface =
       List.filter 
         (fun d ->
           match d.d with
           | Val _
           | Tycon _ -> true //only retain the vals in --MLish mode
           | _ -> false)
         iface
     in
     iface, [impl]@iface_prefix_opens
     
   | _ ->

     let iface_prefix_tycons, iface =
       List.span (fun d -> match d.d with | Tycon _ -> true | _ -> false) iface
     in

     let maybe_get_iface_vals lids iface =
       List.partition
         (fun d -> lids |> Util.for_some (fun x -> is_val (ident_of_lid x) d))
         iface in

     match impl.d with
     | TopLevelLet _
     | Tycon _ ->
       let xs = definition_lids impl in
       let val_xs, rest_iface = maybe_get_iface_vals xs iface in
       rest_iface, iface_prefix_tycons@val_xs@[impl]
     | _ ->
       iface, iface_prefix_tycons@[impl]

let ml_mode_check_initial_interface mname (iface:list decl) =
  iface |> List.filter (fun d ->
    match d.d with
    | Tycon(_, _, tys)
      when (tys |> Util.for_some (function (TyconAbstract _)  -> true | _ -> false)) ->
      raise_error d Errors.Fatal_AbstractTypeDeclarationInInterface
        "Interface contains an abstract 'type' declaration; use 'val' instead"
    | Tycon _
    | Val _
    | Open _
    | ModuleAbbrev _ -> true
    | _ -> false)

let ulib_modules = [
  "FStar.Calc";
  "FStar.TSet";
  "FStar.Seq.Base";
  "FStar.Seq.Properties";
  "FStar.UInt";
  "FStar.UInt8";
  "FStar.UInt16";
  "FStar.UInt32";
  "FStar.UInt64";
  "FStar.Int";
  "FStar.Int8";
  "FStar.Int16";
  "FStar.Int32";
  "FStar.Int64";
]

(*
 * AR: ml mode optimizations are only applied in ml mode and only to non-core files
 *
 *     otherwise we skip effect declarations like Lemma from Pervasives.fsti,
 *       resulting in desugaring failures when typechecking Pervasives.fst
 *)
let apply_ml_mode_optimizations (mname:lident) : bool =
  (*
   * AR: 03/29:
   *     As we introduce interfaces for modules in ulib/, the interleaving code
   *       doesn't interact with it too well when bootstrapping
   *     Essentially we do optimizations here (e.g. not taking any interface decls but vals)
   *       when bootstrapping
   *     This doesn't work well for ulib files (but is ok for compiler files)
   *     A better way to fix this problem would be to make compiler files in a separate namespace
   *       and then do these optimizations (as well as --MLish etc.) only for them
   *     But until then ... (sigh)
   *)  
  Options.ml_ish () &&
  (not (List.contains (Ident.string_of_lid mname) (Parser.Dep.core_modules ()))) &&
  (not (List.contains (Ident.string_of_lid mname) ulib_modules))

let prefix_one_decl mname iface impl =
    match impl.d with
    | TopLevelModule _ -> iface, [impl]
    | _ ->
      if apply_ml_mode_optimizations mname
      then ml_mode_prefix_with_iface_decls iface impl
      else prefix_with_iface_decls iface impl

//////////////////////////////////////////////////////////////////////////
//Top-level interface
//////////////////////////////////////////////////////////////////////////
module E = FStarC.Syntax.DsEnv
let initialize_interface (mname:Ident.lid) (l:list decl) : E.withenv unit =
  fun (env:E.env) ->
    let decls =
        if apply_ml_mode_optimizations mname
        then ml_mode_check_initial_interface mname l
        else check_initial_interface l in
    match E.iface_decls env mname with
    | Some _ ->
      raise_error mname Errors.Fatal_InterfaceAlreadyProcessed
        (Util.format1 "Interface %s has already been processed" (show mname))
    | None ->
      (), E.set_iface_decls env mname decls

let fixup_interleaved_decls (iface : list decl) : list decl =
  let fix1 (d : decl) : decl =
    let d = { d with interleaved = true } in
    d
  in
  iface |> List.map fix1

let prefix_with_interface_decls mname (impl:decl) : E.withenv (list decl) =
  fun (env:E.env) ->
    let decls, env = 
      match E.iface_decls env (E.current_module env) with
      | None ->
        [impl], env
      | Some iface ->
        let iface = fixup_interleaved_decls iface in
        let iface, impl = prefix_one_decl mname iface impl in
        let env = E.set_iface_decls env (E.current_module env) iface in
        impl, env
    in
    if Options.dump_module (Ident.string_of_lid mname)
    then Util.print1 "Interleaved decls:\n%s\n" (show decls);
    decls,env
    

let interleave_module (a:modul) (expect_complete_modul:bool) : E.withenv modul =
  fun (env:E.env)  ->
    match a with
    | Interface _ -> a, env
    | Module(l, impls) -> begin
      match E.iface_decls env l with
      | None -> a, env
      | Some iface ->
        let iface = fixup_interleaved_decls iface in
        let iface, impls =
            List.fold_left
                (fun (iface, impls) impl ->
                    let iface, impls' = prefix_one_decl l iface impl in
                    iface, impls@impls')
                (iface, [])
                impls
        in
        let iface_lets, remaining_iface_vals =
            match FStarC.Util.prefix_until (function {d=Val _} -> true
                                                           | {d=Splice _} -> true
            | _ -> false) iface with
            | None -> iface, []
            | Some (lets, one_val, rest) -> lets, one_val::rest
        in
        let impls = impls@iface_lets in
        let env =
            if Options.interactive()
            then E.set_iface_decls env l remaining_iface_vals
            else env //if not interactive, then don't consume iface_decls
                     //since some batch-mode checks, e.g., must_erase_for_extraction
                     //depend on having all the iface decls around
        in
        let a = Module(l, impls) in
        match remaining_iface_vals with
        | _::_ when expect_complete_modul ->
          let open FStarC.Pprint in
          log_issue l Errors.Fatal_InterfaceNotImplementedByModule [
            text (Util.format1 "Some interface elements were not implemented by module %s:" (show l))
                ^^ sublist empty (List.map (fun d -> doc_of_string (show d)) remaining_iface_vals)
          ];
          a, env
        | _ ->
          if Options.dump_module (string_of_lid l)
          then Util.print1 "Interleaved module is:\n%s\n" (FStarC.Parser.AST.modul_to_string a);
          a, env
      end
