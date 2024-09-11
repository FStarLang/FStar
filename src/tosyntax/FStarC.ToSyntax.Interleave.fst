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

open FStarC
open FStarC.Ident
open FStarC.Errors
open FStarC.Syntax.Syntax
open FStarC.Parser.AST
open FStarC.Class.Show
open FStarC.Pprint
open FStarC.Class.PP


(* Some basic utilities *)
let id_eq_lid i (l:lident) = (string_of_id i) = (string_of_id (ident_of_lid l))

let is_val x d = match d.d with
    | Val(y, _) -> (string_of_id x) = (string_of_id y)
    | DeclToBeDesugared { idents=[y] } -> (string_of_id x) = (string_of_id y)
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
           (Format.fmt1 "Unknown syntax extension %s" extension_name)
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
   : ML (list decl  //remaining iface decls
    & list decl) =  //d prefixed with relevant bits from iface
   let qualify_karamel_private impl =
     if Options.Ext.get "no_krml_private" <> "" then
       impl
     else
       let karamel_private =
           FStarC.Parser.AST.mk_term
                 (Const (FStarC.Const.Const_string ("KrmlPrivate", impl.drange)))
                 impl.drange
                 FStarC.Parser.AST.Expr
       in
       {impl with attrs=karamel_private::impl.attrs}
   in
   //friend always takes precedence
   if Friend? impl.d then iface, [impl] else
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
         let rec aux mutuals iface
            : ML (list decl & list decl) =
           match mutuals, iface with
           | [], _ -> [], iface
           | _::_, [] -> [], []
           | y::ys, iface_hd::iface_tl when is_val (ident_of_lid y) iface_hd ->
             let val_ys, iface = aux ys iface_tl in
             iface_hd::val_ys, iface

           | y::ys, iface_hd::iface_tl when Some? <| List.tryFind (is_val (ident_of_lid y)) iface_tl ->
             raise_error iface_hd Errors.Fatal_WrongDefinitionOrder [
                 text (Format.fmt2 "%s is out of order with the definition of %s"
                                         (show iface_hd)
                                         (Ident.string_of_lid y))
               ]
           | y::ys, iface_hd::iface_tl ->
             aux ys iface //no val given for 'y'; ok
         in
         let take_iface, rest_iface = aux mutually_defined_with_x iface_tl in
         rest_iface, iface_hd::take_iface@[impl]
       )

     //Extension declarations (e.g., Pulse fn) in the interface:
     //When the implementation defines the same name, consume the interface decl.
     //If the implementation is also an extension decl, don't prefix the interface decl
     //(since both will produce their own sigelts). Otherwise, prefix it so the val is available.
     //This prevents the implementation from getting KrmlPrivate.
     | DeclToBeDesugared { idents=[x] } ->
       let def_ids = definition_lids impl in
       let defines_x = Util.for_some (id_eq_lid x) def_ids in
       if defines_x then (
         match impl.d with
         | DeclToBeDesugared _ ->
           //both interface and impl are extension decls; each produces its own sigelt
           iface_tl, [impl]
         | _ ->
           //impl is a regular let; need the interface decl to provide the val
           iface_tl, [iface_hd; impl]
       ) else (
         //implementation doesn't define x; skip past this iface entry
         //and try to find a match further in the interface.
         //Keep iface_hd in the remaining interface for later matching.
         let iface, ds = prefix_with_iface_decls iface_tl impl in
         iface_hd::iface, ds
       )

     | Pragma _ ->
        (* Don't interleave pragmas on interface into implementation *)
        prefix_with_iface_decls iface_tl impl

     | Exception(id, _) ->
       (* If impl also defines the same exception, skip the iface declaration *)
       begin match impl.d with
       | Exception(id', _) when (string_of_id id) = (string_of_id id') ->
         iface_tl, [impl]
       | _ ->
         let iface, ds = prefix_with_iface_decls iface_tl impl in
         iface, iface_hd::ds
       end

     | TopLevelLet(_, defs) when iface_hd.attrs = [] ->
       (* If impl also defines the same names, skip the iface let definition.
          But only when the iface let has no attributes—an [@@expect_failure] let
          is a test, not a real definition, so it should be kept. *)
       let iface_lids = lids_of_let defs in
       let impl_lids = definition_lids impl in
       if iface_lids |> Util.for_some (fun l ->
            impl_lids |> Util.for_some (fun l' -> id_eq_lid (ident_of_lid l) l'))
       then iface_tl, [impl]
       else
         let iface, ds = prefix_with_iface_decls iface_tl impl in
         iface, iface_hd::ds

     | _ ->
       let iface, ds = prefix_with_iface_decls iface_tl impl in
       iface, iface_hd::ds
    end

let check_initial_interface (iface:list decl) =
    let rec aux iface
        : ML unit =
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
                     (Format.fmt2 "'val %s' and 'let %s' cannot both be provided in an interface" (string_of_id x) (string_of_id x))
              else if hd.quals |> List.contains Assumption
              then raise_error hd Errors.Fatal_AssumeValInInterface
                     "Interfaces cannot use `assume val x : t`; just write `val x : t` instead"
              else ()

            | _ -> ()
          end
    in
    aux iface;
    iface |> List.filter (fun d -> match d.d with TopLevelModule _ -> false | _ -> true)

let prefix_one_decl (iface:list decl) impl : ML (list decl & list decl) =
    match impl.d with
    | TopLevelModule _ -> iface, [impl]
    | _ ->
      prefix_with_iface_decls iface impl

//////////////////////////////////////////////////////////////////////////
//Top-level interface
//////////////////////////////////////////////////////////////////////////
module E = FStarC.Syntax.DsEnv
let initialize_interface (mname:Ident.lid) (l:list decl) : E.withenv unit =
  fun (env:E.env) ->
    let decls = check_initial_interface l in
    match E.iface_decls env mname with
    | Some _ ->
      raise_error mname Errors.Fatal_InterfaceAlreadyProcessed
        (Format.fmt1 "Interface %s has already been processed" (show mname))
    | None ->
      (), E.set_iface_decls env mname decls

let fixup_interleaved_decls (iface : list decl) : ML (list decl) =
  let fix1 (d : decl) : decl =
    let d = { d with interleaved = true } in
    d
  in
  iface |> List.map fix1

let prefix_with_interface_decls (impl:decl) : E.withenv (list decl) =
  fun (env:E.env) ->
    let decls, env = 
      match E.iface_decls env (E.current_module env) with
      | None ->
        [impl], env
      | Some iface ->
        let iface = fixup_interleaved_decls iface in
        let iface, impl = prefix_one_decl iface impl in
        let env = E.set_iface_decls env (E.current_module env) iface in
        impl, env
    in
    if Options.dump_module (Ident.string_of_lid (E.current_module env))
    then Format.print1 "Interleaved decls:\n%s\n" (show decls);
    decls,env

let interleave_module (a:modul) (expect_complete_modul:bool) : E.withenv modul =
  fun (env:E.env)  ->
    match a with
    | Interface _ -> a, env
    | Module {no_prelude; mname=l; decls=impls} -> begin
      match E.iface_decls env l with
      | None -> a, env
      | Some iface ->
        let iface = fixup_interleaved_decls iface in
        let iface, impls =
            List.fold_left
                (fun (iface, impls) impl ->
                    let iface, impls' = prefix_one_decl iface impl in
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
        (* Remove .fst TopLevelLet/Exception entries that duplicate .fsti entries.
           This handles the case where both .fsti and .fst define the same let binding
           (e.g., operator aliases in FStarC.Class.Monad) or the same exception
           (e.g., SkipResugar in FStarC.Syntax.Resugar). The interleaver
           emits .fsti TopLevelLets/Exceptions as prefix material; the .fst copies are redundant. *)
        let impls =
            let iface_let_names =
              List.collect (fun (d:decl) ->
                if not d.interleaved then []
                (* Don't count attributed iface lets (e.g., [@@expect_failure])
                   as duplicates—they are tests, not real definitions *)
                else if not (Nil? d.attrs) then []
                else match d.d with
                | TopLevelLet(_, defs) ->
                  lids_of_let defs |> List.map (fun l -> string_of_id (ident_of_lid l))
                | _ -> []) impls
            in
            let iface_exn_names =
              List.collect (fun (d:decl) ->
                if not d.interleaved then []
                else match d.d with
                | Exception(id, _) -> [string_of_id id]
                | _ -> []) impls
            in
            if Nil? iface_let_names && Nil? iface_exn_names then impls
            else
              List.filter (fun (d:decl) ->
                if d.interleaved then true
                else match d.d with
                | TopLevelLet(_, defs) ->
                  let fst_lids = lids_of_let defs |> List.map (fun l -> string_of_id (ident_of_lid l)) in
                  if Nil? fst_lids then true
                  else not (fst_lids |> Util.for_all (fun n -> iface_let_names |> Util.for_some (fun m -> n = m)))
                | Exception(id, _) ->
                  not (iface_exn_names |> Util.for_some (fun m -> (string_of_id id) = m))
                | _ -> true) impls
        in
        let env =
            if Options.interactive()
            then E.set_iface_decls env l remaining_iface_vals
            else env //if not interactive, then don't consume iface_decls
                     //since some batch-mode checks, e.g., must_erase_for_extraction
                     //depend on having all the iface decls around
        in
        let a = Module { no_prelude; mname=l; decls=impls } in
        match remaining_iface_vals with
        | _::_ when expect_complete_modul ->
          let open FStarC.Pprint in
          log_issue l Errors.Fatal_InterfaceNotImplementedByModule [
            text (Format.fmt1 "Some interface elements were not implemented by module %s:" (show l))
                ^^ sublist empty (List.map (fun d -> doc_of_string (show d)) remaining_iface_vals)
          ];
          a, env
        | _ ->
          if Options.dump_module (string_of_lid l)
          then Format.print1 "Interleaved module is:\n%s\n" (FStarC.Parser.AST.modul_to_string a);
          a, env
      end
