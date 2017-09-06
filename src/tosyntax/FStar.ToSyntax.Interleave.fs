﻿(*
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
#light "off"
module FStar.ToSyntax.Interleave
open FStar.ST
open FStar.Exn
open FStar.All
//Reorders the top-level definitions/declarations in a file
//in a proper order for consistent type-checking

open FStar
open FStar.Ident
open FStar.Errors
open FStar.Syntax.Syntax
open FStar.Parser.AST

(* Some basic utilities *)
let id_eq_lid i (l:lident) = i.idText = l.ident.idText

let is_val x d = match d.d with
    | Val(y, _) -> x.idText = y.idText
    | _ -> false

let is_type x d = match d.d with
    | Tycon(_, tys) ->
        tys |> Util.for_some (fun (t,_) -> id_of_tycon t = x.idText)
    | _ -> false

//is d of of the form 'let x = ...' or 'type x = ...'
let definition_lids d =
    match d.d with
    | TopLevelLet(_, defs) ->
        lids_of_let defs
    | Tycon(_, tys) ->
        tys |> List.collect (function
                | TyconAbbrev(id, _, _, _), _ ->
                  [Ident.lid_of_ids [id]]
                | _ -> [])
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

   Essentially, we need to check that the definition of a matches
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
        (iface:list<decl>)
        (impl:decl)
   : list<decl>  //remaining iface decls
   * list<decl> =  //d prefixed with relevant bits from iface
   match iface with
   | [] -> [], [impl]
   | iface_hd::iface_tl -> begin
     match iface_hd.d with
     | Tycon(_, tys) when (tys |> Util.for_some (function (TyconAbstract _, _)  -> true | _ -> false)) ->
        raise (Error("Interface contains an abstract 'type' declaration; use 'val' instead", impl.drange))

     | Val(x, t) ->
       //we have a 'val x' in the interface
       //take impl as is, unless it is a let x, in which case prefix it with iface_hd
       let def_ids = definition_lids impl in
       let defines_x = Util.for_some (id_eq_lid x) def_ids in
       if not defines_x
       then if def_ids |> Util.for_some (fun y ->
               iface_tl |> Util.for_some (is_val y.ident))
            then raise (Error(Util.format2 "Expected the definition of %s to precede %s"
                                           x.idText
                                           (def_ids |> List.map Ident.string_of_lid |> String.concat ", "),
                              impl.drange))
            else iface, [impl]
       else let mutually_defined_with_x = def_ids |> List.filter (fun y -> not (id_eq_lid x y)) in
            let rec aux mutuals iface =
                match mutuals, iface with
                | [], _ -> [], iface
                | _::_, [] -> [], []
                | y::ys, iface_hd::iface_tl ->
                  if is_val y.ident iface_hd
                  then let val_ys, iface = aux ys iface_tl in
                       iface_hd::val_ys, iface
                  else if Option.isSome <| List.tryFind (is_val y.ident) iface_tl
                  then raise (Error (Util.format2 "%s is out of order with the definition of %s"
                                            (decl_to_string iface_hd)
                                            (Ident.string_of_lid y),
                                     iface_hd.drange))
                  else aux ys iface //no val given for 'y'; ok
            in
            let take_iface, rest_iface = aux mutually_defined_with_x iface_tl in
            rest_iface, iface_hd::take_iface@[impl]


     | _ ->
       let iface, ds = prefix_with_iface_decls iface_tl impl in
       iface, iface_hd::ds
    end

let check_initial_interface (iface:list<decl>) =
    let rec aux iface =
        match iface with
        | [] -> ()
        | hd::tl -> begin
            match hd.d with
            | Tycon(_, tys) when (tys |> Util.for_some (function (TyconAbstract _, _)  -> true | _ -> false)) ->
              raise (Error("Interface contains an abstract 'type' declaration; use 'val' instead", hd.drange))

            | Val(x, t) ->  //we have a 'val x' in the interface
              if Util.for_some (is_definition_of x) tl
              then raise (Error(Util.format2 "'val %s' and 'let %s' cannot both be provided in an interface" x.idText x.idText,
                                hd.drange))
              else if hd.quals |> List.contains Assumption
              then raise (Error("Interfaces cannot use `assume val x : t`; just write `val x : t` instead",
                                hd.drange))
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
let rec ml_mode_prefix_with_iface_decls
        (iface:list<decl>)
        (impl:decl)
   : list<decl>    //remaining iface decls
   * list<decl> =  //impl prefixed with relevant bits from iface
   match impl.d with
   | TopLevelLet(_, defs) -> //if c
     let xs = lids_of_let defs in
     let val_xs, rest_iface =
        List.partition
            (fun d -> xs |> Util.for_some (fun x -> is_val x.ident d))
            iface
     in
     rest_iface, val_xs@[impl]
   | _ ->
     iface, [impl]

let ml_mode_check_initial_interface (iface:list<decl>) =
    iface |> List.filter (fun d ->
    match d.d with
    | Val _ -> true //only retain the vals in --MLish mode
    | _ -> false)


let prefix_one_decl iface impl =
    match impl.d with
    | TopLevelModule _ -> iface, [impl]
    | _ ->
      if Options.ml_ish ()
      then ml_mode_prefix_with_iface_decls iface impl
      else prefix_with_iface_decls iface impl

//////////////////////////////////////////////////////////////////////////
//Top-level interface
//////////////////////////////////////////////////////////////////////////
module E = FStar.ToSyntax.Env
let initialize_interface (mname:Ident.lid) (l:list<decl>) (env:E.env) : E.env =
    let decls =
        if Options.ml_ish()
        then ml_mode_check_initial_interface l
        else check_initial_interface l in
    match E.iface_decls env mname with
    | Some _ ->
      raise (Error(Util.format1 "Interface %s has already been processed"
                                (Ident.string_of_lid mname),
                   Ident.range_of_lid mname))
    | None ->
      E.set_iface_decls env mname decls

let prefix_with_interface_decls (env:E.env) (impl:decl) : E.env * list<decl> =
    match E.iface_decls env (E.current_module env) with
    | None ->
      env, [impl]
    | Some iface ->
      let iface, impl = prefix_one_decl iface impl in
      let env = E.set_iface_decls env (E.current_module env) iface in
      env, impl

let interleave_module (env:E.env) (a:modul) (expect_complete_modul:bool) : E.env * modul =
    match a with
    | Interface _ -> env, a
    | Module(l, impls) -> begin
      match E.iface_decls env l with
      | None -> env, a
      | Some iface ->
        let iface, impls =
            List.fold_left
                (fun (iface, impls) impl ->
                    let iface, impls' = prefix_one_decl iface impl in
                    iface, impls@impls')
                (iface, [])
                impls
        in
        let env = E.set_iface_decls env l iface in
        let a = Module(l, impls) in
        match iface with
        | _::_ when expect_complete_modul ->
          let err = List.map FStar.Parser.AST.decl_to_string iface |> String.concat "\n\t" in
          raise (Error(Util.format2 "Some interface elements were not implemented by module %s:\n\t%s"
                                    (Ident.string_of_lid l)
                                    err,
                       Ident.range_of_lid l))
        | _ ->
          env, a
      end
