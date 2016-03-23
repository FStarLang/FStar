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
#light "off"
module FStar.Parser.Interleave
//Reorders the top-level definitions/declarations in a file 
//in a proper order for consistent type-checking

open FStar
open FStar.Ident
open FStar.Syntax.Syntax
open FStar.Parser.AST

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

    Note, the order decls 
 *)

let interleave (ds:list<decl>) : list<decl> = 
    let rec head_id_of_pat p = match p.pat with 
        | PatName l -> [l]
        | PatVar (i, _) -> [FStar.Ident.lid_of_ids [i]]
        | PatApp(p, _) -> head_id_of_pat p
        | _ -> [] 
    in
    
    let id_eq_lid i (l:lident) = i.idText = l.ident.idText in

    let lids_of_let defs =  defs |> List.collect (fun (p, _) -> head_id_of_pat p) in

    let prefix_until_let_with_id ds id = 
        FStar.Util.prefix_until (fun d -> match d.d with 
            | ToplevelLet(_, _, ps) -> 
              lids_of_let ps |> Util.for_some (id_eq_lid id)
            | Tycon(_, tys) ->
              if tys |> Util.for_some (function 
                    | TyconAbbrev(id', _, _, _) -> id.idText = id'.idText
                    | _ -> false)
              then raise (Error(Util.format1 "'type' abbreviation cannot be given a corresponding 'val' declaration (%s)" (Range.string_of_range id.idRange), d.drange))
              else false
            | _ -> false) ds in

    let rec aux (out:list<list<decl>>) (ds:list<decl>) = 
        match ds with 
            | [] -> List.rev out |> List.flatten
            | d::ds -> 
              match d.d with
                | Val(qs, x, t) -> 
                  let lopt = prefix_until_let_with_id ds x in
                  begin match lopt with 
                    | None -> 
                      if qs |> List.contains Assumption
                      then aux ([d]::out) ds
                      else raise (Error("No definition found for " ^x.idText, d.drange))

                    | Some (prefix, let_x, suffix) ->
                      if qs |> List.contains Assumption
                      then raise (Error(Util.format2 "Assumed declaration %s is defined at %s" 
                                                     x.idText (Range.string_of_range let_x.drange), 
                                        d.drange))
                      else begin match let_x.d with 
                             | ToplevelLet(_, _, defs) ->
                               let prefix = d::prefix in //take all the val declarations for the defs from the prefix
                               let def_lids = lids_of_let defs in
                               let popt = prefix |> FStar.Util.prefix_until (fun d -> 
                                match d.d with 
                                    | Val(_, y, _) -> 
                                      not (def_lids |> Util.for_some (id_eq_lid y))

                                    | _ -> true) in
                               //popt takes all the val declarations for the defs from the prefix
                               let hoist, suffix = match popt with 
                                    | None -> //prefix only contains vals_for_defs 
                                      prefix@[let_x], suffix

                                    | Some (vals_for_defs, first_non_val_or_unrelated_val, rest) -> 
                                      let rest = first_non_val_or_unrelated_val::rest in
                                      let rec hoist_rest (hoisted, remaining) val_ids rest = match rest with 
                                        | [] -> List.rev hoisted, List.rev remaining
                                        | hd::tl -> 
                                          match hd.d with 
                                            | Val(_, x, _) -> hoist_rest (hoisted, hd::remaining) (x::val_ids) tl
                                            | ToplevelLet(_, _, defs) -> 
                                              let def_lids = lids_of_let defs in 
                                              if val_ids |> Util.for_some (fun x -> 
                                                 def_lids |> Util.for_some (id_eq_lid x))
                                              then //out of order vals and lets
                                                   raise (Error("The definition is out of order", let_x.drange))
                                              else hoist_rest (hd::hoisted, remaining) val_ids tl
                                            | _ -> hoist_rest (hd::hoisted, remaining) val_ids tl 
                                      in
                                      let hoisted, remaining = hoist_rest ([], []) [] rest in
                                      vals_for_defs@hoisted@[let_x], remaining@suffix in

                               aux (hoist::out) suffix

                             | _ -> failwith "Impossible"
                      end
                   end

                | ToplevelLet(_, _, defs) -> 
                  let def_lids = lids_of_let defs in
                  let val_for_defs = FStar.Util.find_map ds (fun d -> match d.d with 
                        | Val(_, x, _) when (def_lids |> Util.for_some (id_eq_lid x)) -> Some (x, d.drange)
                        | _ -> None) in
                  begin match val_for_defs with 
                    | Some (x, r) ->  //we have a 'let x' followed later in the file by a 'val x'; forbid
                      raise (Error(Util.format2 "Definition of %s precedes its declaration at %s" x.idText (Range.string_of_range r), d.drange))

                    | None -> aux ([d]::out) ds
                  end

                | _ -> aux ([d]::out) ds in

    aux [] ds

let interleave_modul m = 
    if !Options.interleave
    then match m with 
            | Module(l, ds) -> Module(l, interleave ds)
            | _ -> m
    else m