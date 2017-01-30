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
open FStar.Errors
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

let interleave (iface:list<decl>) (impl:list<decl>) : list<decl> = 
    let id_eq_lid i (l:lident) = i.idText = l.ident.idText in

    let is_val x d = match d.d with 
        | Val(y, _) -> x.idText = y.idText
        | _ -> false in

    let is_type x d = match d.d with 
        | Tycon(_, tys) -> 
          tys |> Util.for_some (fun (t,_) -> id_of_tycon t = x.idText)
        | _ -> false in

    //is d of of the form 'let x = ...' or 'type x = ...'
    let is_let x d = match d.d with 
        | TopLevelLet(_, defs) -> 
          lids_of_let defs |> Util.for_some (id_eq_lid x)
        | Tycon(_, tys) ->
          tys |> List.map (fun (x,_) -> x)
            |> Util.for_some (function 
            | TyconAbbrev(id', _, _, _) -> x.idText = id'.idText
            | _ -> false) 
        | _ -> false in
         
          
    let prefix_until_let x ds = ds |> FStar.Util.prefix_until (is_let x) in

    let aux_ml (iface:list<decl>) (impl:list<decl>) : list<decl> = 
        let rec interleave_vals (vals:list<decl>) (impl:list<decl>) = 
            match vals with 
            | [] -> impl
            | {d=Val(x, _)}::remaining_vals ->
              let d = List.hd vals in
              let lopt = prefix_until_let x impl in
              begin match lopt with 
                    | None -> 
                      raise (Error("No definition found for " ^x.idText, d.drange))

                    | Some (prefix, let_x, rest_impl) ->
                      let impl = prefix@[d;let_x]@rest_impl in
                      interleave_vals remaining_vals impl
              end
            
            | _::remaining_vals -> 
              interleave_vals remaining_vals impl
        in
        interleave_vals iface impl
    in

    let rec aux (out:list<list<decl>>) iface impl =
        match iface with 
            | [] -> (List.rev out |> List.flatten) @ impl
            | d::ds -> 
              match d.d with
                | Tycon(_, tys) when (tys |> Util.for_some (function (TyconAbstract _, _)  -> true | _ -> false)) -> 
                  raise (Error("Interface contains an abstract 'type' declaration; use 'val' instead", d.drange))

                | Val(x, t) ->  //we have a 'val x' in the interface
                  let _ = match impl |> List.tryFind (fun d -> is_val x d || is_type x d) with 
                    | None -> ()
                    | Some ({d=Val _; drange=r}) -> raise (Error(Util.format1 "%s is repeated in the implementation" (decl_to_string d), r))
                    | Some i -> raise (Error(Util.format1 "%s in the interface is implemented with a 'type'" (decl_to_string d), i.drange)) in
                  begin match prefix_until_let x iface with
                    | Some _ -> raise (Error(Util.format2 "'val %s' and 'let %s' cannot both be provided in an interface" x.idText x.idText, d.drange))
                    | None ->
                      let lopt = prefix_until_let x impl in
                      begin match lopt with 
                        | None -> 
                          if d.quals |> List.contains Assumption
                          then aux ([d]::out) ds impl
                          else raise (Error("No definition found for " ^x.idText, d.drange))

                        | Some (prefix, let_x, rest_impl) ->
                          if d.quals |> List.contains Assumption
                          then raise (Error(Util.format2 "Assumed declaration %s is defined at %s" 
                                                         x.idText (Range.string_of_range let_x.drange), 
                                            d.drange))
                          else let remaining_iface_vals = 
                                    ds |> List.collect (fun d -> match d.d with
                                       | Val(x, _) -> [x]
                                       | _ -> []) in
                                begin match prefix |> List.tryFind (fun d -> remaining_iface_vals |> Util.for_some (fun x -> is_let x d)) with 
                                    | Some d -> raise (Error (Util.format2 "%s is out of order with %s" (decl_to_string d) (decl_to_string let_x), d.drange))
                                    | _ ->
                                      begin match let_x.d with 
                                         | TopLevelLet(_, defs) ->
                                           let def_lids = lids_of_let defs in //let rec x and y, etc.
                                           let iface_prefix_opt = iface |> FStar.Util.prefix_until (fun d -> 
                                            match d.d with 
                                                | Val(y, _) -> 
                                                  not (def_lids |> Util.for_some (id_eq_lid y))

                                                | _ -> true) in
                                           let all_vals_for_defs, rest_iface = 
                                                  match iface_prefix_opt with 
                                                    | None -> //only val x, val y left in the interface
                                                      iface, [] 

                                                    | Some (all_vals_for_defs, first_non_val, rest_iface) -> 
                                                      all_vals_for_defs, first_non_val::rest_iface in
                                           let hoist = prefix@all_vals_for_defs@[let_x] in
                                           aux (hoist::out) rest_iface rest_impl

                                         | _ -> failwith "Impossible"
                                      end
                                end
                       end
                    end

                | _ -> aux ([d]::out) ds impl 
    in
	if Options.ml_ish ()
	then aux_ml iface impl
	else aux [] iface impl