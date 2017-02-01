(*
  Copyright 2008-2014 Microsoft Research

  Authors: Nikhil Swamy, ...

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
module FStar.ToSyntax.Resugar //we should rename FStar.ToSyntax to something else
open FStar.All
open FStar.Syntax.Syntax
module I = FStar.Ident
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module A  = FStar.Parser.AST

let bv_as_unique_ident (x:S.bv) : I.ident =
    let unique_name =  x.ppname.idText ^ "__" ^ (string_of_int x.index) in
    I.mk_ident (unique_name, x.ppname.idRange)

let resugar_arg_qual (q:option<S.arg_qualifier>) : option<A.arg_qualifier> =
   match q with
   | None -> None
   | Some (Implicit b) -> Some A.Implicit  //TODO: how should we map this flag back to the surface?
   | Some Equality -> Some A.Equality

let rec resugar_term (t : S.term) : A.term =
    let mk (a:A.term') : A.term =
        //augment `a` with its source position
        //and an Unknown level (the level is unimportant ... we should maybe remove it altogether)
        A.mk_term a t.pos A.Un
    in
    match (SS.compress t).n with //always call compress before case-analyzing a S.term
    | Tm_delayed _ ->
      failwith "This case is impossible after compress"

    | Tm_bvar _ ->
      failwith "This case is impossible, if all binders are properly opened"

    | Tm_name x -> //a lower-case identifier
      //this is is too simplistic
      //the resulting unique_name is very ugly
      //it would be better to try to use x.ppname alone, unless the suffix is deemed semantically necessary
      let l = FStar.Ident.lid_of_ids [bv_as_unique_ident x] in
      mk (A.Var l)

    | Tm_fvar fv -> //a top-level identifier, may be lowercase or upper case
      //should be A.Var if lowercase
      //and A.Name if uppercase
      failwith "Not yet implemented"

    | Tm_abs(xs, body, _) -> //fun x1 .. xn -> body
      //before inspecting any syntactic form that has binding structure
      //you must call SS.open_* to replace de Bruijn indexes with names
      let xs, body = SS.open_term xs body in
      let patterns = xs |> List.map (fun (x, qual) ->
        //x.sort contains a type annotation for the bound variable
        //the pattern `p` below only contains the variable, not the annotation
        //but, if the user wrote the annotation, then we should record that and print it back
        //additionally, if we're in verbose mode, e.g., if --print_bound_var_types is set
        //    then we should print the annotation too
        let p = A.PatVar(bv_as_unique_ident x, resugar_arg_qual qual) in
        A.mk_pattern p (S.range_of_bv x)) in
      let body = resugar_term body in
      mk (A.Abs(patterns, body))

    | _ -> failwith "resugar_term: case not yet implemented"