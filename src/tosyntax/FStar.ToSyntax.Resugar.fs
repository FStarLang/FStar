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
open FStar.Ident
open FStar.Util
open FStar.Const
open FStar.Syntax.Print
module I = FStar.Ident
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module A  = FStar.Parser.AST
module C = FStar.Syntax.Const
module U = FStar.Syntax.Util
module BU = FStar.Util

let bv_as_unique_ident (x:S.bv) : I.ident =
  let unique_name =  x.ppname.idText ^ "__" ^ (string_of_int x.index) in
  I.mk_ident (unique_name, x.ppname.idRange)

let resugar_arg_qual (q:option<S.arg_qualifier>) : option<A.arg_qualifier> =
  match q with
    | None -> None
    | Some (Implicit b) -> Some A.Implicit  //TODO: how should we map this flag back to the surface?
    | Some Equality -> Some A.Equality

let rec universe_to_int n u =
  match u with 
    | U_succ u -> universe_to_int (n+1) u
    | _ -> (n, u)

let rec resugar_universe (u:S.universe) r: A.term =
  let mk (a:A.term') r: A.term =
      //augment `a` an Unknown level (the level is unimportant ... we should maybe remove it altogether)
      A.mk_term a r A.Un
  in
  begin match u with 
    | U_zero -> 
      mk (A.Const(Const_int ("0", None))) r 

    | U_succ _ ->
      let (n, u) = universe_to_int 0 u in
      begin match u with
      | U_zero -> 
        mk (A.Const(Const_int(string_of_int n, Some (Unsigned, Int16)))) r 
      
      | _ -> 
        let e1 = mk (A.Const(Const_int(string_of_int n, Some (Unsigned, Int16)))) r in
        let e2 = resugar_universe u r in
        mk (A.Op("+", [e1; e2])) r 
      end

    | U_max([]) -> failwith "Impossible: U_max without arguments"

    | U_max (_1::_2) ->
      let rec aux e = function
        | [] -> e
        | hd::tl ->
          let e = mk (A.App(e, resugar_universe hd r, A.Nothing)) r in
          aux e tl 
      in
      let t = mk (A.Var(lid_of_path ["max"] r)) r in
      let e = mk (A.App(t, resugar_universe _1 r, A.Nothing)) r in
      aux e _2

    | U_name u -> mk (A.Uvar(u)) r
    | U_unif _ -> mk A.Wild r
    | U_bvar _ -> failwith "U_bvar is impossible in resugar universe"
    | U_unknown -> failwith "U_unknow is impossible in resugar universe"
  end

let string_to_op s =
  let (|Prefix|_|) (p:string) (s:string) =
    if s.StartsWith(p) then
        Some(s.Substring(p.Length))
    else
        None
  in 
  let name_of_op = function
    | "Amp" -> Some "&"
    | "At" -> Some "@"
    | "Plus" -> Some "+"
    | "Minus" -> Some "-"
    | "Subtraction" -> Some "-"
    | "Slash" -> Some "/"
    | "Less" -> Some "<"
    | "Equals" -> Some "="
    | "Greater" -> Some ">"
    | "Underscore" -> Some "_"
    | "Bar" -> Some "|"
    | "Bang" -> Some "!" 
    | "Hat" -> Some "^"
    | "Percent" -> Some "%"
    | "Star" -> Some "*"
    | "Question" -> Some "?"
    | "Colon" -> Some ":"
    | _ -> None
  in
  match s with 
  | "op_String_Assignment" -> Some ".[]<-"
  | "op_Array_Assignment" -> Some ".()<-"
  | "op_String_Access" -> Some ".[]"
  | "op_Array_Access" -> Some ".()"
  | Prefix "op__" op -> name_of_op op
  | _ -> None

let resugar_match_pat (p:S.pat) : A.pattern = 
  (* We lose information when desugar PatAscribed to able to resugar it back *)
  let mk a = A.mk_pattern a p.p in
  let rec aux (p:S.pat) = 
    match p.v with
    | Pat_constant c -> mk (A.PatConst c)

    | Pat_disj args ->
      let args = List.map(fun p -> aux p) args in
      mk (A.PatOr args)

    | Pat_cons (fv, []) ->
      mk (A.PatName fv.fv_name.v)

    | Pat_cons(fv, args) when fv.fv_name.v.str.Equals C.cons_lid ->
      failwith "PatList not resugared yet"

    | Pat_cons(fv, args) when U.is_tuple_data_lid' fv.fv_name.v || U.is_dtuple_data_lid' fv.fv_name.v ->
      failwith "PatTuple not resugared yet"

    | Pat_cons({fv_qual=Some (Record_ctor _)}, args) ->
      (* need to find the corresponding record and go through the record.fields *)
      (* if the pattern is not Wild, then we have the pattern for the field to make the (lid*pattern) *)
      failwith "PatRecord not resugared yet"

    | Pat_cons (fv, args) ->
      let args = List.map (fun (p, b) -> aux p) args in
      mk (A.PatApp(mk (A.PatName fv.fv_name.v), args))

    | Pat_var v -> 
      (* both A.PatTvar and A.PatVar are desugared to S.Pat_var, only resugar back as PatVar*)
      begin match string_to_op v.ppname.idText with
       | Some op -> mk (A.PatOp op)
       | None -> mk (A.PatVar (bv_as_unique_ident v, None))
      end

    | Pat_wild _ -> mk (A.PatWild)

    | Pat_dot_term (bv, term) -> failwith "case Pat_dot_term is impossible"
  in
    aux p

let resugar_term_as_op(t:S.term) : option<string> =
  let infix_prim_ops = [
    (C.op_Addition    , "+" );
    (C.op_Subtraction , "-" );
    (C.op_Minus       , "-" );
    (C.op_Multiply    , "*" );
    (C.op_Division    , "/" );
    (C.op_Modulus     , "%" );
    (C.read_lid       , "!" );
    (C.list_append_lid, "@" );
    (C.list_tot_append_lid,"@");
    (C.strcat_lid     , "^" );
    (C.pipe_right_lid , "|>");
    (C.pipe_left_lid  , "<|");
    (C.op_Eq          , "=" );
    (C.op_ColonEq     , ":=");
    (C.op_notEq       , "<>");
    (C.not_lid        , "~" );
    (C.op_And         , "&&");
    (C.op_Or          , "||");
    (C.op_LTE         , "<=");
    (C.op_GTE         , ">=");
    (C.op_LT          , "<" );
    (C.op_GT          , ">" );
    (C.op_Modulus     , "mod");
    (C.and_lid     , "/\\");
    (C.or_lid      , "\\/");
    (C.imp_lid     , "==>");
    (C.iff_lid     , "<==>");
    (C.precedes_lid, "<<");
    (C.eq2_lid     , "==");
    (C.precedes_lid, "<<");
    (C.eq3_lid     , "===");
    (C.forall_lid  , "forall");
    (C.exists_lid  , "exists");
    (C.salloc_lid  , "alloc")
  ] in
  let rec find  f l  = match l with
    | [] -> (None, false)
    | hd::tl -> if f hd then (Some(snd hd), true) else find f tl
  in
  let find_op (x:fv) xs  =
    find (fun p -> fv_eq_lid x (fst p)) xs
  in 
  match (SS.compress t).n with 
    | Tm_fvar fv -> 
      let (op, b) = find_op fv infix_prim_ops in
      if b then op 
      else 
        let str = if fv.fv_name.v.nsstr.Length=0 then fv.fv_name.v.str 
          else fv.fv_name.v.str.Substring(fv.fv_name.v.nsstr.Length+1) in 
        if str.StartsWith("dtuple") then Some "dtuple"
        else if str.StartsWith("tuple") then Some "tuple"
        else if str.StartsWith("try_with") then Some "try_with"
        else if fv_eq_lid fv C.sread_lid then Some fv.fv_name.v.str
        //else if fv.fv_name.v.str.Contains(U.field_projector_prefix) then Some fv.fv_name.v.str
        else None
    | _ -> None

let is_true_pat (p:S.pat) : bool = match p.v with
    | Pat_constant (Const_bool true) -> true
    | _ -> false

let is_wild_pat (p:S.pat) : bool = match p.v with
    | Pat_wild _ -> true
    | _ -> false 

let rec resugar_term (t : S.term) : A.term =
    (* Cannot resugar term back to NamedTyp or Paren *)
    let mk (a:A.term') : A.term =
        //augment `a` with its source position
        //and an Unknown level (the level is unimportant ... we should maybe remove it altogether)
        A.mk_term a t.pos A.Un
    in
    let name a r = 
        // make a Name term'
        A.Name (lid_of_path [a] r)
    in
    let var a r = 
        // make a Var term'
        A.Var (lid_of_path [a] r)
    in
    let resugar_sequence (e:A.term) : A.term =  match e.tm with
      | A.Let(_, [p, t1], t2) ->
        mk (A.Seq(t1, t2))
      | _ -> 
        failwith "This case is impossible for sequence" 
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
      let a = fv.fv_name.v in
      let s = if fv.fv_name.v.nsstr.Length=0 then a.str 
          else a.str.Substring(fv.fv_name.v.nsstr.Length+1) in 
      if (lid_equals a C.assert_lid 
            || lid_equals a C.assume_lid
            || Char.uppercase (String.get s 0) <> String.get s 0) then
        mk (var s t.pos)
      else 
        mk (name s t.pos)

    | Tm_uinst(e, universes) ->
      let e = resugar_term e in
      let rec aux e = function
        | [] -> e
        | hd::tl ->
          let univ = resugar_universe hd t.pos in
          let e = mk (A.App(e, univ, A.UnivApp)) in
          aux e tl in
      aux e universes

    | Tm_constant c -> 
      if is_teff t 
      then mk (name "Effect" t.pos)
      else mk (A.Const c)
        
    | Tm_type u -> 
        begin match u with 
        | U_zero ->  mk (name "Type0" t.pos) 
        | U_unknown -> mk (name "Type" t.pos)
        | _ -> 
            let u = resugar_universe u t.pos in
            let l = lid_of_path ["Type"] t.pos in
            mk (A.Construct (l, [(u, A.Nothing)]))
        end
        
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

    | Tm_arrow(xs, body) ->
      let xs, body = SS.open_comp xs body in
      let body = resugar_comp body in
      //let xs, body = SS.open_term xs body in
      let xs = xs |> List.map (fun (b, qual) -> resugar_bv_as_binder b t.pos) in
      let rec aux body = function
        | [] -> body
        | hd::tl ->
          let body = mk (A.Product([hd], body)) in
          aux body tl in
      aux body xs

    | Tm_refine(b, e) ->
      (* bv * term -> binder * term *)
      let b, e = SS.open_bv b e in 
      let b = resugar_bv_as_binder b t.pos in
      mk (A.Refine(b, resugar_term e))

    | Tm_app(e, args) ->
      (* Op("=!=", args) is desugared into Op("~", Op("==") and not resugared back as "=!=" *)
      begin match resugar_term_as_op e with
        | None->
          let args = args |> List.map (fun (e, qual) ->
            resugar_term e) in
          let e = resugar_term e in
          let rec aux e = function
            | [] -> e
            | hd::tl ->
              let e = mk (A.App(e, hd, A.Nothing)) in
              aux e tl in
          aux e args

        | Some "tuple" ->
          let args = args |> List.map (fun (e, qual) ->
            resugar_term e) in
          let rec aux e = function
            | [] -> e
            | hd::tl ->
              let e = mk (A.Op("*", [e;hd])) in
              aux e tl in
          let e = mk(A.Op("*", [args.Head; args.Tail.Head])) in
          aux e args.Tail.Tail

        | Some "dtuple" -> 
          (* this is desugared from Sum(binders*term) *)
          let rec last = function
            | hd :: [] -> hd
            | hd :: tl -> last tl
            | _ -> failwith "Empty list." in
          let body, _ = last args in
          let binders, body = match (SS.compress body).n with
            | Tm_abs(xs, body, _) ->
                let xs, body = SS.open_term xs body in
                let xs = xs |> List.map (fun (b, qual) -> resugar_bv_as_binder b t.pos) in 
                let body = resugar_term body in
                xs, body
            | _ ->
              [], resugar_term body in
          mk (A.Sum(binders, body))

        (*| Some field_projector when (U.field_projector_contains_constructor field_projector) ->
          (* get the field name from the fvar *)
          let args = args |> List.map (fun (e, qual) ->
            resugar_term e) in
          let f = lid_of_path [field_projector] t.pos in
          mk (A.Project(args.Head, f))
        *)

        | Some ref_read when (ref_read = C.sread_lid.str) ->
          let (t, _) = args.Head in
          begin match (SS.compress t).n with
            | Tm_fvar fv when (U.field_projector_contains_constructor fv.fv_name.v.str) ->
              let f = lid_of_path [fv.fv_name.v.str] t.pos in
              mk (A.Project(resugar_term t, f))
            | Tm_fvar fv when (BU.starts_with fv.fv_name.v.str I.reserved_prefix) ->
              mk (A.Discrim(lid_of_path [fv.fv_name.v.str] t.pos))
            | _ -> resugar_term t
          end

        | Some "try_with" ->
          let body, handler = match args with
            | [(a1, _);(a2, _)] -> a1, a2
            | _ -> failwith("wrong arguments to try_with") in
          (* where a1 and a1 is Tm_abs(Tm_match)) *)
          let decomp term = match (term.n) with
            | Tm_abs(x, e, _) -> 
              let x, e = SS.open_term x e in
              e
            | _ -> failwith("unexpected") in
          let body = resugar_term (decomp body) in
          let handler = resugar_term (decomp handler) in
          let e = match (body.tm) with 
            | A.Match(e, [(_,_,b)]) -> b
            | _ -> failwith("unexpected body format") in
          let branches = match (handler.tm) with
            | A.Match(e, branches) -> branches
            | _ -> failwith("unexpected handler format") in
          mk (A.TryWith(e, branches))

        | Some op when op = "forall" || op = "exists" ->
          (* desugared from QForall(binders * patterns * body) to Tm_app(forall, Tm_abs(binders, Tm_meta(body, meta_pattern(list<args>)*)
          let (body, _) = args.Head in
          begin match (SS.compress body).n with
            | Tm_abs(xs, body, _) ->
                let xs, body = SS.open_term xs body in
                let xs = xs |> List.map (fun (b, qual) -> resugar_bv_as_binder b t.pos) in 
                let pats, body = match (SS.compress body).n with
                  | Tm_meta(e, m) ->
                    let body = resugar_term e in
                    let resugar_pats pats = List.map (fun es -> es |> List.map (fun (e, _) -> resugar_term e)) pats in
                    let pats = match m with 
                      | Meta_pattern pats -> resugar_pats pats
                      | _ -> failwith "wrong pattern format for QForall" 
                    in
                    pats, body
                  | _ -> [], resugar_term body
                in
                if op = "forall" then mk (A.QForall(xs, pats, body)) else mk (A.QExists(xs, pats, body))   
                    
            | _ -> failwith "wrong format to QForall"
          end

        | Some "alloc" ->
          let (e, _ ) = args.Head in
          resugar_term e

        | Some op ->
          let args = args |> List.map (fun (e, qual) ->
            resugar_term e) in
          mk (A.Op(op, args))
      end
    
    | Tm_match(e, [(pat1, _, t1); (pat2, _, t2)]) when is_true_pat pat1 && is_wild_pat pat2 ->
      mk (A.If(resugar_term e, resugar_term t1, resugar_term t2))

    | Tm_match(e, branches) ->
      let resugar_branch (pat, wopt,b) =
        let pat = resugar_match_pat pat in
        let wopt = match wopt with
          | None -> None
          | Some e -> Some (resugar_term e) in
        let b = resugar_term b in
        (pat, wopt, b) in
        mk (A.Match(resugar_term e, List.map resugar_branch branches))

    | Tm_ascribed(e, comp, _) ->
      let term = match comp with
          | Inl n -> (* term *)
            resugar_term n
          | Inr n -> (* comp *)
            resugar_comp n in
      mk (A.Ascribed(resugar_term e, term))

    | Tm_let((is_rec, bnds), body) ->
      let mk_pat a = A.mk_pattern a t.pos in
      let resugar_one_binding bnd = 
        let binders, term, is_pat_app = match (SS.compress bnd.lbdef).n with
          | Tm_abs(b, t, _) -> 
            let b, t = SS.open_term b t in
            b, t, true
          | _ -> [], bnd.lbdef, false
        in 
        let pat, term = match bnd.lbname with
          | Inr fv -> mk_pat (A.PatName fv.fv_name.v), term
          | Inl bv -> 
            let bv, term = SS.open_bv bv term in 
            mk_pat (A.PatVar (bv_as_unique_ident bv, None)), term
        in
        if is_pat_app then
          let args = binders |> List.map (fun (bv, _) -> mk_pat(A.PatVar (bv_as_unique_ident bv, None))) in
          (mk_pat (A.PatApp (pat, args)), resugar_term term)
        else
          (pat, resugar_term term)
      in
      let bnds = List.map (resugar_one_binding) bnds in
      let body = resugar_term body in
      mk (A.Let((if is_rec then A.Rec else A.NoLetQualifier), bnds, body))
    | Tm_uvar _ ->
      failwith "This case is impossible since it is not created in desugar"

    | Tm_meta(e, m) ->
       let resugar_meta_desugared = function
          | Data_app ->
              begin match (SS.compress e).n with
                | Tm_app(head, args) ->
                    let rec aux h = match ((SS.compress h).n) with
                      | Tm_fvar fv -> lid_of_fv fv, []
                      | Tm_uinst(h, u) -> 
                        let h, l = aux h in
                        h, l@u
                      | _ -> failwith "wrong Data_app head format" 
                    in
                    let head, universes = aux head in
                    let universes = List.map (fun u -> (resugar_universe u t.pos, A.UnivApp)) universes in
                    let args = List.map (fun (t, _) -> (resugar_term t, A.Nothing)) args in
                    mk (A.Construct(head, args@universes))
                | _ -> failwith "wrong Data_app format"
              end
          | Sequence ->
              let term = resugar_term e in
              resugar_sequence term
          | Primop (* doesn't seem to be generated by desugar *)
          | Masked_effect (* doesn't seem to be generated by desugar *)
          | Meta_smt_pat -> (* nothing special, just resugar the term *)
              resugar_term e
          | Mutable_alloc ->
              let term = resugar_term e in
              begin match term.tm with
                | A.Let(A.NoLetQualifier,l,t) -> mk (A.Let(A.Mutable, l, t))
                | _ -> failwith "mutable_alloc should have let term with no qualifier"
              end
          | Mutable_rval ->
              let fv = S.lid_as_fv C.sread_lid Delta_constant None in
              begin match (SS.compress e).n with 
                | Tm_app({n=Tm_fvar fv}, [(term, _)])-> resugar_term term
                | _ -> failwith "mutable_rval should have app term"
              end
      in
      begin match m with
      | Meta_pattern pats ->
          failwith "This case is impossible, if Forall and Exist is properly resugared"
      | Meta_labeled (l, _, p) ->
          mk (A.Labeled(resugar_term e, l, p))
      | Meta_desugared i -> 
          resugar_meta_desugared i
      | Meta_named _ 
      | Meta_monadic _ 
      | Meta_monadic_lift _ -> 
          failwith "cases not generated by desugar"
      end
    
    | Tm_unknown _ -> mk A.Wild

and resugar_comp (c:S.comp) : A.term =
  let mk (a:A.term') : A.term =
        //augment `a` with its source position
        //and an Unknown level (the level is unimportant ... we should maybe remove it altogether)
        A.mk_term a c.pos A.Un
  in
  match (c.n) with 
  | Total (typ, _) ->
    let t = resugar_term typ in
    mk (A.Construct(C.effect_Tot_lid, [(t, A.Nothing)]))

  | GTotal (typ, _) ->
    let t = resugar_term typ in
    mk (A.Construct(C.effect_GTot_lid, [(t, A.Nothing)]))

  | Comp c ->
    let universe = List.map (fun u -> resugar_universe u) c.comp_univs in
    let result = (resugar_term c.result_typ, A.Nothing) in
    let args = 
      if (lid_equals c.effect_name C.effect_Lemma_lid) then
        let rec aux l = function
          | [] -> l
          | (t,aq)::tl -> 
            match (t.n) with
            | Tm_fvar fv when S.fv_eq_lid fv C.true_lid ->
              aux l tl
            | Tm_meta _ (* where metadata == Meta_desuagard(Meta_smt_pat) *) ->
              aux l tl
            | _ -> 
              aux ((t,aq)::l) tl
        in
        aux [] c.effect_args
      else 
        c.effect_args 
    in
    let args = List.map(fun (e,_) -> (resugar_term e, A.Nothing)) args in
    let rec aux l = function 
      | [] -> l
      | hd::tl ->
        match hd with 
          | DECREASES e ->
            let e = (resugar_term e, A.Nothing) in
            aux (e::l) tl
          | _ -> aux l tl
    in
    let decrease = aux [] c.flags in
    mk (A.Construct(c.effect_name, decrease@args))
    
 and resugar_bv_as_binder (x:S.bv) r: A.binder =
  let e = resugar_term x.sort in
  match (e.tm) with 
    | A.Wild ->
        A.mk_binder (A.Variable(bv_as_unique_ident x)) r A.Type_level None
    | _ ->
        if (S.is_null_bv x) then
          A.mk_binder (A.NoName(e)) r A.Type_level None
        else 
          A.mk_binder (A.Annotated(bv_as_unique_ident x, e)) r A.Type_level None