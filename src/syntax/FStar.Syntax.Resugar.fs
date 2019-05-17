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
module FStar.Syntax.Resugar //we should rename FStar.ToSyntax to something else
open FStar
open FStar.ST
open FStar.Exn
open FStar.All
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Util
open FStar.Const
open FStar.List
open FStar.Parser.AST

module I = FStar.Ident
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module A  = FStar.Parser.AST
module C = FStar.Parser.Const
module U = FStar.Syntax.Util
module BU = FStar.Util
module D = FStar.Parser.ToDocument
module UF = FStar.Syntax.Unionfind
module E = FStar.Errors
module DsEnv = FStar.Syntax.DsEnv

(* Helpers to print/debug the resugaring phase *)
let doc_to_string doc = FStar.Pprint.pretty_string (float_of_string "1.0") 100 doc
let parser_term_to_string t = doc_to_string (D.term_to_document t)
let parser_pat_to_string t = doc_to_string (D.pat_to_document t)

let map_opt = List.filter_map

let bv_as_unique_ident (x:S.bv) : I.ident =
  let unique_name =
    if starts_with reserved_prefix x.ppname.idText
    ||  Options.print_real_names () then
      x.ppname.idText ^ (string_of_int x.index)
    else
      x.ppname.idText
  in
  I.mk_ident (unique_name, x.ppname.idRange)

let filter_imp a =
  (* keep typeclass args *)
  a |> List.filter (function | (_, Some (S.Meta t)) when U.is_fvar C.tcresolve_lid t -> true
                             | (_, Some (S.Implicit _))
                             | (_, Some (S.Meta _)) -> false
                             | _ -> true)

let filter_pattern_imp xs =
  List.filter (fun (_, is_implicit) -> not is_implicit) xs

let label s t =
  if s = "" then t
  else A.mk_term (A.Labeled (t,s,true)) t.range A.Un

let rec universe_to_int n u =
  match u with
    | U_succ u -> universe_to_int (n+1) u
    | _ -> (n, u)

let universe_to_string univs =
  if (Options.print_universes()) then
    List.map (fun x -> x.idText) univs |> String.concat  ", "
  else ""

// resugar_universe' included for consistency (it doesn't use its environment)
let rec resugar_universe' (env: DsEnv.env) (u:S.universe) r: A.term =
  resugar_universe u r

and resugar_universe (u:S.universe) r: A.term =
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
        mk (A.Const(Const_int(string_of_int n, None))) r

      | _ ->
        let e1 = mk (A.Const(Const_int(string_of_int n, None))) r in
        let e2 = resugar_universe u r in
        mk (A.Op(Ident.id_of_text "+", [e1; e2])) r
      end

    | U_max l ->
      begin match l with
      | [] -> failwith "Impossible: U_max without arguments"
      | _ ->
        let t = mk (A.Var(lid_of_path ["max"] r)) r in
        List.fold_left(fun acc x -> mk (A.App(acc, resugar_universe x r, A.Nothing)) r) t l
      end

    | U_name u -> mk (A.Uvar(u)) r
    | U_unif _ -> mk A.Wild r
    | U_bvar x ->
      (* This case can happen when trying to print a subterm of a term that is not opened.*)
      let id = I.mk_ident (strcat "uu__univ_bvar_" (string_of_int x), r) in
      mk (A.Uvar(id)) r

    | U_unknown -> mk A.Wild r (* not sure what to resugar to since it is not created by desugar *)
  end

let string_to_op s =
  let name_of_op = function
    | "Amp" ->  Some ("&", None)
    | "At" -> Some ("@", None)
    | "Plus" -> Some ("+", None)
    | "Minus" -> Some ("-", None)
    | "Subtraction" -> Some ("-", Some 2)
    | "Tilde" -> Some ("~", None)
    | "Slash" -> Some ("/", None)
    | "Backslash" -> Some ("\\", None)
    | "Less" -> Some ("<", None)
    | "Equals" -> Some ("=", None)
    | "Greater" -> Some (">", None)
    | "Underscore" -> Some ("_", None)
    | "Bar" -> Some ("|", None)
    | "Bang" -> Some ("!", None)
    | "Hat" -> Some ("^", None)
    | "Percent" -> Some ("%", None)
    | "Star" -> Some ("*", None)
    | "Question" -> Some ("?", None)
    | "Colon" -> Some (":", None)
    | "Dollar" -> Some ("$", None)
    | "Dot" -> Some (".", None)
    | _ -> None
  in
  match s with
  | "op_String_Assignment" -> Some (".[]<-", None)
  | "op_Array_Assignment" -> Some (".()<-", None)
  | "op_Brack_Lens_Assignment" -> Some (".[||]<-", None)
  | "op_Lens_Assignment" -> Some (".(||)<-", None)
  | "op_String_Access" -> Some (".[]", None)
  | "op_Array_Access" -> Some (".()", None)
  | "op_Brack_Lens_Access" -> Some (".[||]", None)
  | "op_Lens_Access" -> Some (".(||)", None)
  | _ ->
    if BU.starts_with s "op_" then
      let s = BU.split (BU.substring_from s (String.length "op_"))  "_" in
      match s with
      | [op] -> name_of_op op
      | _ ->
        let op = List.fold_left(fun acc x -> match x with
                                  | Some (op, _) -> acc ^ op
                                  | None -> failwith "wrong composed operator format")
                                  "" (List.map name_of_op s)  in
        Some (op, None)
    else
      None

type expected_arity = option<int>
let rec resugar_term_as_op (t:S.term) : option<(string*expected_arity)> =
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
    (C.eq3_lid     , "===");
    (C.forall_lid  , "forall");
    (C.exists_lid  , "exists");
    (C.salloc_lid  , "alloc")
  ] in
  let fallback fv =
    match infix_prim_ops |> BU.find_opt (fun d -> fv_eq_lid fv (fst d)) with
    | Some op ->
      Some (snd op, None)
    | _ ->
      let length = String.length(fv.fv_name.v.nsstr) in
      let str = if length=0 then fv.fv_name.v.str
          else BU.substring_from fv.fv_name.v.str (length+1) in
      if BU.starts_with str "dtuple" then Some ("dtuple", None)
      else if BU.starts_with str "tuple" then Some ("tuple", None)
      else if BU.starts_with str "try_with" then Some ("try_with", None)
      else if fv_eq_lid fv C.sread_lid then Some (fv.fv_name.v.str, None)
      else None
  in
  match (SS.compress t).n with
    | Tm_fvar fv ->
      let length = String.length(fv.fv_name.v.nsstr) in
      let s = if length=0 then fv.fv_name.v.str
              else BU.substring_from fv.fv_name.v.str (length+1) in
      begin match string_to_op s with
        | Some t -> Some t
        | _ -> fallback fv
      end
    | Tm_uinst(e, us) ->
      resugar_term_as_op e
    | _ -> None

let is_true_pat (p:S.pat) : bool = match p.v with
    | Pat_constant (Const_bool true) -> true
    | _ -> false

let is_wild_pat (p:S.pat) : bool = match p.v with
    | Pat_wild _ -> true
    | _ -> false

let is_tuple_constructor_lid lid =
  C.is_tuple_data_lid' lid || C.is_dtuple_data_lid' lid

let may_shorten lid =
  match lid.str with
  | "Prims.Nil"
  | "Prims.Cons" -> false
  | _ -> not (is_tuple_constructor_lid lid)

let maybe_shorten_fv env fv =
  let lid = fv.fv_name.v in
  if may_shorten lid then DsEnv.shorten_lid env lid else lid

let rec resugar_term' (env: DsEnv.env) (t : S.term) : A.term =
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
    match (SS.compress t).n with //always call compress before case-analyzing a S.term
    | Tm_delayed _ ->
      failwith "Tm_delayed is impossible after compress"

    | Tm_lazy i ->
      resugar_term' env (U.unfold_lazy i)

    | Tm_bvar x ->
      (* this case can happen when printing a subterm of a term that is not opened *)
      let l = FStar.Ident.lid_of_ids [bv_as_unique_ident x] in
      mk (A.Var l)

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
      let length = String.length(fv.fv_name.v.nsstr) in
      let s = if length=0 then a.str
          else BU.substring_from a.str (length+1) in
      let is_prefix = I.reserved_prefix ^ "is_" in
      if BU.starts_with s is_prefix then
        let rest = BU.substring_from s (String.length is_prefix) in
        mk (A.Discrim(lid_of_path [rest] t.pos))
      else if BU.starts_with s U.field_projector_prefix then
        let rest = BU.substring_from s (String.length U.field_projector_prefix) in
        let r = BU.split rest U.field_projector_sep in
        begin match r with
          | [fst; snd] ->
            let l = lid_of_path [fst] t.pos in
            let r = I.mk_ident (snd, t.pos) in
            mk (A.Projector(l, r ))
          | _ ->
            failwith "wrong projector format"
        end
       else if (lid_equals a C.assert_lid || lid_equals a C.assume_lid
                || Char.uppercase (String.get s 0) <> String.get s 0) then
         mk (A.Var (maybe_shorten_fv env fv))
       else // FIXME check in environment instead of checking case
         mk (A.Construct (maybe_shorten_fv env fv, []))

    | Tm_uinst(e, universes) ->
      let e = resugar_term' env e in
      if Options.print_universes() then
        let univs = List.map (fun x -> resugar_universe x t.pos) universes in
        match e with
        | { tm = A.Construct (hd, args); range = r; level = l } ->
          let args = args @ (List.map (fun u -> (u, A.UnivApp)) univs) in
          A.mk_term (A.Construct (hd, args)) r l
        | _ ->
          List.fold_left (fun acc u -> mk (A.App (acc, u, A.UnivApp))) e univs
      else
        e

    | Tm_constant c ->
      if is_teff t
      then mk (name "Effect" t.pos)
      else mk (A.Const c)

    | Tm_type u ->
      let nm, needs_app =
        match u with
        | U_zero ->  "Type0", false
        | U_unknown -> "Type", false
        | _ -> "Type", true in
      let typ = mk (name nm t.pos) in
      if needs_app && Options.print_universes ()
      then mk (A.App (typ, resugar_universe u t.pos, UnivApp))
      else typ

    | Tm_abs(xs, body, _) -> //fun x1 .. xn -> body
      //before inspecting any syntactic form that has binding structure
      //you must call SS.open_* to replace de Bruijn indexes with names
      let xs, body = SS.open_term xs body in
      let xs = if Options.print_implicits () then xs else filter_imp xs in
      let body_bv = FStar.Syntax.Free.names body in
      let patterns = xs |> List.choose (fun (x, qual) ->
        //x.sort contains a type annotation for the bound variable
        //the pattern `p` below only contains the variable, not the annotation
        //but, if the user wrote the annotation, then we should record that and print it back
        //additionally, if we're in verbose mode, e.g., if --print_bound_var_types is set
        //    then we should print the annotation too
        resugar_bv_as_pat env x qual body_bv)
      in
      let body = resugar_term' env body in
      mk (A.Abs(patterns, body))

    | Tm_arrow(xs, body) ->
      let xs, body = SS.open_comp xs body in
      let xs = if (Options.print_implicits()) then xs else filter_imp xs in
      let body = resugar_comp' env body in
      let xs = xs |> map_opt (fun b -> resugar_binder' env b t.pos) |> List.rev in
      let rec aux body = function
        | [] -> body
        | hd::tl ->
          let body = mk (A.Product([hd], body)) in
          aux body tl in
      aux body xs

    | Tm_refine(x, phi) ->
      (* bv * term -> binder * term *)
      let x, phi = SS.open_term [S.mk_binder x] phi in
      let b = BU.must (resugar_binder' env (List.hd x) t.pos) in
      mk (A.Refine(b, resugar_term' env phi))

    | Tm_app({n=Tm_fvar fv}, [(e, _)])
      when not (Options.print_implicits())
           && S.fv_eq_lid fv C.b2t_lid ->
      resugar_term' env e

    | Tm_app(e, args) ->
      (* Op("=!=", args) is desugared into Op("~", Op("==") and not resugared back as "=!=" *)
      let rec last = function
            | hd :: [] -> [hd]
            | hd :: tl -> last tl
            | _ -> failwith "last of an empty list"
      in
      let rec last_two = function
            | [] | [_] -> failwith "last two elements of a list with less than two elements "
            | [a1;a2] -> [a1;a2]
            | _::t -> last_two t
      in
      let resugar_as_app e args =
        let args =
          List.map (fun (e, qual) -> (resugar_term' env e, resugar_imp env qual)) args in
        match resugar_term' env e with
        | { tm = A.Construct (hd, previous_args); range = r; level = l } ->
          A.mk_term (A.Construct (hd, previous_args @ args)) r l
        | e ->
          List.fold_left (fun acc (x, qual) -> mk (A.App (acc, x, qual))) e args
      in
      let args = if Options.print_implicits () then args else filter_imp args
      in
      begin match resugar_term_as_op e with
        | None->
          resugar_as_app e args

        | Some ("tuple", _) ->
          let out =
              List.fold_left
                (fun out (x, _) ->
                    let x = resugar_term' env x in
                    match out with
                    | None -> Some x
                    | Some prefix ->
                      Some (mk(A.Op(Ident.id_of_text "*", [prefix; x]))))
                    None
                    args
          in
          Option.get out

        | Some ("dtuple", _) when List.length args > 0 ->
          (* this is desugared from Sum(binders*term) *)
          let args = last args in
          let body = match args with
            | [(b, _)] -> b
            | _ -> failwith "wrong arguments to dtuple"
          in
          begin match (SS.compress body).n with
            | Tm_abs(xs, body, _) ->
                let xs, body = SS.open_term xs body in
                let xs = if (Options.print_implicits()) then xs else filter_imp xs in
                let xs = xs |> map_opt (fun b -> resugar_binder' env b t.pos) in
                let body = resugar_term' env body in
                mk (A.Sum(List.map Inl xs, body))

            | _ ->
              let args = args |> List.map (fun (e, qual) ->
                resugar_term' env e) in
              let e = resugar_term' env e in
              List.fold_left(fun acc x -> mk (A.App(acc, x, A.Nothing))) e args
          end

        | Some ("dtuple", _) ->
          resugar_as_app e args

        | Some (ref_read, _) when (ref_read = C.sread_lid.str) ->
          let (t, _) = List.hd args in
          begin match (SS.compress t).n with
            | Tm_fvar fv when (U.field_projector_contains_constructor fv.fv_name.v.str) ->
              let f = lid_of_path [fv.fv_name.v.str] t.pos in
              mk (A.Project(resugar_term' env t, f))
            | _ -> resugar_term' env t
          end

        | Some ("try_with", _) when List.length args > 1 ->
          (* only the last two args are from original AST terms, others are added by typechecker *)
          (* TODO: we need a place to store the information in the args added by the typechecker *)
          let new_args = last_two args in
          let body, handler = match new_args with
            | [(a1, _);(a2, _)] -> a1, a2 (* where a1 and a1 is Tm_abs(Tm_match)) *)
            | _ ->
              failwith("wrong arguments to try_with")
          in
          let decomp term = match (SS.compress term).n with
            | Tm_abs(x, e, _) ->
              let x, e = SS.open_term x e in
              e
            | _ -> failwith("wrong argument format to try_with") in
          let body = resugar_term' env (decomp body) in
          let handler = resugar_term' env (decomp handler) in
          let rec resugar_body t = match (t.tm) with
            | A.Match(e, [(_,_,b)]) -> b
            | A.Let(_, _, b) -> b  // One branch Match that is resugared as Let
            | A.Ascribed(t1, t2, t3) ->
              (* this case happens when the match is wrapped in Meta_Monadic which is resugared to Ascribe*)
              mk (A.Ascribed(resugar_body t1, t2, t3))
            | _ -> failwith("unexpected body format to try_with") in
          let e = resugar_body body in
          let rec resugar_branches t = match (t.tm) with
            | A.Match(e, branches) -> branches
            | A.Ascribed(t1, t2, t3) ->
              (* this case happens when the match is wrapped in Meta_Monadic which is resugared to Ascribe*)
              (* TODO: where should we keep the information stored in Ascribed? *)
              resugar_branches t1
            | _ ->
              (* TODO: forall created by close_forall doesn't follow the normal forall format, not sure how to resugar back *)
              []
          in
          let branches = resugar_branches handler in
          mk (A.TryWith(e, branches))

        | Some ("try_with", _) ->
          resugar_as_app e args

        (* These have implicits, don't do the fancy printing when --print_implicits is on *)
        | Some (op, _) when (op = "=" || op = "==" || op = "===" || op = "@" || op = ":=" || op = "|>")
            && Options.print_implicits () ->
          resugar_as_app e args

        | Some (op, _) when op = "forall" || op = "exists" ->
          (* desugared from QForall(binders * patterns * body) to Tm_app(forall, Tm_abs(binders, Tm_meta(body, meta_pattern(list<args>)*)
          let rec uncurry xs pat (t:A.term) = match t.tm with
            | A.QExists(x, _, (_, p) , body)
            | A.QForall(x, _, (_, p), body)  // TODO: check the consistency of {:nopattern}?
              -> uncurry (x@xs) (p@pat) body
            | _ -> xs, pat, t
          in
          let resugar body = match (SS.compress body).n with
            | Tm_abs(xs, body, _) ->
                let xs, body = SS.open_term xs body in
                let xs = if (Options.print_implicits()) then xs else filter_imp xs in
                let xs = xs |> map_opt (fun b -> resugar_binder' env b t.pos) in
                let pats, body = match (SS.compress body).n with
                  | Tm_meta(e, m) ->
                    let body = resugar_term' env e in
                    let pats, body = match m with
                      | Meta_pattern (_, pats) ->
                        List.map (fun es -> es |> List.map (fun (e, _) -> resugar_term' env e)) pats,
                        body
                      | Meta_labeled (s, r, p) ->
                        // this case can occur in typechecker when a failure is wrapped in meta_labeled
                        [], mk (A.Labeled (body, s, p))
                      | _ -> failwith "wrong pattern format for QForall/QExists"
                    in
                    pats, body
                  | _ -> [], resugar_term' env body
                in
                let xs, pats, body = uncurry xs pats body in
                let xs = xs |> List.rev in
                if op = "forall"
                then mk (A.QForall(xs, false, (A.idents_of_binders xs t.pos, pats), body)) // TODO
                else mk (A.QExists(xs, false, (A.idents_of_binders xs t.pos, pats), body)) // TODO

            | _ ->
            (*forall added by typechecker.normalize doesn't not have Tm_abs as body*)
            (*TODO:  should we resugar them back as forall/exists or just as the term of the body *)
            if op = "forall" then mk (A.QForall([], false, ([], []), resugar_term' env body))
            else mk (A.QExists([], false, ([], []), resugar_term' env body))
          in
          (* only the last arg is from original AST terms, others are added by typechecker *)
          (* TODO: we need a place to store the information in the args added by the typechecker *)
          if List.length args > 0 then
            let args = last args in
            begin match args with
              | [(b, _)] -> resugar b
              | _ -> failwith "wrong args format to QForall"
            end
          else
            resugar_as_app e args

        | Some ("alloc", _) ->
          let (e, _ ) = List.hd args in
          resugar_term' env e

        | Some (op, expected_arity) ->
          let op = Ident.id_of_text op in
          let resugar args = args |> List.map (fun (e, qual) ->
            resugar_term' env e, resugar_imp env qual)
          in
           (* ignore the arguments added by typechecker *)
          (* TODO: we need a place to store the information in the args added by the typechecker *)
          //NS: this seems to produce the wrong output on things like
          begin
          match expected_arity with
          | None ->
            let resugared_args = resugar args in
            let expect_n = D.handleable_args_length op in
            if List.length resugared_args >= expect_n
            then let op_args, rest = BU.first_N expect_n resugared_args in
                 let head = mk (A.Op(op, List.map fst op_args)) in
                 List.fold_left
                        (fun head (arg, qual) -> mk (A.App (head, arg, qual)))
                        head
                        rest
            else resugar_as_app e args
          | Some n when List.length args = n -> mk (A.Op(op, List.map fst (resugar args)))
          | _ -> resugar_as_app e args
          end
    end

    | Tm_match(e, [(pat, wopt, t)]) ->
      (* for match expressions that have exactly 1 branch, instead of printing them as `match e with | P -> e1`
        it would be better to print it as `let P = e in e1`. *)
      (* only do it when pat is not Pat_disj since ToDocument only expects disjunctivePattern in Match and TryWith *)
      let pat, wopt, t = SS.open_branch (pat, wopt, t) in
      let branch_bv = FStar.Syntax.Free.names t in
      let bnds = [None, (resugar_pat' env pat branch_bv, resugar_term' env e)] in
      let body = resugar_term' env t in
      mk (A.Let(A.NoLetQualifier, bnds, body))

    | Tm_match(e, [(pat1, _, t1); (pat2, _, t2)]) when is_true_pat pat1 && is_wild_pat pat2 ->
      mk (A.If(resugar_term' env e, resugar_term' env t1, resugar_term' env t2))

    | Tm_match(e, branches) ->
      let resugar_branch (pat, wopt,b) =
        let pat, wopt, b = SS.open_branch (pat, wopt, b) in
        let branch_bv = FStar.Syntax.Free.names b in
        let pat = resugar_pat' env pat branch_bv in
        let wopt = match wopt with
          | None -> None
          | Some e -> Some (resugar_term' env e) in
        let b = resugar_term' env b in
        (pat, wopt, b) in
      mk (A.Match(resugar_term' env e, List.map resugar_branch branches))

    | Tm_ascribed(e, (asc, tac_opt), _) ->
      let term = match asc with
          | Inl n -> (* term *)
            resugar_term' env n
          | Inr n -> (* comp *)
            resugar_comp' env n in
      let tac_opt = Option.map (resugar_term' env) tac_opt in
      mk (A.Ascribed(resugar_term' env e, term, tac_opt))

    | Tm_let((is_rec, source_lbs), body) ->
      let mk_pat a = A.mk_pattern a t.pos in
      let source_lbs, body = SS.open_let_rec source_lbs body in
      let resugar_one_binding bnd =
        (* TODO : some stuff are open twice there ! (may have already been opened in open_let_rec) *)
        let attrs_opt =
            match bnd.lbattrs with
            | [] -> None
            | tms -> Some (List.map (resugar_term' env) tms)
        in
        let univs, td = SS.open_univ_vars bnd.lbunivs (U.mk_conj bnd.lbtyp bnd.lbdef) in
        let typ, def = match (SS.compress td).n with
          | Tm_app(_, [(t, _); (d, _)]) -> t, d
          | _ -> failwith "wrong let binding format"
        in
        let binders, term, is_pat_app = match (SS.compress def).n with
          | Tm_abs(b, t, _) ->
            let b, t = SS.open_term b t in
            let b = if (Options.print_implicits()) then b else filter_imp b in
            b, t, true
          | _ -> [], def, false
        in
        let pat, term = match bnd.lbname with
          | Inr fv -> mk_pat (A.PatName fv.fv_name.v), term
          | Inl bv ->
            mk_pat (A.PatVar (bv_as_unique_ident bv, None)), term
        in
        attrs_opt,
        (if is_pat_app then
          let args = binders |> map_opt (fun (bv, q) ->
            BU.map_opt (resugar_arg_qual env q) (fun q -> mk_pat(A.PatVar (bv_as_unique_ident bv, q)))) in
          ((mk_pat (A.PatApp (pat, args)), resugar_term' env term), (universe_to_string univs))
        else
          ((pat, resugar_term' env term), (universe_to_string univs)))
      in
      let r = List.map (resugar_one_binding) source_lbs in
      let bnds =
          let f (attrs, (pb, univs)) =
            if not (Options.print_universes ()) then attrs, pb
            (* Print bound universes as a comment *)
            else attrs, (fst pb, label univs (snd pb))
          in
          List.map f r
      in
      let body = resugar_term' env body in
      mk (A.Let((if is_rec then A.Rec else A.NoLetQualifier), bnds, body))

    | Tm_uvar (u, _) ->
      let s = "?u" ^ (UF.uvar_id u.ctx_uvar_head |> string_of_int) in
      (* TODO : should we put a pretty_non_parseable option for these cases ? *)
      label s (mk A.Wild)

    | Tm_quoted (tm, qi) ->
      let qi = match qi.qkind with
               | Quote_static -> Static
               | Quote_dynamic -> Dynamic
      in
      mk (A.Quote (resugar_term' env tm, qi))

    | Tm_meta(e, m) ->
       let resugar_meta_desugared = function
          | Sequence ->
              let term = resugar_term' env e in
              let rec resugar_seq t = match t.tm with
                | A.Let(_, [_, (p, t1)], t2) ->
                   mk (A.Seq(t1, t2))
                | A.Ascribed(t1, t2, t3) ->
                   (* this case happens when the let is wrapped in Meta_Monadic which is resugared to Ascribe*)
                   mk (A.Ascribed(resugar_seq t1, t2, t3))
                | _ ->
                   (* this case happens in typechecker.normalize when Tm_let is_pure_effect, then
                      only the body of Tm_let is used. *)
                   (* TODO: How should it be resugared *)
                   t
              in
              resugar_seq term
          | Primop (* doesn't seem to be generated by desugar *)
          | Masked_effect (* doesn't seem to be generated by desugar *)
          | Meta_smt_pat -> (* nothing special, just resugar the term *)
              resugar_term' env e
      in
      begin match m with
      | Meta_pattern (_, pats) ->
        // This case is possible in TypeChecker when creating "haseq" for Sig_inductive_typ whose Sig_datacon has no binders.
        let pats = List.flatten pats |> List.map (fun (x, _) -> resugar_term' env x) in
        // Is it correct to resugar it to Attributes.
        mk (A.Attributes pats)

      | Meta_labeled _ ->
          (* Ignore the label, we don't want to print it *)
          resugar_term' env e
      | Meta_desugared i ->
          resugar_meta_desugared i
      | Meta_named t ->
          mk (A.Name t)
      | Meta_monadic (name, t)
      | Meta_monadic_lift (name, _, t) ->
        resugar_term' env e
      end

    | Tm_unknown -> mk A.Wild

and resugar_comp' (env: DsEnv.env) (c:S.comp) : A.term =
  let mk (a:A.term') : A.term =
        //augment `a` with its source position
        //and an Unknown level (the level is unimportant ... we should maybe remove it altogether)
        A.mk_term a c.pos A.Un
  in
  match (c.n) with
  | Total (typ, u) ->
    let t = resugar_term' env typ in
    begin match u with
    | None ->
      mk (A.Construct(C.effect_Tot_lid, [(t, A.Nothing)]))
    | Some u ->
      // add the universe as the first argument
      if (Options.print_universes()) then
        let u = resugar_universe u c.pos in
        mk (A.Construct(C.effect_Tot_lid, [(u, A.UnivApp);(t, A.Nothing)]))
      else
        mk (A.Construct(C.effect_Tot_lid, [(t, A.Nothing)]))
    end

  | GTotal (typ, u) ->
    let t = resugar_term' env typ in
    begin match u with
    | None ->
      mk (A.Construct(C.effect_GTot_lid, [(t, A.Nothing)]))
    | Some u ->
      // add the universe as the first argument
      if (Options.print_universes()) then
        let u = resugar_universe u c.pos in
        mk (A.Construct(C.effect_GTot_lid, [(u, A.UnivApp);(t, A.Nothing)]))
      else
        mk (A.Construct(C.effect_GTot_lid, [(t, A.Nothing)]))
    end

  | Comp c ->
    let result = (resugar_term' env c.result_typ, A.Nothing) in
    if (Options.print_effect_args()) || lid_equals c.effect_name C.effect_Lemma_lid then
      let universe = List.map (fun u -> resugar_universe u) c.comp_univs in
      let args =
       if (lid_equals c.effect_name C.effect_Lemma_lid) then (
        match c.effect_args with
        | pre::post::pats::[] ->
            // Common case, post is thunked.
            let post = (U.unthunk_lemma_post (fst post), snd post) in
             (if U.is_fvar C.true_lid (fst pre) then [] else [pre])
            @[post]
            @(if U.is_fvar C.nil_lid (fst pats) then [] else [pats])
        | _ -> c.effect_args
       ) else
        c.effect_args
      in
      let args = List.map(fun (e,_) -> (resugar_term' env e, A.Nothing)) args in
      let rec aux l = function
       | [] -> l
       | hd::tl ->
          match hd with
          | DECREASES e ->
            let e = (resugar_term' env e, A.Nothing) in
            aux (e::l) tl
          | _ -> aux l tl
      in
      let decrease = aux [] c.flags in
      mk (A.Construct(c.effect_name, result::decrease@args))
    else
      mk (A.Construct(c.effect_name, [result]))

and resugar_binder' env (b:S.binder) r : option<A.binder> =
  let (x, aq) = b in
  BU.map_opt (resugar_arg_qual env aq) begin fun imp ->
    let e = resugar_term' env x.sort in
    match (e.tm) with
    | A.Wild ->
      A.mk_binder (A.Variable(bv_as_unique_ident x)) r A.Type_level imp
    | _ ->
      if S.is_null_bv x then
        A.mk_binder (A.NoName e) r A.Type_level imp
      else
        A.mk_binder (A.Annotated (bv_as_unique_ident x, e)) r A.Type_level imp
  end

and resugar_bv_as_pat' env (v: S.bv) aqual (body_bv: BU.set<bv>) typ_opt =
  let mk a = A.mk_pattern a (S.range_of_bv v) in
  let used = BU.set_mem v body_bv in
  let pat =
    mk (if used
        then A.PatVar (bv_as_unique_ident v, aqual)
        else A.PatWild aqual) in
  match typ_opt with
  | None | Some { n = Tm_unknown } -> pat
  | Some typ -> if Options.print_bound_var_types ()
               then mk (A.PatAscribed (pat, (resugar_term' env typ, None)))
               else pat

and resugar_bv_as_pat env (x:S.bv) qual body_bv: option<A.pattern> =
  BU.map_opt (resugar_arg_qual env qual)
    (fun aqual -> resugar_bv_as_pat' env x aqual body_bv (Some <| SS.compress x.sort))

and resugar_pat' env (p:S.pat) (branch_bv: set<bv>) : A.pattern =
  (* We lose information when desugar PatAscribed to able to resugar it back *)
  let mk a = A.mk_pattern a p.p in
  let to_arg_qual bopt = // FIXME do (Some false) and None mean the same thing?
    BU.bind_opt bopt (fun b -> if b then Some A.Implicit else None) in
  let may_drop_implicits args =
    not (Options.print_implicits ()) &&
    not (List.existsML (fun (pattern, is_implicit) ->
             let might_be_used =
               match pattern.v with
               | Pat_var bv
               | Pat_dot_term (bv, _) -> Util.set_mem bv branch_bv
               | Pat_wild _ -> false
               | _ -> true in
             is_implicit && might_be_used) args) in
  let resugar_plain_pat_cons' fv args =
    mk (A.PatApp (mk (A.PatName fv.fv_name.v), args)) in
  let rec resugar_plain_pat_cons fv args =
    let args =
      if may_drop_implicits args
      then filter_pattern_imp args
      else args in
    let args = List.map (fun (p, b) -> aux p (Some b)) args in
    resugar_plain_pat_cons' fv args
  and aux (p:S.pat) (imp_opt:option<bool>)=
    match p.v with
    | Pat_constant c -> mk (A.PatConst c)

    | Pat_cons (fv, []) ->
      mk (A.PatName fv.fv_name.v)

    | Pat_cons(fv, args) when (lid_equals fv.fv_name.v C.nil_lid
                               && may_drop_implicits args) ->
      if not (List.isEmpty (filter_pattern_imp args)) then
        E.log_issue p.p (E.Warning_NilGivenExplicitArgs, "Prims.Nil given explicit arguments");
      mk (A.PatList [])

    | Pat_cons(fv, args) when (lid_equals fv.fv_name.v C.cons_lid
                               && may_drop_implicits args) ->
      (match filter_pattern_imp args with
       | [(hd, false); (tl, false)] ->
         let hd' = aux hd (Some false) in
         (match aux tl (Some false) with
          | { pat = A.PatList tl'; prange = p } -> A.mk_pattern (A.PatList (hd' :: tl')) p
          | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
       | args' ->
         E.log_issue p.p (E.Warning_ConsAppliedExplicitArgs,
           (Util.format1 "Prims.Cons applied to %s explicit arguments"
             (string_of_int <| List.length args')));
         resugar_plain_pat_cons fv args)

    | Pat_cons(fv, args) when (is_tuple_constructor_lid fv.fv_name.v
                               && may_drop_implicits args) ->
      let args =
        args |>
        List.filter_map (fun (p, is_implicit) ->
            if is_implicit then None else Some (aux p (Some false))) in
      let is_dependent_tuple = C.is_dtuple_data_lid' fv.fv_name.v in
      mk (A.PatTuple (args, is_dependent_tuple))

    | Pat_cons({fv_qual=Some (Record_ctor(name, fields))}, args) ->
      // reverse the fields and args list to match them since the args added by the type checker
      // are inserted in the front of the args list.
      let fields = fields |> List.map (fun f -> FStar.Ident.lid_of_ids [f]) |> List.rev in
      let args = args |> List.map (fun (p, b) -> aux p (Some b)) |> List.rev in
      // make sure the fields and args are of the same length.
      let rec map2 l1 l2  = match (l1, l2) with
        | ([], []) -> []
        | ([], hd::tl) -> [] (* new args could be added by the type checker *)
        | (hd::tl, []) -> (hd, mk (A.PatWild None)) :: map2 tl [] (* no new fields should be added*)
        | (hd1::tl1, hd2::tl2) -> (hd1, hd2) :: map2 tl1 tl2
      in
      // reverse back the args list
      let args = map2 fields args |> List.rev in
      mk (A.PatRecord(args))

    | Pat_cons (fv, args) ->
      resugar_plain_pat_cons fv args

    | Pat_var v ->
      // both A.PatTvar and A.PatVar are desugared to S.Pat_var. A PatTvar in the original file coresponds
      // to some type variable which is implicitly bound to the enclosing toplevel declaration.
      // When resugaring it will be just a normal (explicitly bound) variable.
      begin match string_to_op v.ppname.idText with
       | Some (op, _) -> mk (A.PatOp (Ident.mk_ident (op, v.ppname.idRange)))
       | None -> resugar_bv_as_pat' env v (to_arg_qual imp_opt) branch_bv None
      end

    | Pat_wild _ -> mk (A.PatWild (to_arg_qual imp_opt))

    | Pat_dot_term (bv, term) ->
      (* TODO : this should never be resugared unless in a comment *)
      resugar_bv_as_pat' env bv (Some A.Implicit) branch_bv (Some term)
  in
  aux p None
// FIXME inspect uses of resugar_arg_qual and resugar_imp
(* If resugar_arg_qual returns None, the corresponding binder should *not* be resugared *)
and resugar_arg_qual env (q:option<S.arg_qualifier>) : option<(option<A.arg_qualifier>)> =
  match q with
  | None -> Some None
  | Some (S.Implicit b) ->
    (* TODO : set an option to print these inaccessible patterns at least with a comment *)
    if b then None
    else Some (Some A.Implicit)
  | Some S.Equality -> Some (Some A.Equality)
  | Some (S.Meta t) ->
    Some (Some (A.Meta (resugar_term' env t)))

and resugar_imp env (q:option<S.arg_qualifier>) : A.imp =
  match q with
  | None -> A.Nothing
  | Some (S.Implicit false) -> A.Hash
  | Some S.Equality
  | Some (S.Implicit true) -> A.Nothing // We don't have syntax for inaccessible arguments
  | Some (S.Meta t) -> A.HashBrace (resugar_term' env t)

let resugar_qualifier : S.qualifier -> option<A.qualifier> = function
  | S.Assumption -> Some A.Assumption
  | S.New -> Some A.New
  | S.Private -> Some A.Private
  | S.Unfold_for_unification_and_vcgen -> Some A.Unfold_for_unification_and_vcgen
  (* TODO : Find the correct option to display this *)
  | Visible_default -> if true then None else Some A.Visible
  | S.Irreducible -> Some A.Irreducible
  | S.Abstract -> Some A.Abstract
  | S.Inline_for_extraction -> Some A.Inline_for_extraction
  | S.NoExtract -> Some A.NoExtract
  | S.Noeq -> Some A.Noeq
  | S.Unopteq -> Some A.Unopteq
  | S.TotalEffect -> Some A.TotalEffect
  (* TODO : Find the correct option to display this *)
  | S.Logic -> if true then None else Some A.Logic
  | S.Reifiable -> Some A.Reifiable
  | S.Reflectable _ -> Some A.Reflectable
  | S.Discriminator _ -> None
  | S.Projector _ -> None
  | S.RecordType _ -> None
  | S.RecordConstructor _ -> None
  | S.Action _ -> None
  | S.ExceptionConstructor -> None
  | S.HasMaskedEffect -> None
  | S.Effect -> Some A.Effect_qual
  | S.OnlyName -> None


let resugar_pragma = function
  | S.SetOptions s -> A.SetOptions s
  | S.ResetOptions s -> A.ResetOptions s
  | S.PushOptions s -> A.PushOptions s
  | S.PopOptions -> A.PopOptions
  | S.LightOff -> A.LightOff

let resugar_typ env datacon_ses se : sigelts * A.tycon =
  match se.sigel with
  | Sig_inductive_typ (tylid, uvs, bs, t, _, datacons) ->
      let current_datacons, other_datacons = datacon_ses |> List.partition (fun se -> match se.sigel with
        | Sig_datacon (_, _, _, inductive_lid, _, _) -> lid_equals inductive_lid tylid
        | _ -> failwith "unexpected" )
      in
      assert (List.length current_datacons = List.length datacons) ;
      let bs = if (Options.print_implicits()) then bs else filter_imp bs in
      let bs = bs |> map_opt (fun b -> resugar_binder' env b t.pos) in
      let tyc =
        if se.sigquals |> BU.for_some (function | RecordType _ -> true | _ -> false)
        then
          (* Resugar as a record *)
          let resugar_datacon_as_fields fields se = match se.sigel with
            | Sig_datacon (_, univs, term, _, num, _) ->
              (* Todo: resugar univs *)
              begin match (SS.compress term).n with
                | Tm_arrow(bs, _) ->
                  let mfields = bs |> List.map (fun (b, qual) -> (bv_as_unique_ident b, resugar_term' env b.sort, None)) in
                  mfields@fields
                | _ -> failwith "unexpected"
              end
            | _ -> failwith "unexpected"
          in
          let fields =  List.fold_left resugar_datacon_as_fields [] current_datacons in
          A.TyconRecord(tylid.ident, bs, None, fields)
        else
          (* Resugar as a variant *)
          let resugar_datacon constructors se = match se.sigel with
            | Sig_datacon (l, univs, term, _, num, _) ->
              (* Todo: resugar univs *)
              let c = (l.ident, Some (resugar_term' env term), None, false)  in
              c::constructors
            | _ -> failwith "unexpected"
          in
          let constructors =  List.fold_left resugar_datacon [] current_datacons in
          A.TyconVariant(tylid.ident, bs, None, constructors)
      in
      other_datacons, tyc
  | _ -> failwith "Impossible : only Sig_inductive_typ can be resugared as types"

let mk_decl r q d' =
  {
    d = d' ;
    drange = r ;
    (* TODO : documentation should be retrieved from the desugaring environment at some point *)
    doc = None ;
    quals = List.choose resugar_qualifier q ;
    (* TODO : are these stocked up somewhere ? *)
    attrs = [] ;
  }

let decl'_to_decl se d' =
  mk_decl se.sigrng se.sigquals d'

let resugar_tscheme'' env name (ts:S.tscheme) =
  let (univs, typ) = ts in
  let name = I.mk_ident (name, typ.pos) in
  mk_decl typ.pos [] (A.Tycon(false, false, [(A.TyconAbbrev(name, [], None, resugar_term' env typ), None)]))

let resugar_tscheme' env (ts:S.tscheme) =
  resugar_tscheme'' env "tscheme" ts

let resugar_eff_decl' env for_free r q ed =
  let resugar_action d for_free =
    let action_params = SS.open_binders d.action_params in
    let bs, action_defn = SS.open_term action_params d.action_defn in
    let bs, action_typ = SS.open_term action_params d.action_typ in
    let action_params = if (Options.print_implicits()) then action_params else filter_imp action_params in
    let action_params = action_params |> map_opt (fun b -> resugar_binder' env b r) |> List.rev in
    let action_defn = resugar_term' env action_defn in
    let action_typ = resugar_term' env action_typ in
    if for_free then
      let a = A.Construct ((I.lid_of_str "construct"), [(action_defn, A.Nothing);(action_typ, A.Nothing)]) in
      let t = A.mk_term a r A.Un in
      mk_decl r q (A.Tycon(false, false, [(A.TyconAbbrev(d.action_name.ident, action_params, None, t ), None)]))
    else
      mk_decl r q (A.Tycon(false, false, [(A.TyconAbbrev(d.action_name.ident, action_params, None, action_defn), None)]))
  in
  let eff_name = ed.mname.ident in
  let eff_binders, eff_typ = SS.open_term ed.binders ed.signature in
  let eff_binders = if (Options.print_implicits()) then eff_binders else filter_imp eff_binders in
  let eff_binders = eff_binders |> map_opt (fun b -> resugar_binder' env b r) |> List.rev in
  let eff_typ = resugar_term' env eff_typ in
  let ret_wp = resugar_tscheme'' env "ret_wp" ed.ret_wp in
  let bind_wp = resugar_tscheme'' env "bind_wp" ed.bind_wp in
  let if_then_else = resugar_tscheme'' env "if_then_else" ed.if_then_else in
  let ite_wp = resugar_tscheme'' env "ite_wp" ed.ite_wp in
  let stronger = resugar_tscheme'' env "stronger" ed.stronger in
  let close_wp = resugar_tscheme'' env "close_wp" ed.close_wp in
  let assert_p = resugar_tscheme'' env "assert_p" ed.assert_p in
  let assume_p = resugar_tscheme'' env "assume_p" ed.assume_p in
  let null_wp = resugar_tscheme'' env "null_wp" ed.null_wp in
  let trivial = resugar_tscheme'' env "trivial" ed.trivial in
  let repr = resugar_tscheme'' env "repr" ([], ed.repr) in
  let return_repr = resugar_tscheme'' env "return_repr" ed.return_repr in
  let bind_repr = resugar_tscheme'' env "bind_repr" ed.bind_repr in
  let mandatory_members_decls =
    if for_free then
      [repr; return_repr; bind_repr]
    else
      [repr; return_repr; bind_repr; ret_wp; bind_wp;
       if_then_else; ite_wp; stronger; close_wp; assert_p;
        assume_p; null_wp; trivial] in
  let actions = ed.actions |> List.map (fun a -> resugar_action a false) in
  let decls = mandatory_members_decls@actions in
  mk_decl r q (A.NewEffect(DefineEffect(eff_name, eff_binders, eff_typ, decls)))

let resugar_sigelt' env se : option<A.decl> =
  match se.sigel with
  | Sig_bundle (ses, _) ->
    let decl_typ_ses, datacon_ses = ses |> List.partition
      (fun se -> match se.sigel with
        | Sig_inductive_typ _ | Sig_declare_typ _ -> true
        | Sig_datacon _ -> false
        | _ -> failwith "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"
      )
    in
    let retrieve_datacons_and_resugar (datacon_ses, tycons) se =
      let datacon_ses, tyc = resugar_typ env datacon_ses se in
      datacon_ses, tyc::tycons
    in
    let leftover_datacons, tycons = List.fold_left retrieve_datacons_and_resugar (datacon_ses, []) decl_typ_ses in
    begin match leftover_datacons with
      | [] -> //true
        (* TODO : documentation should be retrieved from the desugaring environment at some point *)
        Some (decl'_to_decl se (Tycon (false, false, List.map (fun tyc -> tyc, None) tycons)))
      | [se] ->
        //assert (se.sigquals |> BU.for_some (function | ExceptionConstructor -> true | _ -> false));
        (* Exception constructor declaration case *)
        begin match se.sigel with
        | Sig_datacon(l, _, _, _, _, _) ->
          Some (decl'_to_decl se (A.Exception (l.ident, None)))
        | _ -> failwith "wrong format for resguar to Exception"
        end
      | _ ->
        failwith "Should not happen hopefully"
    end

  | Sig_let (lbs, _) ->
    if (se.sigquals |> BU.for_some (function S.Projector(_,_) | S.Discriminator _ -> true | _ -> false)) then
      None
    else
      let mk e = S.mk e None se.sigrng in
      let dummy = mk Tm_unknown in
      let desugared_let = mk (Tm_let(lbs, dummy)) in
      let t = resugar_term' env desugared_let in
      begin match t.tm with
        | A.Let(isrec, lets, _) ->
          Some (decl'_to_decl se (TopLevelLet (isrec, List.map snd lets)))
        | _ -> failwith "Should not happen hopefully"
      end

  | Sig_assume (lid, _, fml) ->
    Some (decl'_to_decl se (Assume (lid.ident, resugar_term' env fml)))

  | Sig_new_effect ed ->
    Some (resugar_eff_decl' env false se.sigrng se.sigquals ed)

  | Sig_new_effect_for_free ed ->
    Some (resugar_eff_decl' env true se.sigrng se.sigquals ed)

  | Sig_sub_effect e ->
    let src = e.source in
    let dst = e.target in
    let lift_wp = match e.lift_wp with
      | Some (_, t) ->
          Some (resugar_term' env t)
      | _ -> None
    in
    let lift = match e.lift with
      | Some (_, t) ->
          Some (resugar_term' env t)
      | _ -> None
    in
    let op = match (lift_wp, lift) with
      | Some t, None -> A.NonReifiableLift t
      | Some wp, Some t -> A.ReifiableLift (wp, t)
      | None, Some t -> A.LiftForFree t
      | _ -> failwith "Should not happen hopefully"
    in
    Some (decl'_to_decl se (A.SubEffect({msource=src; mdest=dst; lift_op=op})))

  | Sig_effect_abbrev (lid, vs, bs, c, flags) ->
    let bs, c = SS.open_comp bs c in
    let bs = if (Options.print_implicits()) then bs else filter_imp bs in
    let bs = bs |> map_opt (fun b -> resugar_binder' env b se.sigrng) in
    Some (decl'_to_decl se (A.Tycon(false, false, [A.TyconAbbrev(lid.ident, bs, None, resugar_comp' env c), None])))

  | Sig_pragma p ->
    Some (decl'_to_decl se (A.Pragma (resugar_pragma p)))

  | Sig_declare_typ (lid, uvs, t) ->
    if (se.sigquals |> BU.for_some (function S.Projector(_,_) | S.Discriminator _ -> true | _ -> false)) then
      None
    else
      let t' =
        if not (Options.print_universes ()) || isEmpty uvs then resugar_term' env t
        else
          let uvs, t = SS.open_univ_vars uvs t in
          let universes = universe_to_string uvs in
          label universes (resugar_term' env t)
      in
      Some (decl'_to_decl se (A.Val (lid.ident,t')))

  | Sig_splice (ids, t) ->
    Some (decl'_to_decl se (A.Splice (List.map (fun l -> l.ident) ids, resugar_term' env t)))

  (* Already desugared in one of the above case or non-relevant *)
  | Sig_inductive_typ _
  | Sig_datacon _
  | Sig_main _ -> None

(* Old interface: no envs *)

let empty_env = DsEnv.empty_env FStar.Parser.Dep.empty_deps //dep graph not needed for resugaring

let noenv (f: DsEnv.env -> 'a) : 'a =
  f empty_env

let resugar_term (t : S.term) : A.term =
  noenv resugar_term' t

let resugar_sigelt se : option<A.decl> =
  noenv resugar_sigelt' se

let resugar_comp (c:S.comp) : A.term =
  noenv resugar_comp' c

let resugar_pat (p:S.pat) (branch_bv: set<bv>) : A.pattern =
  noenv resugar_pat' p branch_bv

let resugar_binder (b:S.binder) r : option<A.binder> =
  noenv resugar_binder' b r

let resugar_tscheme (ts:S.tscheme) =
  noenv resugar_tscheme' ts

let resugar_eff_decl for_free r q ed =
  noenv resugar_eff_decl' for_free r q ed
