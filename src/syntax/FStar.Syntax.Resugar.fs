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
module C = FStar.Syntax.Const
module U = FStar.Syntax.Util
module BU = FStar.Util
module D = FStar.Parser.ToDocument

let bv_as_unique_ident (x:S.bv) : I.ident =
  let unique_name =  
    if starts_with reserved_prefix x.ppname.idText then
      x.ppname.idText ^ (string_of_int x.index)
    else
      x.ppname.idText
  in
  I.mk_ident (unique_name, x.ppname.idRange)

let filter_imp a = a |> List.filter (function (_, Some (S.Implicit _)) -> false | _ -> true)

(* If resugar_arg_qual returns None, the corresponding binder should *not* be resugared *)
let resugar_arg_qual (q:option<S.arg_qualifier>) : option<(option<A.arg_qualifier>)> =
  match q with
  | None -> Some None
  | Some (S.Implicit b) ->
    (* TODO : set an option to print these inaccessible patterns *)
    if b then None
    else Some (Some A.Implicit)
  | Some S.Equality -> Some (Some A.Equality)

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
    | "Amp" -> Some ("&", 0)
    | "At" -> Some ("@", 0)
    | "Plus" -> Some ("+", 0)
    | "Minus" -> Some ("-", 0)
    | "Subtraction" -> Some ("-", 2)
    | "Slash" -> Some ("/", 0)
    | "Less" -> Some ("<", 0)
    | "Equals" -> Some ("=", 0)
    | "Greater" -> Some (">", 0)
    | "Underscore" -> Some ("_", 0)
    | "Bar" -> Some ("|", 0)
    | "Bang" -> Some ("!", 0)
    | "Hat" -> Some ("^", 0)
    | "Percent" -> Some ("%", 0)
    | "Star" -> Some ("*", 0)
    | "Question" -> Some ("?", 0)
    | "Colon" -> Some (":", 0)
    | _ -> None
  in
  match s with
  | "op_String_Assignment" -> Some (".[]<-", 0)
  | "op_Array_Assignment" -> Some (".()<-", 0)
  | "op_String_Access" -> Some (".[]", 0)
  | "op_Array_Access" -> Some (".()", 0)
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
        Some (op, 0)
    else
      None

let rec resugar_term_as_op(t:S.term) : option<(string*int)> =
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
    (C.eq3_lid     , "===");
    (C.forall_lid  , "forall");
    (C.exists_lid  , "exists");
    (C.salloc_lid  , "alloc")
  ] in
  let fallback fv =
    match infix_prim_ops |> BU.find_opt (fun d -> fv_eq_lid fv (fst d)) with
    | Some op ->
      Some (snd op, 0)
    | _ ->
      let length = String.length(fv.fv_name.v.nsstr) in
      let str = if length=0 then fv.fv_name.v.str
          else BU.substring_from fv.fv_name.v.str (length+1) in
      if BU.starts_with str "dtuple" then Some ("dtuple", 0)
      else if BU.starts_with str "tuple" then Some ("tuple", 0)
      else if BU.starts_with str "try_with" then Some ("try_with", 0)
      else if fv_eq_lid fv C.sread_lid then Some (fv.fv_name.v.str, 0)
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
    | Tm_uinst(e, us) -> resugar_term_as_op e
    | _ -> None

let is_true_pat (p:S.pat) : bool = match p.v with
    | Pat_constant (Const_bool true) -> true
    | _ -> false

let is_wild_pat (p:S.pat) : bool = match p.v with
    | Pat_wild _ -> true
    | _ -> false

let is_disj_pat (p:S.pat) : bool = match p.v with
  | Pat_disj _ -> true
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
    match (SS.compress t).n with //always call compress before case-analyzing a S.term
    | Tm_delayed _ ->
      failwith "Tm_delayed is impossible after compress"

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
       else if (lid_equals a C.assert_lid
            || lid_equals a C.assume_lid
            || Char.uppercase (String.get s 0) <> String.get s 0) then
              mk (var a.str t.pos)
          else
              mk (name a.str t.pos)
    | Tm_uinst(e, universes) ->
      if (Options.print_universes()) then
        let e = resugar_term e in
        List.fold_left(fun acc x -> mk (A.App(acc, resugar_universe x t.pos, A.UnivApp))) e universes
      else 
        resugar_term e

    | Tm_constant c ->
      if is_teff t
      then mk (name "Effect" t.pos)
      else mk (A.Const c)

    | Tm_type u ->
        begin match u with
        | U_zero ->  mk (name "Type0" t.pos)
        | U_unknown -> mk (name "Type" t.pos)
        | _ ->
          if (Options.print_universes()) then 
            let u = resugar_universe u t.pos in
            let l = lid_of_path ["Type"] t.pos in
            mk (A.Construct (l, [(u, UnivApp)]))
          else 
            mk (name "Type" t.pos)
        end

    | Tm_abs(xs, body, _) -> //fun x1 .. xn -> body
      //before inspecting any syntactic form that has binding structure
      //you must call SS.open_* to replace de Bruijn indexes with names
      let xs, body = SS.open_term xs body in
      let xs = if (Options.print_implicits()) then xs else filter_imp xs in
      let patterns = xs |> List.choose (fun (x, qual) ->
        //x.sort contains a type annotation for the bound variable
        //the pattern `p` below only contains the variable, not the annotation
        //but, if the user wrote the annotation, then we should record that and print it back
        //additionally, if we're in verbose mode, e.g., if --print_bound_var_types is set
        //    then we should print the annotation too
        resugar_bv_as_pat x qual) 
      in
      let body = resugar_term body in
      mk (A.Abs(patterns, body))

    | Tm_arrow(xs, body) ->
      let xs, body = SS.open_comp xs body in
      let xs = if (Options.print_implicits()) then xs else filter_imp xs in
      let body = resugar_comp body in
      let xs = xs |> List.map (fun b -> resugar_binder b t.pos) |> List.rev in
      let rec aux body = function
        | [] -> body
        | hd::tl ->
          let body = mk (A.Product([hd], body)) in
          aux body tl in
      aux body xs

    | Tm_refine(x, phi) ->
      (* bv * term -> binder * term *)
      let x, phi = SS.open_term [S.mk_binder x] phi in
      let b = resugar_binder (List.hd x) t.pos in
      mk (A.Refine(b, resugar_term phi))

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
      let rec last_three = function
            | [] | [_] | [_;_] -> failwith "last three elements of a list with less than three elements "
            | [a1;a2;a3] -> [a1;a2;a3]
            | _::t -> last_three t
      in
      let resugar_as_app e args =
        let args = args |> List.map (fun (e, qual) ->
              resugar_term e) in
        let e = resugar_term e in
        List.fold_left(fun acc x -> mk (A.App(acc, x, A.Nothing))) e args
      in
      let args = if (Options.print_implicits()) then args else filter_imp args
      in
      begin match resugar_term_as_op e with
        | None->
          resugar_as_app e args

        | Some ("tuple", _) ->
          begin match args with
            | (fst, _)::(snd, _)::rest ->
              let e = mk(A.Op(Ident.id_of_text "*", [(resugar_term fst); (resugar_term snd)])) in
              List.fold_left(fun acc (x,_) -> mk (A.Op(Ident.id_of_text "*", [e; resugar_term x]))) e rest
            | _ -> resugar_as_app e args
          end

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
                let xs = xs |> List.map (fun b -> resugar_binder b t.pos) in
                let body = resugar_term body in
                mk (A.Sum(xs, body))

            | _ ->
              let args = args |> List.map (fun (e, qual) ->
                resugar_term e) in
              let e = resugar_term e in
              List.fold_left(fun acc x -> mk (A.App(acc, x, A.Nothing))) e args
          end

        | Some ("dtuple", _) ->
          resugar_as_app e args

        | Some (ref_read, _) when (ref_read = C.sread_lid.str) ->
          let (t, _) = List.hd args in
          begin match (SS.compress t).n with
            | Tm_fvar fv when (U.field_projector_contains_constructor fv.fv_name.v.str) ->
              let f = lid_of_path [fv.fv_name.v.str] t.pos in
              mk (A.Project(resugar_term t, f))
            | _ -> resugar_term t
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
          let body = resugar_term (decomp body) in
          let handler = resugar_term (decomp handler) in
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

        | Some (op, _) when op = "forall" || op = "exists" ->
          (* desugared from QForall(binders * patterns * body) to Tm_app(forall, Tm_abs(binders, Tm_meta(body, meta_pattern(list<args>)*)
          let rec uncurry xs pat (t:A.term) = match t.tm with
            | A.QExists(x, p , body)
            | A.QForall(x, p, body)
              -> uncurry (x@xs) (p@pat) body
            | _ -> xs, pat, t
          in
          let resugar body = match (SS.compress body).n with
            | Tm_abs(xs, body, _) ->
                let xs, body = SS.open_term xs body in
                let xs = if (Options.print_implicits()) then xs else filter_imp xs in
                let xs = xs |> List.map (fun b -> resugar_binder b t.pos) in
                let pats, body = match (SS.compress body).n with
                  | Tm_meta(e, m) ->
                    let body = resugar_term e in
                    let pats = match m with
                      | Meta_pattern pats -> List.map (fun es -> es |> List.map (fun (e, _) -> resugar_term e)) pats
                      | Meta_labeled (s, r, _) ->
                        // this case can occur in typechecker when a failure is wrapped in meta_labeled
                        [[mk (name s r)]]
                      | _ -> failwith "wrong pattern format for QForall/QExists"
                    in
                    pats, body
                  | _ -> [], resugar_term body
                in
                let xs, pats, body = uncurry xs pats body in
                let xs = xs |> List.rev in
                if op = "forall" then mk (A.QForall(xs, pats, body)) else mk (A.QExists(xs, pats, body))

            | _ ->
            (*forall added by typechecker.normalize doesn't not have Tm_abs as body*)
            (*TODO:  should we resugar them back as forall/exists or just as the term of the body *)
            if op = "forall" then mk (A.QForall([], [[]], resugar_term body))
            else mk (A.QExists([], [[]], resugar_term body))
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
          resugar_term e

        | Some (op, arity) ->
          let op = Ident.id_of_text op in
          let resugar args = args |> List.map (fun (e, qual) ->
              resugar_term e)
          in
          (* ignore the arguments added by typechecker *)
          (* TODO: we need a place to store the information in the args added by the typechecker *)
          //NS: this seems to produce the wrong output on things like
          begin match arity with 
          | 0 -> begin match D.handleable_args_length op with
                 | 1 when List.length args > 0 -> mk (A.Op(op, resugar (last args)))
                 | 2 when List.length args > 1 -> mk (A.Op(op, resugar (last_two args)))
                 | 3 when List.length args > 2 -> mk (A.Op(op, resugar (last_three args)))
                 | _ -> resugar_as_app e args
                 end
          | 2 when List.length args > 1 -> mk (A.Op(op, resugar (last_two args)))
          | _ -> resugar_as_app e args
          end 
    end

    | Tm_match(e, [(pat, _, t)]) when not (is_disj_pat pat) -> 
    (* for match expressions that have exactly 1 branch, instead of printing them as `match e with | P -> e1` 
       it would be better to print it as `let P = e in e1`. *)
    (* only do it when pat is not Pat_disj since ToDocument only expects disjunctivePattern in Match and TryWith *)
    let bnds = [(resugar_pat pat, resugar_term e)] in
    let body = resugar_term t in
    mk (A.Let(A.NoLetQualifier, bnds, body))

    | Tm_match(e, [(pat1, _, t1); (pat2, _, t2)]) when is_true_pat pat1 && is_wild_pat pat2 ->
      mk (A.If(resugar_term e, resugar_term t1, resugar_term t2))

    | Tm_match(e, branches) ->
      let resugar_branch (pat, wopt,b) =
        let pat = resugar_pat pat in
        let wopt = match wopt with
          | None -> None
          | Some e -> Some (resugar_term e) in
        let b = resugar_term b in
        (pat, wopt, b) in
        mk (A.Match(resugar_term e, List.map resugar_branch branches))

    | Tm_ascribed(e, (asc, tac_opt), _) ->
      let term = match asc with
          | Inl n -> (* term *)
            resugar_term n
          | Inr n -> (* comp *)
            resugar_comp n in
      let tac_opt = Option.map resugar_term tac_opt in
      mk (A.Ascribed(resugar_term e, term, tac_opt))

    | Tm_let((is_rec, bnds), body) ->
      let mk_pat a = A.mk_pattern a t.pos in
      let bnds, body = SS.open_let_rec bnds body in
      let resugar_one_binding bnd =
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
        let universe_to_string univs = 
          if (Options.print_universes()) then
            List.map (fun x -> x.idText) univs |> String.concat  ", "
          else ""
        in   
        let pat, term = match bnd.lbname with
          | Inr fv -> mk_pat (A.PatName fv.fv_name.v), term
          | Inl bv ->
            mk_pat (A.PatVar (bv_as_unique_ident bv, None)), term
        in
        if is_pat_app then
          let args = binders |> List.map (fun (bv, _) -> mk_pat(A.PatVar (bv_as_unique_ident bv, None))) in
          ((mk_pat (A.PatApp (pat, args)), resugar_term term), (universe_to_string univs))
        else
          ((pat, resugar_term term), (universe_to_string univs))
      in
      let r = List.map (resugar_one_binding) bnds in
      let bnds = List.map fst r in
      let comments = List.map snd r in
      let body = resugar_term body in
      mk (A.Let((if is_rec then A.Rec else A.NoLetQualifier), bnds, body))

    | Tm_uvar (u, _) ->
      let s = "uu___unification_ " ^ (FStar.Unionfind.uvar_id u |> string_of_int) in
      mk (var s t.pos)

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
                    if (U.is_tuple_data_lid' head) then
                      // ToDocument doesn't expect uvar that is added by the
                      // typechecker in tuple constructor
                      // TODO: where should be store the universe information?
                      mk (A.Construct(head, args))
                    else
                      if (Options.print_universes()) then
                        mk (A.Construct(head, args@universes))
                      else 
                        mk (A.Construct(head, args))
                | Tm_meta(_, m) ->
                  // the Tm_app for Data_app could be wrapped inside Tm_meta(_, Meta_monadic) after TypeChecker
                  // applies monadic_application
                  begin match m with
                    | Meta_monadic (_, _) -> resugar_term e
                    | _ -> failwith "wrong Tm_meta format in Meta_desugared"
                  end
                | _ ->
                  failwith "wrong Data_app format"
              end
          | Sequence ->
              let term = resugar_term e in
              let rec resugar_seq t = match t.tm with
                | A.Let(_, [p, t1], t2) ->
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
        // This case is possible in TypeChecker when creating "haseq" for Sig_inductive_typ whose Sig_datacon has no binders.
        let pats = List.flatten pats |> List.map (fun (x, _) -> resugar_term x) in
        // Is it correct to resugar it to Attributes.
        mk (A.Attributes pats)

      | Meta_labeled (l, _, p) ->
          mk (A.Labeled(resugar_term e, l, p))
      | Meta_desugared i ->
          resugar_meta_desugared i
      | Meta_named t ->
          mk (A.Name t)
      | Meta_monadic (name, t)
      | Meta_monadic_lift (name, _, t) ->
        mk (A.Ascribed(resugar_term e,
                       mk (A.Construct(name,[resugar_term t, A.Nothing])),
                       None))
      end

    | Tm_unknown -> mk A.Wild

and resugar_comp (c:S.comp) : A.term =
  let mk (a:A.term') : A.term =
        //augment `a` with its source position
        //and an Unknown level (the level is unimportant ... we should maybe remove it altogether)
        A.mk_term a c.pos A.Un
  in
  match (c.n) with
  | Total (typ, u) ->
    let t = resugar_term typ in
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
    let t = resugar_term typ in
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
    let result = (resugar_term c.result_typ, A.Nothing) in
    if (Options.print_effect_args()) then
      let universe = List.map (fun u -> resugar_universe u) c.comp_univs in
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
      mk (A.Construct(c.effect_name, result::decrease@args))
    else
      mk (A.Construct(c.effect_name, [result]))

and resugar_binder (b:S.binder) r: A.binder =
  let (x, imp) = b in
  let e = resugar_term x.sort in
  match (e.tm) with
    | A.Wild ->
        A.mk_binder (A.Variable(bv_as_unique_ident x)) r A.Type_level None
    | _ ->
        if (S.is_null_bv x) then
          A.mk_binder (A.NoName(e)) r A.Type_level None
        else
          A.mk_binder (A.Annotated(bv_as_unique_ident x, e)) r A.Type_level None

and resugar_bv_as_pat (x:S.bv) qual: option<A.pattern> =
  let mk a = A.mk_pattern a (S.range_of_bv x) in
  match (SS.compress x.sort).n with
  //| Tm_type U_unknown
  | Tm_unknown ->
    let i = String.compare x.ppname.idText I.reserved_prefix in
    if i = 0 then
      Some (mk (A.PatWild))
    else
      BU.bind_opt (resugar_arg_qual qual) (fun aq -> Some (mk (A.PatVar(bv_as_unique_ident x, aq))))
  | _ ->
    BU.bind_opt (resugar_arg_qual qual)
      begin fun aq ->
        let pat = mk (A.PatVar(bv_as_unique_ident x, aq)) in
        if Options.print_bound_var_types() then
          Some (mk (A.PatAscribed(pat, resugar_term x.sort)))
        else
          Some pat
      end

and resugar_pat (p:S.pat) : A.pattern =
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

    | Pat_cons(fv, args) when lid_equals fv.fv_name.v C.cons_lid ->
      let args = List.map(fun (p, b) -> aux p) args in
      mk (A.PatList(args))

    | Pat_cons(fv, args) when U.is_tuple_data_lid' fv.fv_name.v || U.is_dtuple_data_lid' fv.fv_name.v ->
      let args = List.map(fun (p, b) -> aux p) args in
      if (U.is_dtuple_data_lid' fv.fv_name.v) then
        mk (A.PatTuple(args, true))
      else
        mk (A.PatTuple(args, false))

    | Pat_cons({fv_qual=Some (Record_ctor(name, fields))}, args) ->
      // reverse the fields and args list to match them since the args added by the type checker
      // are inserted in the front of the args list.
      let fields = fields |> List.map (fun f -> FStar.Ident.lid_of_ids [f]) |> List.rev in
      let args = args |> List.map (fun (p, b) -> aux p) |> List.rev in
      // make sure the fields and args are of the same length.
      let rec map2 l1 l2  = match (l1, l2) with
        | ([], []) -> []
        | ([], hd::tl) -> [] (* new args could be added by the type checker *)
        | (hd::tl, []) -> (hd, mk (A.PatWild)) :: map2 tl [] (* no new fields should be added*)
        | (hd1::tl1, hd2::tl2) -> (hd1, hd2) :: map2 tl1 tl2
      in
      // reverse back the args list
      let args = map2 fields args |> List.rev in
      mk (A.PatRecord(args))


    | Pat_cons (fv, args) ->
      let args = List.map (fun (p, b) -> aux p) args in
      mk (A.PatApp(mk (A.PatName fv.fv_name.v), args))

    | Pat_var v ->
      // both A.PatTvar and A.PatVar are desugared to S.Pat_var. A PatTvar in the original file coresponds
      // to some type variable which is implicitly bound to the enclosing toplevel declaration.
      // When resugaring it will be just a normal (explicitly bound) variable.
      begin match string_to_op v.ppname.idText with
       | Some (op, _) -> mk (A.PatOp (Ident.mk_ident (op, v.ppname.idRange)))
       | None -> mk (A.PatVar (bv_as_unique_ident v, None))
      end

    | Pat_wild _ -> mk (A.PatWild)

    | Pat_dot_term (bv, term) ->
      // no sure if this is correct resugar since the term is not generated from desugar
      let pat = mk (A.PatVar(bv_as_unique_ident bv, None)) in
      if Options.print_bound_var_types() then
        mk (A.PatAscribed(pat, resugar_term term))
      else
        pat
  in
    aux p

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
  | S.LightOff -> A.LightOff

let resugar_typ datacon_ses se : sigelts * A.tycon =
  match se.sigel with
  | Sig_inductive_typ (tylid, uvs, bs, t, _, datacons) ->
      let current_datacons, other_datacons = datacon_ses |> List.partition (fun se -> match se.sigel with
        | Sig_datacon (_, _, _, inductive_lid, _, _) -> lid_equals inductive_lid tylid
        | _ -> failwith "unexpected" )
      in
      assert (List.length current_datacons = List.length datacons) ;
      let bs = if (Options.print_implicits()) then bs else filter_imp bs in
      let bs = bs |> List.map (fun b -> resugar_binder b t.pos) in
      let tyc =
        if se.sigquals |> BU.for_some (function | RecordType _ -> true | _ -> false)
        then
          (* Resugar as a record *)
          let resugar_datacon_as_fields fields se = match se.sigel with 
            | Sig_datacon (_, univs, term, _, num, _) ->
              (* Todo: resugar univs *)
              begin match (SS.compress term).n with
                | Tm_arrow(bs, _) -> 
                  let mfields = bs |> List.map (fun (b, qual) -> (U.unmangle_field_name (bv_as_unique_ident b), resugar_term b.sort, None)) in
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
              let c = (l.ident, Some (resugar_term term), None, false)  in
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

let resugar_tscheme' name (ts:S.tscheme) = 
  let (univs, typ) = ts in
  let name = I.mk_ident (name, typ.pos) in
  mk_decl typ.pos [] (A.Tycon(false, [(A.TyconAbbrev(name, [], None, resugar_term typ), None)]))

let resugar_tscheme (ts:S.tscheme) = 
  resugar_tscheme' "tsheme" ts

let resugar_eff_decl for_free r q ed =
  let resugar_action d for_free = 
    let action_params = SS.open_binders d.action_params in
    let bs, action_defn = SS.open_term action_params d.action_defn in
    let bs, action_typ = SS.open_term action_params d.action_typ in
    let action_params = if (Options.print_implicits()) then action_params else filter_imp action_params in
    let action_params = action_params |> List.map (fun b -> resugar_binder b r) |> List.rev in
    let action_defn = resugar_term action_defn in
    let action_typ = resugar_term action_typ in
    if for_free then
      let a = A.Construct ((I.lid_of_str "construct"), [(action_defn, A.Nothing);(action_typ, A.Nothing)]) in
      let t = A.mk_term a r A.Un in
      mk_decl r q (A.Tycon(false, [(A.TyconAbbrev(d.action_name.ident, action_params, None, t ), None)]))
    else 
      mk_decl r q (A.Tycon(false, [(A.TyconAbbrev(d.action_name.ident, action_params, None, action_defn), None)]))
  in
  let eff_name = ed.mname.ident in
  let eff_binders, eff_typ = SS.open_term ed.binders ed.signature in
  let eff_binders = if (Options.print_implicits()) then eff_binders else filter_imp eff_binders in
  let eff_binders = eff_binders |> List.map (fun b -> resugar_binder b r) |> List.rev in
  let eff_typ = resugar_term eff_typ in
  let ret_wp = resugar_tscheme' "ret_wp" ed.ret_wp in
  let bind_wp = resugar_tscheme' "bind_wp" ed.ret_wp in
  let if_then_else = resugar_tscheme' "if_then_else" ed.if_then_else in
  let ite_wp = resugar_tscheme' "ite_wp" ed.ite_wp in
  let stronger = resugar_tscheme' "stronger" ed.stronger in
  let close_wp = resugar_tscheme' "close_wp" ed.close_wp in
  let assert_p = resugar_tscheme' "assert_p" ed.assert_p in
  let assume_p = resugar_tscheme' "assume_p" ed.assume_p in
  let null_wp = resugar_tscheme' "null_wp" ed.null_wp in
  let trivial = resugar_tscheme' "trivial" ed.trivial in
  let repr = resugar_tscheme' "repr" ([], ed.repr) in
  let return_repr = resugar_tscheme' "return_repr" ed.return_repr in
  let bind_repr = resugar_tscheme' "bind_repr" ed.bind_repr in
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

let resugar_sigelt se : option<A.decl> =
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
      let datacon_ses, tyc = resugar_typ datacon_ses se in
      datacon_ses, tyc::tycons
    in
    let leftover_datacons, tycons = List.fold_left retrieve_datacons_and_resugar (datacon_ses, []) decl_typ_ses in
    begin match leftover_datacons with
      | [] -> //true
        (* TODO : documentation should be retrieved from the desugaring environment at some point *)
        Some (decl'_to_decl se (Tycon (false, List.map (fun tyc -> tyc, None) tycons)))
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

  | Sig_let (lbs, _, attrs) ->
    if (se.sigquals |> BU.for_some (function S.Projector(_,_) | S.Discriminator _ -> true | _ -> false)) then
      None
    else
      let mk e = S.mk e None se.sigrng in
      let dummy = mk Tm_unknown in
      let desugared_let = mk (Tm_let(lbs, dummy)) in
      let t = resugar_term desugared_let in
      begin match t.tm with
        | A.Let(isrec, lets, _) ->
          Some (decl'_to_decl se (TopLevelLet (isrec, lets)))
        | _ -> failwith "Should not happen hopefully"
      end

  | Sig_assume (lid, fml) ->
    Some (decl'_to_decl se (Assume (lid.ident, resugar_term fml)))

  | Sig_new_effect ed ->
    Some (resugar_eff_decl false se.sigrng se.sigquals ed)

  | Sig_new_effect_for_free ed ->
    Some (resugar_eff_decl true se.sigrng se.sigquals ed)

  | Sig_sub_effect e ->
    let src = e.source in
    let dst = e.target in 
    let lift_wp = match e.lift_wp with 
      | Some (_, t) ->
          Some (resugar_term t)
      | _ -> None
    in
    let lift = match e.lift with
      | Some (_, t) ->
          Some (resugar_term t)
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
    let bs = bs |> List.map (fun b -> resugar_binder b se.sigrng) in
    Some (decl'_to_decl se (A.Tycon(false, [A.TyconAbbrev(lid.ident, bs, None, resugar_comp c), None])))

  | Sig_pragma p ->
    Some (decl'_to_decl se (A.Pragma (resugar_pragma p)))

  | Sig_declare_typ (lid, uvs, t) ->
    if (se.sigquals |> BU.for_some (function S.Projector(_,_) | S.Discriminator _ -> true | _ -> false)) then
      None
    else
      Some (decl'_to_decl se (A.Val(lid.ident, resugar_term t))) 

  (* Already desugared in one of the above case or non-relevant *)
  | Sig_inductive_typ _
  | Sig_datacon _
  | Sig_main _ -> None