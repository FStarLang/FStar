(*
   Copyright 2008-2015 Abhishek Anand, Nikhil Swamy and Microsoft Research

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
module FStar.Extraction.ML.Modul
open FStar.ST
open FStar.All
open FStar
open FStar.Util
open FStar.Syntax.Syntax
open FStar.Const
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Extraction.ML.UEnv
open FStar.Extraction.ML.Util
open FStar.Ident
open FStar.Syntax

module Term = FStar.Extraction.ML.Term
module Print = FStar.Syntax.Print
module MLS = FStar.Extraction.ML.Syntax
module BU = FStar.Util
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module UF = FStar.Syntax.Unionfind
module U  = FStar.Syntax.Util
module TC = FStar.TypeChecker.Tc
module N  = FStar.TypeChecker.Normalize
module PC = FStar.Parser.Const
module Util = FStar.Extraction.ML.Util
module Env = FStar.TypeChecker.Env
module TcUtil = FStar.TypeChecker.Util
module Env = FStar.TypeChecker.Env

type env_t = UEnv.uenv

(*This approach assumes that failwith already exists in scope. This might be problematic, see below.*)
let fail_exp (lid:lident) (t:typ) =
    mk (Tm_app(S.fvar PC.failwith_lid delta_constant None, //NS delta: wrong
               [ S.iarg t
               ; S.as_arg <|
                 mk (Tm_constant
                      (Const_string ("Not yet implemented:"^(Print.lid_to_string lid), Range.dummyRange)))
                    Range.dummyRange]))
        Range.dummyRange

let always_fail lid t =
    let imp =
        match U.arrow_formals t with
        | [], t ->
            // Avoid top-level failwith statements
            let b = mk_binder <| (gen_bv "_" None t) in
            U.abs [b] (fail_exp lid t) None
        | bs, t ->
            U.abs bs (fail_exp lid t) None
    in
    let lb = {
        lbname=Inr (S.lid_as_fv lid delta_constant None);
        lbunivs=[];
        lbtyp=t;
        lbeff=PC.effect_ML_lid;
        lbdef=imp;
        lbattrs=[];
        lbpos=imp.pos;
    } in
    lb

let as_pair = function
   | [a;b] -> (a,b)
   | _ -> failwith "Expected a list with 2 elements"

let flag_of_qual = function
  | Assumption -> Some Assumed
  | S.Private -> Some Private
  | S.NoExtract -> Some NoExtract
  | _ -> None

(*****************************************************************************)
(* Extracting type definitions from the signature                            *)
(*****************************************************************************)

// So far, we recognize only a couple special attributes; they are encoded as
// type constructors for an inductive defined in Pervasives, to provide a minimal
// amount of typo-checking via desugaring.
let rec extract_meta x =
  match SS.compress x with
  | { n = Tm_fvar fv } ->
      begin match string_of_lid (lid_of_fv fv) with
      | "FStar.Pervasives.PpxDerivingShow" -> Some PpxDerivingShow
      | "FStar.Pervasives.PpxDerivingYoJson" -> Some PpxDerivingYoJson
      | "FStar.Pervasives.CInline" -> Some CInline
      | "FStar.Pervasives.Substitute" -> Some Substitute
      | "FStar.Pervasives.Gc" -> Some GCType
      | "FStar.Pervasives.CAbstractStruct" -> Some CAbstract
      | "FStar.Pervasives.CIfDef" -> Some CIfDef
      | "FStar.Pervasives.CMacro" -> Some CMacro
      | "Prims.deprecated" -> Some (Deprecated "")
      | _ -> None
      end
  | { n = Tm_app ({ n = Tm_fvar fv }, [{ n = Tm_constant (Const_string (s, _)) }, _]) } ->
      begin match string_of_lid (lid_of_fv fv) with
      | "FStar.Pervasives.PpxDerivingShowConstant" -> Some (PpxDerivingShowConstant s)
      | "FStar.Pervasives.Comment" -> Some (Comment s)
      | "FStar.Pervasives.CPrologue" -> Some (CPrologue s)
      | "FStar.Pervasives.CEpilogue" -> Some (CEpilogue s)
      | "FStar.Pervasives.CConst" -> Some (CConst s)
      | "FStar.Pervasives.CCConv" -> Some (CCConv s)
      | "Prims.deprecated" -> Some (Deprecated s)
      | _ -> None
      end
  | { n = Tm_constant (Const_string ("KremlinPrivate", _)) } -> Some Private // This one generated internally
  // These are only for backwards compatibility, they should be removed at some point.
  | { n = Tm_constant (Const_string ("c_inline", _)) } -> Some CInline
  | { n = Tm_constant (Const_string ("substitute", _)) } -> Some Substitute
  | { n = Tm_meta (x, _) } -> extract_meta x
  | _ ->
    let head, args = U.head_and_args x in
    match (SS.compress head).n, args with
    | Tm_fvar fv, [_]
       when S.fv_eq_lid fv FStar.Parser.Const.remove_unused_type_parameters_lid ->
       begin
       match fst (FStar.ToSyntax.ToSyntax.parse_attr_with_list
                    false x FStar.Parser.Const.remove_unused_type_parameters_lid)
       with
       | None -> None
       | Some l -> Some (RemoveUnusedTypeParameters (l, S.range_of_fv fv))
       end
    | _ -> None

let extract_metadata metas =
  List.choose extract_meta metas

let binders_as_mlty_binders (env:UEnv.uenv) bs =
    BU.fold_map
      (fun env ({binder_bv=bv}) ->
        let env = UEnv.extend_ty env bv false in
        let name =
          match lookup_bv env bv with
          | Inl ty -> ty.ty_b_name
          | _ -> failwith "Impossible"
        in
        env, name)
      env bs

(*******************************************************************************)
(* A more convenient representation of inductive types for extraction purposes *)
(*******************************************************************************)

(*just enough info to generate OCaml code; add more info as needed*)
type data_constructor = {
  dname: lident;
  dtyp : typ;
}

type inductive_family = {
  ifv    : fv;
  iname  : lident;
  iparams: binders;
  ityp   : term;
  idatas : list<data_constructor>;
  iquals : list<S.qualifier>;
  imetadata : metadata;
}

let print_ifamily i =
    BU.print4 "\n\t%s %s : %s { %s }\n"
        (Print.lid_to_string i.iname)
        (Print.binders_to_string " " i.iparams)
        (Print.term_to_string i.ityp)
        (i.idatas
        |> List.map (fun d ->
            Print.lid_to_string d.dname
            ^ " : "
            ^ Print.term_to_string d.dtyp)
        |> String.concat "\n\t\t")

let bundle_as_inductive_families env ses quals
    : UEnv.uenv
    * list<inductive_family> =
    let env, ifams =
        BU.fold_map
        (fun env se -> match se.sigel with
            | Sig_inductive_typ(l, us, bs, t, _mut_i, datas) ->
                let _us, t = SS.open_univ_vars us t in
                let bs, t = SS.open_term bs t in
                let datas = ses |> List.collect (fun se -> match se.sigel with
                    | Sig_datacon(d, us, t, l', nparams, _) when Ident.lid_equals l l' ->
                        let _us, t = SS.open_univ_vars us t in
                        let bs', body = U.arrow_formals t in
                        let bs_params, rest = BU.first_N (List.length bs) bs' in
                        let subst = List.map2 (fun ({binder_bv=b'}) ({binder_bv=b}) -> S.NT(b', S.bv_to_name b)) bs_params bs in
                        let t = U.arrow rest (S.mk_Total body) |> SS.subst subst in
                        [{dname=d; dtyp=t}]
                    | _ -> []) in
                let metadata = extract_metadata se.sigattrs @ List.choose flag_of_qual quals in
                let fv = S.lid_as_fv l delta_constant None in
                let _, env = UEnv.extend_type_name env fv in
                env, [{   ifv = fv
                        ; iname=l
                        ; iparams=bs
                        ; ityp=t
                        ; idatas=datas
                        ; iquals=se.sigquals
                        ; imetadata = metadata }]
            | _ -> env, [])
        env ses in
    env, List.flatten ifams

(********************************************************************************************)
(* Extract Interfaces *)
(********************************************************************************************)

type tydef_declaration = (mlsymbol * FStar.Extraction.ML.Syntax.metadata * int) //int is the arity

type iface = {
    iface_module_name: mlpath;
    iface_bindings: list<(fv * exp_binding)>;
    iface_tydefs: list<(either<tydef, tydef_declaration>)>;
    iface_type_names:list<(fv * mlpath)>;
}

let empty_iface = {
    iface_module_name=[], "";
    iface_bindings = [];
    iface_tydefs = [];
    iface_type_names = []
}

let iface_of_bindings fvs = {
    empty_iface with
        iface_bindings = fvs;
}

let iface_of_tydefs tds = {
    empty_iface with
        iface_tydefs = List.map Inl tds;
        iface_type_names=List.map (fun td -> tydef_fv td, tydef_mlpath td) tds;
}

let iface_of_type_names fvs = {
    empty_iface with
        iface_type_names = fvs
}

let iface_union if1 if2 = {
    iface_module_name =
        (if if1.iface_module_name <> if1.iface_module_name
         then failwith "Union not defined"
         else if1.iface_module_name);
    iface_bindings = if1.iface_bindings @ if2.iface_bindings;
    iface_tydefs = if1.iface_tydefs @ if2.iface_tydefs;
    iface_type_names = if1.iface_type_names @ if2.iface_type_names
}

let iface_union_l ifs = List.fold_right iface_union ifs empty_iface

let mlpath_to_string (p:mlpath) =
    String.concat ". " (fst p @ [snd p])
let tscheme_to_string cm ts =
        (Code.string_of_mlty cm (snd ts))
let print_exp_binding cm e =
    BU.format3 "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s }"
        e.exp_b_name
        (Code.string_of_mlexpr cm e.exp_b_expr)
        (tscheme_to_string cm e.exp_b_tscheme)
let print_binding cm (fv, exp_binding) =
    BU.format2 "(%s, %s)"
            (Print.fv_to_string fv)
            (print_exp_binding cm exp_binding)
let print_tydef cm tydef =
  let name, defn =
      match tydef with
      | Inl tydef ->
        Print.fv_to_string (tydef_fv tydef),
        tscheme_to_string cm (tydef_def tydef)
      | Inr (p, _, _) ->
        p, "None"
  in
  BU.format2 "(%s, %s)" name defn
let iface_to_string iface =
    let cm = iface.iface_module_name in
    let print_type_name (tn, _) = Print.fv_to_string tn in
    BU.format4 "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
        (mlpath_to_string iface.iface_module_name)
        (List.map (print_binding cm) iface.iface_bindings |> String.concat "\n")
        (List.map (print_tydef cm) iface.iface_tydefs |> String.concat "\n")
        (List.map print_type_name iface.iface_type_names |> String.concat "\n")
let gamma_to_string env =
    let cm = current_module_of_uenv env in
    let gamma = List.collect (function Fv (b, e) -> [b, e] | _ -> []) (bindings_of_uenv env) in
    BU.format1 "Gamma = {\n %s }"
        (List.map (print_binding cm) gamma |> String.concat "\n")


(* Type abbreviations:
          //extracting `type t = e`
          //or         `let t = e` when e is a type

      Extraction for interfaces and implementations is basically the same

      - The returned env is extended with the tydef

      - A tydef provides the representation of the abbreviation
        unfolded all the way to a type constant, i.e., inductive or arrow

      - The list<mlmodule1> returned is the concrete definition
        of the abbreviation in ML, emitted only in the implementation
*)
let extract_typ_abbrev env quals attrs lb
    : env_t
    * iface
    * list<mlmodule1> =
    let tcenv, (lbdef, lbtyp) =
        let tcenv, _, def_typ =
          FStar.TypeChecker.Env.open_universes_in (tcenv_of_uenv env) lb.lbunivs [lb.lbdef; lb.lbtyp]
        in
        tcenv, as_pair def_typ
    in
    let lbtyp = FStar.TypeChecker.Normalize.normalize [Env.Beta;Env.UnfoldUntil delta_constant; Env.ForExtraction] tcenv lbtyp in
    //eta expansion is important; see issue #490
    let lbdef = FStar.TypeChecker.Normalize.eta_expand_with_type tcenv lbdef lbtyp in
    let fv = right lb.lbname in
    let lid = fv.fv_name.v in
    let def = SS.compress lbdef |> U.unmeta |> U.un_uinst in
    let def =
        match def.n with
        | Tm_abs _ -> Term.normalize_abs def
        | _ -> def in
    let bs, body =
        match def.n with
        | Tm_abs(bs, body, _) ->
          SS.open_term bs body
        | _ -> [], def in
    let assumed = BU.for_some (function Assumption -> true | _ -> false) quals in
    let env1, ml_bs = binders_as_mlty_binders env bs in
    let body =
      Term.term_as_mlty env1 body |> Util.eraseTypeDeep (Util.udelta_unfold env1)
    in
    let metadata =
      let has_val_decl = UEnv.has_tydef_declaration env lid in
      let meta = extract_metadata attrs @ List.choose flag_of_qual quals in
      if has_val_decl
      then (//BU.print1 "%s has val decl\n" (Ident.string_of_lid lid);
            HasValDecl (Ident.range_of_lid lid) :: meta)
      else (//BU.print1 "%s does not have val decl\n" (Ident.string_of_lid lid);
            meta)
    in
    let tyscheme = ml_bs, body in
    let mlpath, iface, env =
        if quals |> BU.for_some (function Assumption | New -> true | _ -> false)
        then let mlp, env = UEnv.extend_type_name env fv in
             mlp, iface_of_type_names [(fv, mlp)], env
        else let td, mlp, env = UEnv.extend_tydef env fv tyscheme metadata in
             mlp, iface_of_tydefs [td], env
    in
    let td = {
      tydecl_assumed = assumed;
      tydecl_name = snd mlpath;
      tydecl_ignored = None;
      tydecl_parameters = ml_bs;
      tydecl_meta = metadata;
      tydecl_defn = Some (MLTD_Abbrev body)
    } in
    let def = [MLM_Loc (Util.mlloc_of_range (Ident.range_of_lid lid)); MLM_Ty [td]] in
    env,
    iface,
    def

let extract_let_rec_type env quals attrs lb
    : env_t
    * iface
    * list<mlmodule1> =
    let lbtyp =
      FStar.TypeChecker.Normalize.normalize
        [Env.Beta;
         Env.AllowUnboundUniverses;
         Env.EraseUniverses;
         Env.UnfoldUntil delta_constant;
         Env.ForExtraction]
        (tcenv_of_uenv env)
        lb.lbtyp
    in
    let bs, _ = U.arrow_formals lbtyp in
    let env1, ml_bs = binders_as_mlty_binders env bs in
    let fv = right lb.lbname in
    let lid = fv.fv_name.v in
    let body = MLTY_Top in
    let metadata = extract_metadata attrs @ List.choose flag_of_qual quals in
    let assumed = false in
    let tscheme = ml_bs, body in
    let tydef, mlp, env = UEnv.extend_tydef env fv tscheme metadata in
    let td = {
      tydecl_assumed = assumed;
      tydecl_name = snd mlp;
      tydecl_ignored = None;
      tydecl_parameters = ml_bs;
      tydecl_meta = metadata;
      tydecl_defn = Some (MLTD_Abbrev body)
    } in
    let def = [MLM_Loc (Util.mlloc_of_range (Ident.range_of_lid lid)); MLM_Ty [td]] in
    let iface = iface_of_tydefs [tydef] in
    env,
    iface,
    def

(* extract_bundle_iface:
       Extracts a bundle of inductive type definitions for an interface

       Effectively providing names and types to the data constructors
       and arities for the type coonstructors
*)
let extract_bundle_iface env se
    : env_t * iface =
    let extract_ctor (env_iparams:env_t)
                     (ml_tyvars:list<mlsymbol>)
                     (env:env_t)
                     (ctor: data_constructor)
        :  env_t * (fv * exp_binding) =
        let mlt = Util.eraseTypeDeep
                    (Util.udelta_unfold env_iparams)
                    (Term.term_as_mlty env_iparams ctor.dtyp) in
        let tys = (ml_tyvars, mlt) in
        let fvv = lid_as_fv ctor.dname delta_constant None in
        let env, _, b = extend_fv env fvv tys false in
        env, (fvv, b)
    in

    let extract_one_family env ind
        : env_t * list<(fv * exp_binding)> =
       let env_iparams, vars  = binders_as_mlty_binders env ind.iparams in
       let env, ctors = ind.idatas |> BU.fold_map (extract_ctor env_iparams vars) env in
       let env =
         match BU.find_opt (function RecordType _ -> true | _ -> false) ind.iquals with
         | Some (RecordType (ns, ids)) ->
           let g =
            List.fold_right
                (fun id g ->
                   let _, g = UEnv.extend_record_field_name g (ind.iname, id) in
                   g)
                ids
                env
           in
           g
         | _ ->
          env
       in
       env, ctors
    in

    match se.sigel, se.sigquals with
    | Sig_bundle([{sigel = Sig_datacon(l, _, t, _, _, _)}], _), [ExceptionConstructor] ->
        let env, ctor = extract_ctor env [] env ({dname=l; dtyp=t}) in
        env, iface_of_bindings [ctor]

    | Sig_bundle(ses, _), quals ->
        if U.has_attribute se.sigattrs PC.erasable_attr
        then env, empty_iface
        else begin
          let env, ifams = bundle_as_inductive_families env ses quals in
          let env, td = BU.fold_map extract_one_family env ifams in
          env,
          iface_union
            (iface_of_type_names (List.map (fun x -> x.ifv, UEnv.mlpath_of_lident env x.iname) ifams))
            (iface_of_bindings (List.flatten td))
        end

    | _ -> failwith "Unexpected signature element"

let extract_type_declaration (g:uenv) is_interface_val lid quals attrs univs t
    : env_t
    * iface
    * list<mlmodule1>
    = if not (quals |> BU.for_some (function Assumption -> true | _ -> false))
      then let g = UEnv.extend_with_tydef_declaration g lid in
           g, empty_iface, []
      else let bs, _ = U.arrow_formals t in
           let fv = S.lid_as_fv lid delta_constant None in
           let lb = {
               lbname = BU.Inr fv;
               lbunivs = univs;
               lbtyp = t;
               lbeff = PC.effect_Tot_lid;
               lbdef = U.abs bs t_unit None;
               lbattrs = attrs;
               lbpos = t.pos
           } in
           let g, iface, mods = extract_typ_abbrev g quals attrs lb in
           let iface =
             if is_interface_val
             then let mlp = UEnv.mlpath_of_lident g lid in
                  let meta = extract_metadata attrs in
                  { empty_iface with iface_tydefs = [Inr (snd mlp, meta, List.length bs)] }
             else iface
           in
           g, iface, mods

let extract_reifiable_effect g ed
    : uenv
    * iface
    * list<mlmodule1> =
    let extend_iface lid mlp exp exp_binding =
        let fv = (S.lid_as_fv lid delta_equational None) in
        let lb = {
            mllb_name=snd mlp;
            mllb_tysc=None;
            mllb_add_unit=false;
            mllb_def=exp;
            mllb_meta = [];
            print_typ=false
            }
        in
        iface_of_bindings [fv, exp_binding], MLM_Let(NonRec, [lb])
    in

    let rec extract_fv tm =
        if Env.debug (tcenv_of_uenv g) <| Options.Other "ExtractionReify" then
            BU.print1 "extract_fv term: %s\n" (Print.term_to_string tm);
        match (SS.compress tm).n with
        | Tm_uinst (tm, _) -> extract_fv tm
        | Tm_fvar fv ->
            let mlp = mlpath_of_lident g fv.fv_name.v in
            let ({exp_b_tscheme=tysc}) = UEnv.lookup_fv tm.pos g fv in
            with_ty MLTY_Top <| MLE_Name mlp, tysc
        | _ -> failwith (BU.format2 "(%s) Not an fv: %s"
                                        (Range.string_of_range tm.pos)
                                        (Print.term_to_string tm))
    in

    let extract_action g (a:S.action) =
        assert (match a.action_params with | [] -> true | _ -> false);
        if Env.debug (tcenv_of_uenv g) <| Options.Other "ExtractionReify" then
            BU.print2 "Action type %s and term %s\n"
            (Print.term_to_string a.action_typ)
            (Print.term_to_string a.action_defn);
        let lbname = Inl (S.new_bv (Some a.action_defn.pos) tun) in
        let lb = mk_lb (lbname, a.action_univs, PC.effect_Tot_lid, a.action_typ, a.action_defn, [], a.action_defn.pos) in
        let lbs = (false, [lb]) in
        let action_lb = mk (Tm_let(lbs, U.exp_false_bool)) a.action_defn.pos in
        let a_let, _, ty = Term.term_as_mlexpr g action_lb in
        let exp, tysc = match a_let.expr with
            | MLE_Let((_, [mllb]), _) ->
                (match mllb.mllb_tysc with
                | Some(tysc) -> mllb.mllb_def, tysc
                | None -> failwith "No type scheme")
            | _ -> failwith "Impossible" in
        let a_nm, a_lid, exp_b, g = extend_with_action_name g ed a tysc in
        if Env.debug (tcenv_of_uenv g) <| Options.Other "ExtractionReify" then
            BU.print1 "Extracted action term: %s\n" (Code.string_of_mlexpr a_nm a_let);
        if Env.debug (tcenv_of_uenv g) <| Options.Other "ExtractionReify" then begin
            BU.print1 "Extracted action type: %s\n" (Code.string_of_mlty a_nm (snd tysc));
            List.iter (fun x -> BU.print1 "and binders: %s\n" x) (fst tysc) end;
        let iface, impl = extend_iface a_lid a_nm exp exp_b in
        g, (iface, impl)
    in

    let g, return_iface, return_decl =
        let return_tm, ty_sc = extract_fv (ed |> U.get_return_repr |> must |> snd) in
        let return_nm, return_lid, return_b, g = extend_with_monad_op_name g ed "return" ty_sc in
        let iface, impl = extend_iface return_lid return_nm return_tm return_b in
        g, iface, impl
    in

    let g, bind_iface, bind_decl =
        let bind_tm, ty_sc = extract_fv (ed |> U.get_bind_repr |> must |> snd) in
        let bind_nm, bind_lid, bind_b, g = extend_with_monad_op_name g ed "bind" ty_sc in
        let iface, impl = extend_iface bind_lid bind_nm bind_tm bind_b in
        g, iface, impl
    in

    let g, actions = BU.fold_map extract_action g ed.actions in
    let actions_iface, actions = List.unzip actions in

    g,
    iface_union_l (return_iface::bind_iface::actions_iface),
    return_decl::bind_decl::actions

let extract_let_rec_types se (env:uenv) (lbs:list<letbinding>) =
    //extracting `let rec t .. : Type = e
    //            and ...
    if BU.for_some (fun lb -> not (Term.is_arity env lb.lbtyp)) lbs
    then //mixtures of mutually recursively defined types and terms
         //are not yet supported
         Errors.raise_error
           (Errors.Fatal_ExtractionUnsupported,
             "Mutually recursively defined typed and terms cannot yet be extracted")
           se.sigrng
    else
      let env, iface_opt, impls =
          List.fold_left
            (fun (env, iface_opt, impls) lb ->
              let env, iface, impl =
                extract_let_rec_type env se.sigquals se.sigattrs lb
              in
              let iface_opt =
                match iface_opt with
                | None -> Some iface
                | Some iface' -> Some (iface_union iface' iface)
              in
              (env, iface_opt, impl::impls))
            (env, None, [])
            lbs
      in
      env,
      Option.get iface_opt,
      List.rev impls |> List.flatten

module EMB=FStar.Syntax.Embeddings

let get_noextract_to (se:sigelt) (backend:option<Options.codegen_t>) : bool =
  BU.for_some (function attr ->
    let hd, args = U.head_and_args attr in
    match (SS.compress hd).n, args with
    | Tm_fvar fv, [(a, _)] when S.fv_eq_lid fv PC.noextract_to_attr ->
        begin match EMB.unembed EMB.e_string a false EMB.id_norm_cb with
        | Some s ->
          Option.isSome backend && Options.parse_codegen s = backend
        | None ->
          false
        end
    | _ -> false
  ) se.sigattrs

(*
 * We support two kinds of noextract knobs:
 *   - a noextract qualifier
 *   - a "noextract_to" attribute that takes a string value as argument
 *     the string value is the backend name, e.g. Kremlin, OCaml, ...
 *
 * Whether to extract a definition depends on the backend
 *   since sometimes Kremlin needs the stubs even for definitions
 *   marked as noextract
 *
 * TODO: what are such cases? Even there, can we optimize
 *   extraction to extract only the signature of the definition
 *   so that we don't pay the cost of normalization etc. for the body
 *)
let sigelt_has_noextract (se:sigelt) : bool =
  let has_noextract_qualifier = List.contains S.NoExtract se.sigquals in
  let has_noextract_attribute = get_noextract_to se (Options.codegen ()) in
  match Options.codegen () with
  | Some Options.Kremlin ->
    has_noextract_qualifier && has_noextract_attribute
  | _ ->
    has_noextract_qualifier || has_noextract_attribute
  
// If this sigelt had [@@ noextract_to "Kremlin"] and we are indeed
// extracting to Kremlin, then we will still process it: it's the
// kremlin pipeline which will later drop the body. It checks for the
// NoExtract qualifier to decide that, so we add it here.
let kremlin_fixup_qual (se:sigelt) : sigelt =
 if Options.codegen () = Some Options.Kremlin
    && get_noextract_to se (Some Options.Kremlin)
    && not (List.contains S.NoExtract se.sigquals)
 then { se with sigquals = S.NoExtract :: se.sigquals }
 else se

let mark_sigelt_erased (se:sigelt) (g:uenv) : uenv =
  debug g (fun u -> BU.print1 ">>>> NOT extracting %s \n" (Print.sigelt_to_string_short se));
  // Cheating with delta levels and qualifiers below, but we don't ever use them.
  List.fold_right (fun lid g -> extend_erased_fv g (S.lid_as_fv lid delta_constant None))
                  (U.lids_of_sigelt se) g

(*  The top-level extraction of a sigelt to an interface *)
let extract_sigelt_iface (g:uenv) (se:sigelt) : uenv * iface =
    if sigelt_has_noextract se then
      let g = mark_sigelt_erased se g in
      g, empty_iface
    else
    let se = kremlin_fixup_qual se in

    match se.sigel with
    | Sig_bundle _
    | Sig_inductive_typ _
    | Sig_datacon _ ->
      extract_bundle_iface g se

    | Sig_declare_typ(lid, univs, t)  when Term.is_arity g t -> //lid is a type
      let env, iface, _ =
          extract_type_declaration g true lid se.sigquals se.sigattrs univs t
      in
      env, iface

    | Sig_let((false, [lb]), _) when Term.is_arity g lb.lbtyp ->
      if se.sigquals |> BU.for_some (function Projector _ -> true | _ -> false)
      then (
        //Don't extract projectors returning types---not useful for typing generated code and
        //And can actually break F# extraction, in case there are unused type parameters
        g, empty_iface
      ) else (
        let env, iface, _ =
          extract_typ_abbrev g se.sigquals se.sigattrs lb
        in
        env, iface
      )

    | Sig_let ((true, lbs), _)
      when BU.for_some (fun lb -> Term.is_arity g lb.lbtyp) lbs ->
      let env, iface, _ =
        extract_let_rec_types se g lbs
      in
      env, iface

    | Sig_declare_typ(lid, _univs, t) ->
      let quals = se.sigquals in
      if quals |> List.contains Assumption
      && not (TcUtil.must_erase_for_extraction (tcenv_of_uenv g) t)
      then let g, bindings = Term.extract_lb_iface g (false, [always_fail lid t]) in
           g, iface_of_bindings bindings
      else g, empty_iface //it's not assumed, so wait for the corresponding Sig_let to generate code
                    //or, it must be erased

    | Sig_let (lbs, _) ->
      let g, bindings = Term.extract_lb_iface g lbs in
      g, iface_of_bindings bindings

    | Sig_assume _
    | Sig_sub_effect  _
    | Sig_effect_abbrev _
    | Sig_polymonadic_bind _
    | Sig_polymonadic_subcomp _ ->
      g, empty_iface

    | Sig_pragma (p) ->
      U.process_pragma p se.sigrng;
      g, empty_iface

    | Sig_splice _ ->
      failwith "impossible: trying to extract splice"

    | Sig_fail _ ->
      failwith "impossible: trying to extract Sig_fail"

    | Sig_new_effect ed ->
      if Env.is_reifiable_effect (tcenv_of_uenv g) ed.mname
      && List.isEmpty ed.binders //we do not extract parameterized effects
      then let env, iface, _ = extract_reifiable_effect g ed in
           env, iface
      else g, empty_iface

let extract_iface' (g:env_t) modul =
    if Options.interactive() then g, empty_iface else
    let _ = Options.restore_cmd_line_options true in
    let decls = modul.declarations in
    let iface = {empty_iface with iface_module_name=(current_module_of_uenv g)} in
    let res =
        List.fold_left (fun (g, iface) se ->
            let g, iface' = extract_sigelt_iface g se in
            g, iface_union iface iface')
            (g, iface)
            decls
    in
    ignore <| Options.restore_cmd_line_options true;
    res

let extract_iface (g:env_t) modul =
  let g, iface =
    UF.with_uf_enabled (fun () ->
      if Options.debug_any()
      then FStar.Util.measure_execution_time
             (BU.format1 "Extracted interface of %s" (string_of_lid modul.name))
             (fun () -> extract_iface' g modul)
      else extract_iface' g modul)
  in
  let g, _ = UEnv.with_typars_env g (fun e ->
    let iface_tydefs : list<RemoveUnusedParameters.tydef> =
      List.map
        (function
          | Inl td -> snd (UEnv.tydef_mlpath td), UEnv.tydef_meta td, Inl (UEnv.tydef_def td)
          | Inr (p, m, n) -> p, m, Inr n)
        iface.iface_tydefs
    in
    let module_name, _ = UEnv.extend_with_module_name g modul.name in
    let e = RemoveUnusedParameters.set_current_module e module_name in
    RemoveUnusedParameters.elim_tydefs e iface_tydefs)
  in
  UEnv.exit_module g, iface

(********************************************************************************************)
(* Extract Implementations *)
(********************************************************************************************)

let extract_bundle env se =
    let extract_ctor (env_iparams:env_t)
                     (ml_tyvars:list<mlsymbol>)
                     (env:env_t)
                     (ctor: data_constructor):
        env_t * (mlsymbol * list<(mlsymbol * mlty)>)
        =
        let mlt = Util.eraseTypeDeep (Util.udelta_unfold env_iparams) (Term.term_as_mlty env_iparams ctor.dtyp) in
        let steps = [ Env.Inlining; Env.UnfoldUntil S.delta_constant; Env.EraseUniverses; Env.AllowUnboundUniverses; Env.ForExtraction ] in
        let names = match (SS.compress (N.normalize steps (tcenv_of_uenv env_iparams) ctor.dtyp)).n with
          | Tm_arrow (bs, _) ->
              List.map (fun ({binder_bv={ ppname = ppname }}) -> (string_of_id ppname)) bs
          | _ ->
              []
        in
        let tys = (ml_tyvars, mlt) in
        let fvv = lid_as_fv ctor.dname delta_constant None in
        let env, mls, _ = extend_fv env fvv tys false in
        env,
        (mls, List.zip names (argTypes mlt)) in

    let extract_one_family env ind =
       let env_iparams, vars  = binders_as_mlty_binders env ind.iparams in
       let env, ctors = ind.idatas |> BU.fold_map (extract_ctor env_iparams vars) env in
       let indices, _ = U.arrow_formals ind.ityp in
       let ml_params = List.append vars (indices |> List.mapi (fun i _ -> "'dummyV" ^ BU.string_of_int i)) in
       let tbody, env =
         match BU.find_opt (function RecordType _ -> true | _ -> false) ind.iquals with
         | Some (RecordType (ns, ids)) ->
             let _, c_ty = List.hd ctors in
             assert (List.length ids = List.length c_ty);
             let fields, g =
                List.fold_right2
                  (fun id (_, ty) (fields, g) ->
                     let mlid, g = UEnv.extend_record_field_name g (ind.iname, id) in
                     (mlid, ty)::fields, g)
                   ids
                   c_ty
                   ([], env)
             in
             Some (MLTD_Record fields), g
         | _ when List.length ctors = 0 ->
             None, env
         | _ ->
             Some (MLTD_DType ctors), env
       in
       let td = {
         tydecl_assumed = false;
         tydecl_name = snd (mlpath_of_lident env ind.iname);
         tydecl_ignored = None;
         tydecl_parameters = ml_params;
         tydecl_meta = ind.imetadata;
         tydecl_defn = tbody
       } in
       env,
       td
    in

    match se.sigel, se.sigquals with
    | Sig_bundle([{sigel = Sig_datacon(l, _, t, _, _, _)}], _), [ExceptionConstructor] ->
        let env, ctor = extract_ctor env [] env ({dname=l; dtyp=t}) in
        env, [MLM_Exn ctor]

    | Sig_bundle(ses, _), quals ->
        if U.has_attribute se.sigattrs PC.erasable_attr
        then env, []
        else begin
          let env, ifams = bundle_as_inductive_families env ses quals in
          let env, td = BU.fold_map extract_one_family env ifams in
          env, [MLM_Ty td]
        end

    | _ -> failwith "Unexpected signature element"



(* When extracting a plugin, each top-level definition marked with a `@plugin` attribute
   is extracted along with an invocation to FStar.Tactics.Native.register_tactic or register_plugin,
   which installs the compiled term as a primitive step in the normalizer
 *)
let maybe_register_plugin (g:env_t) (se:sigelt) : list<mlmodule1> =
    let w = with_ty MLTY_Top in
    let plugin_with_arity attrs =
        BU.find_map attrs (fun t ->
              let head, args = U.head_and_args t in
              if not (U.is_fvar PC.plugin_attr head)
              then None
              else match args with
                   | [({n=Tm_constant (Const_int(s, _))}, _)] ->
                     Some (Some (BU.int_of_string s))
                   | _ -> Some None)
    in
    if Options.codegen() <> Some Options.Plugin then []
    else match plugin_with_arity se.sigattrs with
         | None -> []
         | Some arity_opt ->
           // BU.print2 "Got plugin with attrs = %s; arity_opt=%s"
           //          (List.map Print.term_to_string se.sigattrs |> String.concat " ")
           //          (match arity_opt with None -> "None" | Some x -> "Some " ^ string_of_int x);
           begin
           match se.sigel with
           | Sig_let(lbs, lids) ->
               let mk_registration lb : list<mlmodule1> =
                  let fv = right lb.lbname in
                  let fv_lid = fv.fv_name.v in
                  let fv_t = lb.lbtyp in
                  let ml_name_str = MLE_Const (MLC_String (Ident.string_of_lid fv_lid)) in
                  match Util.interpret_plugin_as_term_fun g fv fv_t arity_opt ml_name_str with
                  | Some (interp, nbe_interp, arity, plugin) ->
                      let register, args =
                        if plugin
                        then (["FStar_Tactics_Native"], "register_plugin"), [interp; nbe_interp]
                        else (["FStar_Tactics_Native"], "register_tactic"), [interp]
                      in
                      let h = with_ty MLTY_Top <| MLE_Name register in
                      let arity  = MLE_Const (MLC_Int(string_of_int arity, None)) in
                      let app = with_ty MLTY_Top <| MLE_App (h, [w ml_name_str; w arity] @ args) in
                      [MLM_Top app]
                  | None -> []
               in
               List.collect mk_registration (snd lbs)
           | _ -> []
           end


(*****************************************************************************)
(* Extracting the top-level definitions in a module                          *)
(*****************************************************************************)
let rec extract_sig (g:env_t) (se:sigelt) : env_t * list<mlmodule1> =
  Errors.with_ctx (BU.format1 "While extracting top-level definition `%s`" (Print.sigelt_to_string_short se)) (fun () ->
     debug g (fun u -> BU.print1 ">>>> extract_sig %s \n" (Print.sigelt_to_string_short se));

     if sigelt_has_noextract se then
       let g = mark_sigelt_erased se g in
       g, []
     else
    let se = kremlin_fixup_qual se in

     match se.sigel with
        | Sig_bundle _
        | Sig_inductive_typ _
        | Sig_datacon _ ->
          extract_bundle g se

        | Sig_new_effect ed when Env.is_reifiable_effect (tcenv_of_uenv g) ed.mname ->
          let env, _iface, impl =
              extract_reifiable_effect g ed in
          env, impl

        | Sig_splice _ ->
          failwith "impossible: trying to extract splice"

        | Sig_fail _ ->
          failwith "impossible: trying to extract Sig_fail"

        | Sig_new_effect _ ->
          g, []

        | Sig_declare_typ(lid, univs, t)  when Term.is_arity g t -> //lid is a type
          //extracting `assume type t : k`
          let env, _, impl = extract_type_declaration g false lid se.sigquals se.sigattrs univs t in
          env, impl

        | Sig_let((false, [lb]), _) when Term.is_arity g lb.lbtyp ->
          //extracting `type t = e`
          //or         `let t = e` when e is a type
          if se.sigquals |> BU.for_some (function Projector _ -> true | _ -> false)
          then (
            //Don't extract projectors returning types---not useful for typing generated code and
            //And can actually break F# extraction, in case there are unused type parameters
            g, []
          ) else (
            let env, _, impl =
                extract_typ_abbrev g se.sigquals se.sigattrs lb
            in
            env, impl
          )

        | Sig_let((true, lbs), _)
          when BU.for_some (fun lb -> Term.is_arity g lb.lbtyp) lbs ->
          //extracting `let rec t .. : Type = e
          //            and ...
          let env, _, impl =
            extract_let_rec_types se g lbs
          in
          env, impl

        | Sig_let (lbs, _) ->
          let attrs = se.sigattrs in
          let quals = se.sigquals in
          let attrs, post_tau =
              match U.extract_attr' PC.postprocess_extr_with attrs with
              | None -> attrs, None
              | Some (ats, (tau, None)::_) -> ats, Some tau
              | Some (ats, args) ->
                  Errors.log_issue se.sigrng (Errors.Warning_UnrecognizedAttribute,
                                         ("Ill-formed application of `postprocess_for_extraction_with`"));
                  attrs, None
          in
          let postprocess_lb (tau:term) (lb:letbinding) : letbinding =
              let lbdef = Env.postprocess (tcenv_of_uenv g) tau lb.lbtyp lb.lbdef in
              { lb with lbdef = lbdef }
          in
          let lbs = (fst lbs,
                      (match post_tau with
                       | Some tau -> List.map (postprocess_lb tau) (snd lbs)
                       | None -> (snd lbs)))
          in
          let ml_let, _, _ =
            Term.term_as_mlexpr
                    g
                    (mk (Tm_let(lbs, U.exp_false_bool)) se.sigrng)
          in
          begin
          match ml_let.expr with
          | MLE_Let((flavor, bindings), _) ->

            (* Treatment of qualifiers: we synthesize the metadata that goes
                * onto each let-binding as follows:
                * - F* keywords (qualifiers, such as "inline_for_extraction" or
                *   "private") are in [quals] and are distributed on each
                *   let-binding in the mutually recursive block of bindings
                * - F* attributes (custom arbitrary terms, such as "[@ GcType
                *   ]"), are attached to the block of mutually recursive
                *   definitions, we don't have syntax YET for attaching these
                *   to individual definitions
                * - some extra information is looked up here and added as a
                *   bonus; in particular, the MustDisappear attribute (that
                *   StackInline bestows upon an individual let-binding) is
                *   specific to each let-binding! *)
            let flags = List.choose flag_of_qual quals in
            let flags' = extract_metadata attrs in

            let g, ml_lbs' =
                List.fold_left2
                    (fun (env, ml_lbs) (ml_lb:mllb) {lbname=lbname; lbtyp=t } ->
                        if ml_lb.mllb_meta |> List.contains Erased
                        then env, ml_lbs
                        else
                            // debug g (fun () -> printfn "Translating source lb %s at type %s to %A" (Print.lbname_to_string lbname) (Print.typ_to_string t) (must (mllb.mllb_tysc)));
                            let lb_lid = (right lbname).fv_name.v in
                            let flags'' =
                                match (SS.compress t).n with
                                | Tm_arrow (_, { n = Comp { effect_name = e }})
                                    when string_of_lid e = "FStar.HyperStack.ST.StackInline" ->
                                    [ StackInline ]
                                | _ ->
                                    []
                            in
                            let meta = flags @ flags' @ flags'' in
                            let ml_lb = { ml_lb with mllb_meta = meta } in
                            let g, ml_lb =
                                if quals |> BU.for_some (function Projector _ -> true | _ -> false) //projector names have to mangled
                                then let env, mls, _ =
                                         UEnv.extend_fv
                                                env
                                                (right lbname)
                                                (must ml_lb.mllb_tysc)
                                                ml_lb.mllb_add_unit
                                     in
                                     env, {ml_lb with mllb_name=mls }
                                else let env, _, _ = UEnv.extend_lb env lbname t (must ml_lb.mllb_tysc) ml_lb.mllb_add_unit in
                                     env, ml_lb in
                        g, ml_lb::ml_lbs)
                (g, [])
                bindings
                (snd lbs) in
            g,
            [MLM_Loc (Util.mlloc_of_range se.sigrng);
             MLM_Let (flavor, List.rev ml_lbs')]
            @ maybe_register_plugin g se

        | _ ->
          failwith (BU.format1 "Impossible: Translated a let to a non-let: %s" (Code.string_of_mlexpr (current_module_of_uenv g) ml_let))
        end

       | Sig_declare_typ(lid, _, t) ->
         let quals = se.sigquals in
         if quals |> List.contains Assumption
         && not (TcUtil.must_erase_for_extraction (tcenv_of_uenv g) t)
         then let always_fail =
                  { se with sigel = Sig_let((false, [always_fail lid t]), []) } in
              let g, mlm = extract_sig g always_fail in //extend the scope with the new name
              match BU.find_map quals (function Discriminator l -> Some l |  _ -> None) with
              | Some l -> //if it's a discriminator, generate real code for it, rather than mlm
                g, [MLM_Loc (Util.mlloc_of_range se.sigrng); Term.ind_discriminator_body g lid l]

              | _ ->
                begin match BU.find_map quals (function  Projector (l,_)  -> Some l |  _ -> None) with
                    (* TODO : this could fail, it happens that projectors for variants are assumed *)
                    | Some _ -> //it must be a record projector, since other projectors are not assumed
                        g, [] //records are extracted as ML records; no projectors for them
                    | _ ->
                        g, mlm //in all other cases, generate mlm, a stub that always fails
                end
         else g, [] //it's not assumed, so wait for the corresponding Sig_let to generate code
                    //or, it must be erased

       | Sig_assume _ //not needed; purely logical
       | Sig_sub_effect  _
       | Sig_effect_abbrev _ //effects are all primitive; so these are not extracted; this may change as we add user-defined non-primitive effects
       | Sig_polymonadic_bind _
       | Sig_polymonadic_subcomp _ ->
         g, []
       | Sig_pragma (p) ->
         U.process_pragma p se.sigrng;
         g, []
  )

let extract' (g:uenv) (m:modul) : uenv * option<mllib> =
  let _ = Options.restore_cmd_line_options true in
  let name, g = UEnv.extend_with_module_name g m.name in
  let g = set_tcenv g (FStar.TypeChecker.Env.set_current_module (tcenv_of_uenv g) m.name) in
  let g = set_current_module g name in
  let g, sigs =
    BU.fold_map
        (fun g se ->
            if Options.debug_module (string_of_lid m.name)
            then let nm = FStar.Syntax.Util.lids_of_sigelt se |> List.map Ident.string_of_lid |> String.concat ", " in
                 BU.print1 "+++About to extract {%s}\n" nm;
                 FStar.Util.measure_execution_time
                       (BU.format1 "---Extracted {%s}" nm)
                       (fun () -> extract_sig g se)
            else extract_sig g se)
        g m.declarations in
  let mlm : mlmodule = List.flatten sigs in
  let is_kremlin = Options.codegen () = Some Options.Kremlin in
  if string_of_lid m.name <> "Prims"
  && (is_kremlin || not m.is_interface)
  then begin
    if not (Options.silent()) then (BU.print1 "Extracted module %s\n" (string_of_lid m.name));
    g, Some (MLLib ([name, Some ([], mlm), (MLLib [])]))
  end
  else g, None

let extract (g:uenv) (m:modul) =
  ignore <| Options.restore_cmd_line_options true;
  if not (Options.should_extract (string_of_lid m.name)) then
    failwith (BU.format1 "Extract called on a module %s that should not be extracted" (Ident.string_of_lid m.name));

  if Options.interactive() then g, None else begin

  let nm = string_of_lid m.name in
  let g, mllib =
    UF.with_uf_enabled (fun () ->
      Errors.with_ctx ("While extracting module " ^ nm) (fun () ->
        if Options.debug_any () then
          let msg = BU.format1 "Extracting module %s" nm in
          BU.measure_execution_time msg (fun () -> extract' g m)
        else
          extract' g m))
  in
  let g, mllib =
    match mllib with
    | None ->
      g, mllib
    | Some mllib ->
      let g, mllib = UEnv.with_typars_env g (fun e -> RemoveUnusedParameters.elim_mllib e mllib) in
      g, Some mllib
  in
  ignore <| Options.restore_cmd_line_options true;
  exit_module g, mllib
  end
