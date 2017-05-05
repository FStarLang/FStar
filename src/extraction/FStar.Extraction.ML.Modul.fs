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
open FStar.All
open FStar
open FStar.Util
open FStar.Syntax.Syntax
open FStar.Const
open FStar.Extraction.ML.Syntax
open FStar.Extraction.ML.UEnv
open FStar.Extraction.ML.Util
open FStar.Ident

module Term = FStar.Extraction.ML.Term
module Print = FStar.Syntax.Print
module MLS = FStar.Extraction.ML.Syntax
module BU = FStar.Util
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U  = FStar.Syntax.Util
module TC = FStar.TypeChecker.Tc
module N  = FStar.TypeChecker.Normalize
module C  = FStar.Syntax.Const
module Util = FStar.Extraction.ML.Util
module Env = FStar.TypeChecker.Env

(*This approach assumes that failwith already exists in scope. This might be problematic, see below.*)
let fail_exp (lid:lident) (t:typ) =
    mk (Tm_app(S.fvar C.failwith_lid Delta_constant None,
               [ S.iarg t
               ; S.as_arg <| mk (Tm_constant (Const_string (Bytes.string_as_unicode_bytes ("Not yet implemented:"^(Print.lid_to_string lid)), Range.dummyRange))) None Range.dummyRange]))
        None
        Range.dummyRange

let mangle_projector_lid (x: lident) : lident =
    x

let lident_as_mlsymbol (id : lident) : mlsymbol = id.ident.idText

let as_pair = function
   | [a;b] -> (a,b)
   | _ -> failwith "Expected a list with 2 elements"

(*****************************************************************************)
(* Extracting type definitions from the signature                            *)
(*****************************************************************************)
let binders_as_mlty_binders (env:UEnv.env) bs =
    BU.fold_map (fun env (bv, _) ->
//        if Term.is_type env.tcenv bv.sort || true
//        then
        UEnv.extend_ty env bv (Some (MLTY_Var (bv_as_ml_tyvar bv))), bv_as_ml_tyvar bv
//        else UEnv.extend_bv env bv ([], erasedContent) false false false, bv_as_ml_tyvar bv
    )
    env bs

//Type abbreviations
let extract_typ_abbrev env fv quals def =
    let lid = fv.fv_name.v in
    let def = SS.compress def |> U.unmeta |> U.un_uinst in
    let def = match def.n with
        | Tm_abs _ -> Term.normalize_abs def
        | _ -> def in
    let bs, body = match def.n with
        | Tm_abs(bs, body, _) ->
          SS.open_term bs body
        | _ -> [], def in
    let assumed = BU.for_some (function Assumption -> true | _ -> false) quals in
    let env, ml_bs = binders_as_mlty_binders env bs in
    let body = Term.term_as_mlty env body |> Util.eraseTypeDeep (Util.udelta_unfold env) in
    let mangled_projector =
         if quals |> BU.for_some (function Projector _ -> true | _ -> false) //projector names have to mangled
         then let mname = mangle_projector_lid lid in
              Some mname.ident.idText
         else None in
    let td = [assumed, lident_as_mlsymbol lid, mangled_projector, ml_bs, Some (MLTD_Abbrev body)] in
    let def = [MLM_Loc (Util.mlloc_of_range (Ident.range_of_lid lid)); MLM_Ty td] in
    let env = if quals |> BU.for_some (function Assumption | New -> true | _ -> false)
              then env
              else UEnv.extend_tydef env fv td in
    env, def


//Extracting inductive type definitions

(*just enough info to generate OCaml code; add more info as needed*)
type data_constructor = {
  dname: lident;
  dtyp : typ;
}

type inductive_family = {
  iname  : lident;
  iparams: binders;
  ityp   : term;
  idatas : list<data_constructor>;
  iquals : list<S.qualifier>
}

let print_ifamily i =
    BU.print4 "\n\t%s %s : %s { %s }\n"
        (Print.lid_to_string i.iname)
        (Print.binders_to_string " " i.iparams)
        (Print.term_to_string i.ityp)
        (i.idatas |> List.map (fun d -> Print.lid_to_string d.dname ^ " : " ^ Print.term_to_string d.dtyp) |> String.concat "\n\t\t")

let bundle_as_inductive_families env ses quals : list<inductive_family> =
    ses |> List.collect
        (fun se -> match se.sigel with
            | Sig_inductive_typ(l, _us, bs, t, _mut_i, datas) ->
                let bs, t = SS.open_term bs t in
                let datas = ses |> List.collect (fun se -> match se.sigel with
                    | Sig_datacon(d, _, t, l', nparams, _) when Ident.lid_equals l l' ->
                        let bs', body = U.arrow_formals t in
                        let bs_params, rest = BU.first_N (List.length bs) bs' in
                        let subst = List.map2 (fun (b', _) (b, _) -> S.NT(b', S.bv_to_name b)) bs_params bs in
                        let t = U.arrow rest (S.mk_Total body) |> SS.subst subst in
                        [{dname=d; dtyp=t}]
                    | _ -> []) in
                [{  iname=l
                  ; iparams=bs
                  ; ityp=t
                  ; idatas=datas
                  ; iquals=se.sigquals  }]

            | _ -> [])

type env_t = UEnv.env

let extract_bundle env se =
    let extract_ctor (ml_tyvars:list<(mlsymbol*int)>) (env:env_t) (ctor: data_constructor):  env_t * (mlsymbol * list<mlty>) =
        let mlt = Util.eraseTypeDeep (Util.udelta_unfold env) (Term.term_as_mlty env ctor.dtyp) in
        let tys = (ml_tyvars, mlt) in
        let fvv = mkFvvar ctor.dname ctor.dtyp in
        fst (extend_fv env fvv tys false false),
        (lident_as_mlsymbol ctor.dname, argTypes mlt) in

    let extract_one_family env ind =
       let env, vars  = binders_as_mlty_binders env ind.iparams in
       let env, ctors = ind.idatas |> BU.fold_map (extract_ctor vars) env in
       let indices, _ = U.arrow_formals ind.ityp in
       let ml_params = List.append vars (indices |> List.mapi (fun i _ -> "'dummyV" ^ BU.string_of_int i, 0)) in
       let tbody = match BU.find_opt (function RecordType _ -> true | _ -> false) ind.iquals with
            | Some (RecordType (ns, ids)) ->
              let _, c_ty = List.hd ctors in
              assert (List.length ids = List.length c_ty);
              let fields = List.map2 (fun id ty -> let lid = lid_of_ids (ns @ [id]) in (lident_as_mlsymbol lid), ty) ids c_ty in
              MLTD_Record fields

            | _ -> MLTD_DType ctors in
        env,  (false, lident_as_mlsymbol ind.iname, None, ml_params, Some tbody) in


    match se.sigel, se.sigquals with
        | Sig_bundle([{sigel = Sig_datacon(l, _, t, _, _, _)}], _), [ExceptionConstructor] ->
          let env, ctor = extract_ctor [] env ({dname=l; dtyp=t}) in
          env, [MLM_Exn ctor]

        | Sig_bundle(ses, _), quals ->
          let ifams = bundle_as_inductive_families env ses quals in
//          ifams |> List.iter print_ifamily;
          let env, td = BU.fold_map extract_one_family env ifams in
          env, [MLM_Ty td]

        | _ -> failwith "Unexpected signature element"


(*****************************************************************************)
(* Extracting the top-level definitions in a module                          *)
(*****************************************************************************)
let rec extract_sig (g:env_t) (se:sigelt) : env_t * list<mlmodule1> =
     debug g (fun u -> BU.print1 ">>>> extract_sig %s \n" (Print.sigelt_to_string se));
     match se.sigel with
        | Sig_bundle _
        | Sig_inductive_typ _
        | Sig_datacon _ ->
          extract_bundle g se

        | Sig_new_effect ed when se.sigquals |> List.contains Reifiable ->
          let extend_env g lid ml_name tm tysc =
            let g, mangled_name = extend_fv' g (S.lid_as_fv lid Delta_equational None) ml_name tysc false false in
            if Env.debug g.tcenv <| Options.Other "ExtractionReify" then
            BU.print1 "Mangled name: %s\n" (fst mangled_name);
            let lb = {
                mllb_name=mangled_name;
                mllb_tysc=None;
                mllb_add_unit=false;
                mllb_def=tm;
                print_typ=false
              }
            in
            g, MLM_Let(NonRec, [], [lb])
          in

          let rec extract_fv tm =
            if Env.debug g.tcenv <| Options.Other "ExtractionReify" then
              BU.print1 "extract_fv term: %s\n" (Print.term_to_string tm);
            match (SS.compress tm).n with
            | Tm_uinst (tm, _) -> extract_fv tm
            | Tm_fvar fv ->
              let mlp = mlpath_of_lident fv.fv_name.v in
              let _, _, tysc, _ = BU.right <| UEnv.lookup_fv g fv in
              with_ty MLTY_Top <| MLE_Name mlp, tysc
            | _ -> failwith "Not an fv" in

          let extract_action g (a:S.action) =
            assert (match a.action_params with | [] -> true | _ -> false);
            if Env.debug g.tcenv <| Options.Other "ExtractionReify" then
              BU.print2 "Action type %s and term %s\n"
                (Print.term_to_string a.action_typ)
                (Print.term_to_string a.action_defn);
            let a_nm, a_lid = action_name ed a in
            let lbname = Inl (S.new_bv (Some a.action_defn.pos) tun) in
            let lb = mk_lb (lbname, a.action_univs, C.effect_Tot_lid, a.action_typ, a.action_defn) in
            let lbs = (false, [lb]) in
            let action_lb = mk (Tm_let(lbs, FStar.Syntax.Const.exp_false_bool)) None a.action_defn.pos in
            let a_let, _, ty = Term.term_as_mlexpr g action_lb in
            if Env.debug g.tcenv <| Options.Other "ExtractionReify" then
              BU.print1 "Extracted action term: %s\n" (Code.string_of_mlexpr a_nm a_let);
            let exp, tysc = match a_let.expr with
              | MLE_Let((_, _, [mllb]), _) ->
                  (match mllb.mllb_tysc with
                  | Some(tysc) -> mllb.mllb_def, tysc
                  | None -> failwith "No type scheme")
              | _ -> failwith "Impossible" in
            if Env.debug g.tcenv <| Options.Other "ExtractionReify" then begin
              BU.print1 "Extracted action type: %s\n" (Code.string_of_mlty a_nm (snd tysc));
              List.iter (fun x -> BU.print1 "and binders: %s\n" (fst x)) (fst tysc) end;
            extend_env g a_lid a_nm exp tysc in

          let g, return_decl =
            let return_tm, ty_sc = extract_fv (snd ed.return_repr) in
            let return_nm, return_lid = monad_op_name ed "return" in
            extend_env g return_lid return_nm return_tm ty_sc in

          let g, bind_decl =
            let bind_tm, ty_sc = extract_fv (snd ed.bind_repr) in
            let bind_nm, bind_lid = monad_op_name ed "bind" in
            extend_env g bind_lid bind_nm bind_tm ty_sc in

          let g, actions = BU.fold_map extract_action g ed.actions in

          g, [return_decl;bind_decl]@actions

        | Sig_new_effect _ ->
          g, []

        | Sig_declare_typ(lid, _, t)  when Term.is_arity g t -> //lid is a type
          //extracting `assume type t : k`
          let quals = se.sigquals in
          if not (quals |> BU.for_some (function Assumption -> true | _ -> false))
          then g, []
          else let bs, _ = U.arrow_formals t in
               let fv = S.lid_as_fv lid Delta_constant None in
               extract_typ_abbrev g fv quals (U.abs bs TypeChecker.Common.t_unit None)

        | Sig_let((false, [lb]), _, _) when Term.is_arity g lb.lbtyp ->
          //extracting `type t = e`
          //or         `let t = e` when e is a type
          let quals = se.sigquals in
          let tcenv, (lbdef, lbtyp) =
            let tcenv, _, def_typ =
                FStar.TypeChecker.Env.open_universes_in g.tcenv lb.lbunivs [lb.lbdef; lb.lbtyp] in
            tcenv, as_pair def_typ in
          let lbtyp = FStar.TypeChecker.Normalize.unfold_whnf tcenv lbtyp in
          let lbdef = FStar.TypeChecker.Normalize.eta_expand_with_type tcenv lbdef lbtyp in
          //eta expansion is important; see issue #490
          extract_typ_abbrev g (right lb.lbname) quals lbdef

        | Sig_let (lbs, _, attrs) ->
          let quals = se.sigquals in
          let elet = mk (Tm_let(lbs, FStar.Syntax.Const.exp_false_bool)) None se.sigrng in
          let ml_let, _, _ = Term.term_as_mlexpr g elet in
          begin match ml_let.expr with
            | MLE_Let((flavor, _, bindings), _) ->
              let g, ml_lbs' = List.fold_left2 (fun (env, ml_lbs) (ml_lb:mllb) {lbname=lbname; lbtyp=t} ->
//              debug g (fun () -> printfn "Translating source lb %s at type %s to %A" (Print.lbname_to_string lbname) (Print.typ_to_string t) (must (mllb.mllb_tysc)));
                  let lb_lid = (right lbname).fv_name.v in
                  let g, ml_lb =
                    if quals |> BU.for_some (function Projector _ -> true | _ -> false) //projector names have to mangled
                    then let mname = mangle_projector_lid lb_lid |> mlpath_of_lident in
                         let env, _ = UEnv.extend_fv' env (right lbname) mname (must ml_lb.mllb_tysc) ml_lb.mllb_add_unit false in
                         env, {ml_lb with mllb_name=(snd mname,0)}
                    else fst <| UEnv.extend_lb env lbname t (must ml_lb.mllb_tysc) ml_lb.mllb_add_unit false, ml_lb in
                 g, ml_lb::ml_lbs)
              (g, []) bindings (snd lbs) in
              let flags = List.choose (function
                | Assumption -> Some Assumed
                | S.Private -> Some Private
                | S.NoExtract -> Some NoExtract
                | _ -> None
              ) quals in
              let flags' = List.choose (function
                | { n = Tm_constant (Const_string (data, _)) } ->
                    Some (Attribute (string_of_unicode data))
                | _ ->
                    print_warning "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                    None
              ) attrs in
              g, [MLM_Loc (Util.mlloc_of_range se.sigrng); MLM_Let (flavor, flags @ flags', List.rev ml_lbs')]

            | _ ->
              failwith (BU.format1 "Impossible: Translated a let to a non-let: %s" (Code.string_of_mlexpr g.currentModule ml_let))
          end

       | Sig_declare_typ(lid, _, t) ->
         let quals = se.sigquals in
         if quals |> List.contains Assumption
         then let always_fail =
                  let imp = match U.arrow_formals t with
                    | [], t ->
                      // Avoid top-level failwith statements
                      let b = mk_binder <| (gen_bv "_" None t) in
                      U.abs [b] (fail_exp lid t) None
                    | bs, t ->
                      U.abs bs (fail_exp lid t) None in
                  { se with sigel = Sig_let((false, [{lbname=Inr (S.lid_as_fv lid Delta_constant None);
                                                      lbunivs=[];
                                                      lbtyp=t;
                                                      lbeff=FStar.Syntax.Const.effect_ML_lid;
                                                      lbdef=imp}]), [], []) } in
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

       | Sig_main(e) ->
         let ml_main, _, _ = Term.term_as_mlexpr g e in
         g, [MLM_Loc (Util.mlloc_of_range se.sigrng); MLM_Top ml_main]

       | Sig_new_effect_for_free _ ->
           failwith "impossible -- removed by tc.fs"

       | Sig_assume _ //not needed; purely logical
       | Sig_sub_effect  _
       | Sig_effect_abbrev _ -> //effects are all primitive; so these are not extracted; this may change as we add user-defined non-primitive effects
         g, []
       | Sig_pragma (p) ->
         if p = S.LightOff
         then Options.set_ml_ish();
         g, []

let extract_iface (g:env) (m:modul) =  BU.fold_map extract_sig g m.declarations |> fst

let extract (g:env) (m:modul) : env * list<mllib> =
  S.reset_gensym();
  if Options.debug_any ()
  then BU.print1 "Extracting module %s\n" (Print.lid_to_string m.name);
  let _ = Options.restore_cmd_line_options true in
  let name = MLS.mlpath_of_lident m.name in
  let g = {g with currentModule = name}  in
  let g, sigs = BU.fold_map extract_sig g m.declarations in
  let mlm : mlmodule = List.flatten sigs in
  let is_kremlin = match Options.codegen () with | Some "Kremlin" -> true | _ -> false in
  if m.name.str <> "Prims"
  && (is_kremlin || not m.is_interface)
  && Options.should_extract m.name.str then begin
    BU.print1 "Extracted module %s\n" (Print.lid_to_string m.name);
    g, [MLLib ([name, Some ([], mlm), (MLLib [])])]
  end else begin
    g, []
  end
