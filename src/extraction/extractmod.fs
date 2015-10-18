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
module FStar.Extraction.ML.ExtractMod
open FStar
open FStar.Util
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Extraction.ML.Syntax
open FStar.Extraction.ML.Env
open FStar.Extraction.ML.Util

(*This approach assumes that failwith already exists in scope. This might be problematic, see below.*)
let fail_exp (lid:lident) (t:typ) = mk_Exp_app(Util.fvar None Const.failwith_lid dummyRange,
                          [ targ t
                          ; varg <| mk_Exp_constant (Const_string (Bytes.string_as_unicode_bytes ("Not yet implemented:"^(Print.sli lid)), dummyRange)) None dummyRange]) None dummyRange

let mangle_projector_lid (x: lident) : lident =
    let projecteeName = x.ident in
    let prefix, constrName = Util.prefix x.ns in
    let mangledName = Syntax.id_of_text ("___"^constrName.idText^"___"^projecteeName.idText) in
    lid_of_ids (prefix@[mangledName])

let rec extract_sig (g:env) (se:sigelt) : env * list<mlmodule1> =
   (debug g (fun u -> Util.print_string (Util.format1 "now extracting :  %s \n" (Print.sigelt_to_string se))));
     match se with
        | Sig_datacon _
        | Sig_bundle _
        | Sig_tycon _
        | Sig_typ_abbrev _ ->
            let c, tds = ExtractTyp.extractSigElt g se in
            c, tds

        | Sig_let (lbs, r, _, quals) ->
          let elet = mk_Exp_let(lbs, Const.exp_false_bool) None r in
          let ml_let, _, _ = ExtractExp.synth_exp g elet in
          begin match ml_let.expr with
            | MLE_Let(ml_lbs, _) ->
              let g, ml_lbs' = List.fold_left2 (fun (env, ml_lbs) (ml_lb:mllb) {lbname=lbname; lbtyp=t} ->
//              debug g (fun () -> printfn "Translating source lb %s at type %s to %A" (Print.lbname_to_string lbname) (Print.typ_to_string t) (must (mllb.mllb_tysc)));
                  let g, ml_lb =
                    if quals |> Util.for_some (function Projector _ -> true | _ -> false) //projector names have to mangled
                    then let mname = mangle_projector_lid (right lbname) |> mlpath_of_lident in
                         let env = Env.extend_fv' env (Util.fv <| right lbname) mname ml_lb.mllb_tysc ml_lb.mllb_add_unit in
                         env, {ml_lb with mllb_name=(snd mname, 0)}
                    else fst <| Env.extend_lb env lbname t ml_lb.mllb_tysc ml_lb.mllb_add_unit, ml_lb in
                 g, ml_lb::ml_lbs)
              (g, []) (snd ml_lbs) (snd lbs) in
              g, [MLM_Let (fst ml_lbs, List.rev ml_lbs')]

            | _ -> //printfn "%A\n" ml_let;
                failwith "impossible"
          end

       | Sig_val_decl(lid, t, quals, r) ->
         if quals |> List.contains Assumption
         //&& not (quals |> Util.for_some (function Projector _ -> true | _ -> false))
         then let impl = match Util.function_formals t with
                | Some (bs, c) -> mk_Exp_abs(bs, fail_exp lid (Util.comp_result c)) None dummyRange
                | _ -> fail_exp lid t in
              let se = Sig_let((false, [{lbname=Inr lid; lbtyp=t; lbeff=Const.effect_ML_lid; lbdef=impl}]), r, [], quals) in
              let g, mlm = extract_sig g se in
              let is_record = Util.for_some (function RecordType _ -> true | _ -> false) quals in
              match Util.find_map quals (function Discriminator l -> Some l |  _ -> None) with
                  | Some l when (not is_record) -> g, [ExtractExp.ind_discriminator_body g lid l] //records are single constructor types; there should be no discriminators for them
                  | _ ->
                    begin match Util.find_map quals (function  Projector (l,_)  -> Some l |  _ -> None) with
                        | Some _ -> g, [] //records are extracted as ML records; no projectors for them
                        | _ -> g, mlm
                    end
         else g, []

       | Sig_main(e, _) ->
         let ml_main, _, _ = ExtractExp.synth_exp g e in
         g, [MLM_Top ml_main]


       | Sig_kind_abbrev _ //not needed; we expand kind abbreviations while translating types
       | Sig_assume _ //not needed; purely logical

       | Sig_new_effect _
       | Sig_sub_effect  _
       | Sig_effect_abbrev _  //effects are all primitive; so these are not extracted; this may change as we add user-defined non-primitive effects
       | Sig_pragma _ -> //pragmas are currently not relevant for codegen; they may be in the future
         g, []

let extract_iface (g:env) (m:modul) =  Util.fold_map extract_sig g m.declarations |> fst

let rec extract (g:env) (m:modul) : env * list<mllib> =
    Util.reset_gensym();
    let name = Extraction.ML.Syntax.mlpath_of_lident m.name in
    let g = {g with currentModule = name}  in
    if m.name.str = "Prims" 
    || m.is_interface
    || List.contains m.name.str !Options.admit_fsi
    then let g = extract_iface g m in
         g, [] //MLLib([Util.flatten_mlpath name, None, MLLib []])
    else let g, sigs = Util.fold_map extract_sig g m.declarations in
         let mlm : mlmodule = List.flatten sigs in
         g, [MLLib ([Util.flatten_mlpath name, Some ([], mlm), (MLLib [])])]

