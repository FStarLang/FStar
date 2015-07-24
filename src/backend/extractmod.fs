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
module Microsoft.FStar.Backends.ML.ExtractMod
open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.ML.Syntax
open Microsoft.FStar.Backends.ML.Env
open Microsoft.FStar.Backends.ML.Util

(*This approach assumes that failwith already exists in scope. This might be problematic, see below.*)
let fail_exp = mk_Exp_app(Util.fvar false Const.failwith_lid dummyRange, [varg <| mk_Exp_constant (Const_string (Bytes.string_as_unicode_bytes "Not yet implemented", dummyRange)) None dummyRange]) None dummyRange 

    
let rec extract_sig (g:env) (se:sigelt) : env * list<mlmodule1> = 
    //printfn "(* now extracting :  %A *) \n" (Print.sigelt_to_string_short se);
     match se with
        | Sig_datacon _
        | Sig_bundle _
        | Sig_tycon _
        | Sig_typ_abbrev _ -> 
            let c, tds = ExtractTyp.extractSigElt g se in
            c, [MLM_Ty tds]

        | Sig_let (lbs, r, _, _) -> 
          let elet = mk_Exp_let(lbs, Const.exp_false_bool) None r in
          let ml_let, _, _ = ExtractExp.synth_exp g elet in
          begin match ml_let with 
            | MLE_Let(ml_lbs, _) -> 
              let g = List.fold_left2 (fun env (id, poly_t, _, _) {lbname=lbname; lbtyp=t} -> fst <| Env.extend_lb env lbname t (must poly_t))
                      g (snd ml_lbs) (snd lbs) in 
              g, [MLM_Let ml_lbs]
            | _ -> //printfn "%A\n" ml_let; 
                failwith "impossible"
          end

       | Sig_val_decl(lid, t, quals, r) -> 
         if quals |> List.contains Assumption 
         then let tbinders,_ = Util.tbinder_prefix t in
              let impl = match tbinders with
                | [] -> fail_exp
                | bs -> mk_Exp_abs(bs, fail_exp) None dummyRange in
              let se = Sig_let((false, [{lbname=Inr lid; lbtyp=t; lbeff=Const.effect_Tot_lid; lbdef=impl}]), r, [], quals) in
              let g, mlm = extract_sig g se in
              if quals |> Util.for_some (function Projector _ | Discriminator _ -> true | _ -> false)
              then g, [] //TODO: generate a proper projector/discriminator
              else g, mlm
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

let extract_prims (g:env) (m:modul) =  Util.fold_map extract_sig g m.declarations |> fst
    
let rec extract (g:env) (m:modul) : env * mllib = 
    let name = Backends.ML.Syntax.mlpath_of_lident m.name in
    let g = {g with currentModule = name}  in
    if m.is_interface then failwith "NYI";
    if m.name.str = "Prims"
    then let g = extract_prims g m in 
         g, MLLib(["Prims", None, MLLib []])
    else let g, sigs = Util.fold_map extract_sig g m.declarations in
         let mlm : mlmodule = List.flatten sigs in
         g, MLLib ([m.name.str, Some ([], mlm), (MLLib [])])
    
