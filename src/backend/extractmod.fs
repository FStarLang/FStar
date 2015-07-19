#light "off"
module Microsoft.FStar.Backends.ML.ExtractMod
open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.ML.Syntax
open Microsoft.FStar.Backends.ML.Env
open Microsoft.FStar.Backends.ML.Util

let extract (g:env) (m:modul) : env * mllib = 
    if m.is_interface then failwith "NYI";
    let g, sigs = Util.fold_map (fun g se -> match se with
        | Sig_bundle _
        | Sig_tycon _
        | Sig_typ_abbrev _ -> 
            let c, tds = ExtractTyp.extractSigElt g se in
            c, List.map MLM_Ty tds

        | Sig_let (lbs, r, _, _) -> 
          let elet = mk_Exp_let(lbs, Const.exp_false_bool) None r in
          let ml_let, _, _ = ExtractExp.synth_exp' g elet in
          begin match ml_let with 
            | MLE_Let(lbs, _) -> g, [MLM_Let lbs]
            | _ -> //printfn "%A\n" ml_let; 
                failwith "impossible"
          end

        | _ -> g, []
        | se -> failwith (Util.format1 "NYI: %s\n" (Print.sigelt_to_string_short se))) g m.declarations in
    let mlm : mlmodule = List.flatten sigs in
    g, MLLib ([m.name.str, Some ([], mlm), (MLLib [])])
    
