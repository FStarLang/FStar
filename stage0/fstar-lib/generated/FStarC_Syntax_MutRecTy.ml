open Prims
let (disentangle_abbrevs_from_bundle :
  FStarC_Syntax_Syntax.sigelt Prims.list ->
    FStarC_Syntax_Syntax.qualifier Prims.list ->
      FStarC_Ident.lident Prims.list ->
        FStarC_Compiler_Range_Type.range ->
          (FStarC_Syntax_Syntax.sigelt * FStarC_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun sigelts ->
    fun quals ->
      fun members ->
        fun rng ->
          let sigattrs =
            FStarC_Compiler_List.collect
              (fun s ->
                 match s.FStarC_Syntax_Syntax.sigel with
                 | FStarC_Syntax_Syntax.Sig_inductive_typ uu___ ->
                     s.FStarC_Syntax_Syntax.sigattrs
                 | FStarC_Syntax_Syntax.Sig_let uu___ ->
                     s.FStarC_Syntax_Syntax.sigattrs
                 | uu___ -> []) sigelts in
          let sigattrs1 = FStarC_Syntax_Util.deduplicate_terms sigattrs in
          let type_abbrev_sigelts =
            FStarC_Compiler_List.collect
              (fun x ->
                 match x.FStarC_Syntax_Syntax.sigel with
                 | FStarC_Syntax_Syntax.Sig_let
                     {
                       FStarC_Syntax_Syntax.lbs1 =
                         (false,
                          {
                            FStarC_Syntax_Syntax.lbname =
                              FStar_Pervasives.Inr uu___;
                            FStarC_Syntax_Syntax.lbunivs = uu___1;
                            FStarC_Syntax_Syntax.lbtyp = uu___2;
                            FStarC_Syntax_Syntax.lbeff = uu___3;
                            FStarC_Syntax_Syntax.lbdef = uu___4;
                            FStarC_Syntax_Syntax.lbattrs = uu___5;
                            FStarC_Syntax_Syntax.lbpos = uu___6;_}::[]);
                       FStarC_Syntax_Syntax.lids1 = uu___7;_}
                     -> [x]
                 | FStarC_Syntax_Syntax.Sig_let uu___ ->
                     failwith
                       "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                 | uu___ -> []) sigelts in
          match type_abbrev_sigelts with
          | [] ->
              ({
                 FStarC_Syntax_Syntax.sigel =
                   (FStarC_Syntax_Syntax.Sig_bundle
                      {
                        FStarC_Syntax_Syntax.ses = sigelts;
                        FStarC_Syntax_Syntax.lids = members
                      });
                 FStarC_Syntax_Syntax.sigrng = rng;
                 FStarC_Syntax_Syntax.sigquals = quals;
                 FStarC_Syntax_Syntax.sigmeta =
                   FStarC_Syntax_Syntax.default_sigmeta;
                 FStarC_Syntax_Syntax.sigattrs = sigattrs1;
                 FStarC_Syntax_Syntax.sigopens_and_abbrevs = [];
                 FStarC_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
               }, [])
          | uu___ ->
              let type_abbrevs =
                FStarC_Compiler_List.map
                  (fun x ->
                     match x.FStarC_Syntax_Syntax.sigel with
                     | FStarC_Syntax_Syntax.Sig_let
                         {
                           FStarC_Syntax_Syntax.lbs1 =
                             (uu___1,
                              {
                                FStarC_Syntax_Syntax.lbname =
                                  FStar_Pervasives.Inr fv;
                                FStarC_Syntax_Syntax.lbunivs = uu___2;
                                FStarC_Syntax_Syntax.lbtyp = uu___3;
                                FStarC_Syntax_Syntax.lbeff = uu___4;
                                FStarC_Syntax_Syntax.lbdef = uu___5;
                                FStarC_Syntax_Syntax.lbattrs = uu___6;
                                FStarC_Syntax_Syntax.lbpos = uu___7;_}::[]);
                           FStarC_Syntax_Syntax.lids1 = uu___8;_}
                         ->
                         (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                     | uu___1 ->
                         failwith
                           "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible")
                  type_abbrev_sigelts in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs =
                  FStarC_Compiler_Util.mk_ref [] in
                let in_progress = FStarC_Compiler_Util.mk_ref [] in
                let not_unfolded_yet =
                  FStarC_Compiler_Util.mk_ref type_abbrev_sigelts in
                let remove_not_unfolded lid =
                  let uu___1 =
                    let uu___2 =
                      FStarC_Compiler_Effect.op_Bang not_unfolded_yet in
                    FStarC_Compiler_List.filter
                      (fun x ->
                         match x.FStarC_Syntax_Syntax.sigel with
                         | FStarC_Syntax_Syntax.Sig_let
                             {
                               FStarC_Syntax_Syntax.lbs1 =
                                 (uu___3,
                                  {
                                    FStarC_Syntax_Syntax.lbname =
                                      FStar_Pervasives.Inr fv;
                                    FStarC_Syntax_Syntax.lbunivs = uu___4;
                                    FStarC_Syntax_Syntax.lbtyp = uu___5;
                                    FStarC_Syntax_Syntax.lbeff = uu___6;
                                    FStarC_Syntax_Syntax.lbdef = uu___7;
                                    FStarC_Syntax_Syntax.lbattrs = uu___8;
                                    FStarC_Syntax_Syntax.lbpos = uu___9;_}::[]);
                               FStarC_Syntax_Syntax.lids1 = uu___10;_}
                             ->
                             let uu___11 =
                               FStarC_Ident.lid_equals lid
                                 (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
                             Prims.op_Negation uu___11
                         | uu___3 -> true) uu___2 in
                  FStarC_Compiler_Effect.op_Colon_Equals not_unfolded_yet
                    uu___1 in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStarC_Syntax_Syntax.sigel with
                    | FStarC_Syntax_Syntax.Sig_let
                        {
                          FStarC_Syntax_Syntax.lbs1 =
                            (uu___1,
                             {
                               FStarC_Syntax_Syntax.lbname =
                                 FStar_Pervasives.Inr fv';
                               FStarC_Syntax_Syntax.lbunivs = uu___2;
                               FStarC_Syntax_Syntax.lbtyp = uu___3;
                               FStarC_Syntax_Syntax.lbeff = uu___4;
                               FStarC_Syntax_Syntax.lbdef = uu___5;
                               FStarC_Syntax_Syntax.lbattrs = uu___6;
                               FStarC_Syntax_Syntax.lbpos = uu___7;_}::[]);
                          FStarC_Syntax_Syntax.lids1 = uu___8;_}
                        when
                        FStarC_Ident.lid_equals
                          (fv'.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                          (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu___1 -> FStar_Pervasives_Native.None in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStarC_Syntax_Syntax.sigel =
                            FStarC_Syntax_Syntax.Sig_let
                            {
                              FStarC_Syntax_Syntax.lbs1 =
                                (uu___1,
                                 { FStarC_Syntax_Syntax.lbname = uu___2;
                                   FStarC_Syntax_Syntax.lbunivs = uu___3;
                                   FStarC_Syntax_Syntax.lbtyp = uu___4;
                                   FStarC_Syntax_Syntax.lbeff = uu___5;
                                   FStarC_Syntax_Syntax.lbdef = tm;
                                   FStarC_Syntax_Syntax.lbattrs = uu___6;
                                   FStarC_Syntax_Syntax.lbpos = uu___7;_}::[]);
                              FStarC_Syntax_Syntax.lids1 = uu___8;_};
                          FStarC_Syntax_Syntax.sigrng = uu___9;
                          FStarC_Syntax_Syntax.sigquals = uu___10;
                          FStarC_Syntax_Syntax.sigmeta = uu___11;
                          FStarC_Syntax_Syntax.sigattrs = uu___12;
                          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___13;
                          FStarC_Syntax_Syntax.sigopts = uu___14;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu___1 -> FStar_Pervasives_Native.None in
                  let uu___1 =
                    let uu___2 =
                      FStarC_Compiler_Effect.op_Bang
                        rev_unfolded_type_abbrevs in
                    FStarC_Compiler_Util.find_map uu___2 replacee_term in
                  match uu___1 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None ->
                      let uu___2 =
                        FStarC_Compiler_Util.find_map type_abbrev_sigelts
                          replacee in
                      (match uu___2 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu___3 =
                             let uu___4 =
                               FStarC_Compiler_Effect.op_Bang in_progress in
                             FStarC_Compiler_List.existsb
                               (fun x ->
                                  FStarC_Ident.lid_equals x
                                    (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v)
                               uu___4 in
                           if uu___3
                           then
                             let msg =
                               let uu___4 =
                                 FStarC_Ident.string_of_lid
                                   (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
                               FStarC_Compiler_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 uu___4 in
                             FStarC_Errors.raise_error
                               FStarC_Ident.hasrange_lident
                               (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                               FStarC_Errors_Codes.Fatal_CycleInRecTypeAbbreviation
                               ()
                               (Obj.magic
                                  FStarC_Errors_Msg.is_error_message_string)
                               (Obj.magic msg)
                           else unfold_abbrev se
                       | uu___3 -> t)
                and unfold_abbrev x =
                  match x.FStarC_Syntax_Syntax.sigel with
                  | FStarC_Syntax_Syntax.Sig_let
                      { FStarC_Syntax_Syntax.lbs1 = (false, lb::[]);
                        FStarC_Syntax_Syntax.lids1 = uu___1;_}
                      ->
                      let quals1 =
                        FStarC_Compiler_List.filter
                          (fun uu___2 ->
                             match uu___2 with
                             | FStarC_Syntax_Syntax.Noeq -> false
                             | uu___3 -> true)
                          x.FStarC_Syntax_Syntax.sigquals in
                      let lid =
                        match lb.FStarC_Syntax_Syntax.lbname with
                        | FStar_Pervasives.Inr fv ->
                            (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                        | uu___2 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible" in
                      ((let uu___3 =
                          let uu___4 =
                            FStarC_Compiler_Effect.op_Bang in_progress in
                          lid :: uu___4 in
                        FStarC_Compiler_Effect.op_Colon_Equals in_progress
                          uu___3);
                       (match () with
                        | () ->
                            (remove_not_unfolded lid;
                             (match () with
                              | () ->
                                  let ty' =
                                    FStarC_Syntax_InstFV.inst
                                      unfold_abbrev_fv
                                      lb.FStarC_Syntax_Syntax.lbtyp in
                                  let tm' =
                                    FStarC_Syntax_InstFV.inst
                                      unfold_abbrev_fv
                                      lb.FStarC_Syntax_Syntax.lbdef in
                                  let lb' =
                                    {
                                      FStarC_Syntax_Syntax.lbname =
                                        (lb.FStarC_Syntax_Syntax.lbname);
                                      FStarC_Syntax_Syntax.lbunivs =
                                        (lb.FStarC_Syntax_Syntax.lbunivs);
                                      FStarC_Syntax_Syntax.lbtyp = ty';
                                      FStarC_Syntax_Syntax.lbeff =
                                        (lb.FStarC_Syntax_Syntax.lbeff);
                                      FStarC_Syntax_Syntax.lbdef = tm';
                                      FStarC_Syntax_Syntax.lbattrs =
                                        (lb.FStarC_Syntax_Syntax.lbattrs);
                                      FStarC_Syntax_Syntax.lbpos =
                                        (lb.FStarC_Syntax_Syntax.lbpos)
                                    } in
                                  let sigelt' =
                                    FStarC_Syntax_Syntax.Sig_let
                                      {
                                        FStarC_Syntax_Syntax.lbs1 =
                                          (false, [lb']);
                                        FStarC_Syntax_Syntax.lids1 = [lid]
                                      } in
                                  ((let uu___5 =
                                      let uu___6 =
                                        FStarC_Compiler_Effect.op_Bang
                                          rev_unfolded_type_abbrevs in
                                      {
                                        FStarC_Syntax_Syntax.sigel = sigelt';
                                        FStarC_Syntax_Syntax.sigrng =
                                          (x.FStarC_Syntax_Syntax.sigrng);
                                        FStarC_Syntax_Syntax.sigquals =
                                          quals1;
                                        FStarC_Syntax_Syntax.sigmeta =
                                          (x.FStarC_Syntax_Syntax.sigmeta);
                                        FStarC_Syntax_Syntax.sigattrs =
                                          (x.FStarC_Syntax_Syntax.sigattrs);
                                        FStarC_Syntax_Syntax.sigopens_and_abbrevs
                                          =
                                          (x.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                        FStarC_Syntax_Syntax.sigopts =
                                          (x.FStarC_Syntax_Syntax.sigopts)
                                      } :: uu___6 in
                                    FStarC_Compiler_Effect.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu___5);
                                   (match () with
                                    | () ->
                                        ((let uu___6 =
                                            let uu___7 =
                                              FStarC_Compiler_Effect.op_Bang
                                                in_progress in
                                            FStarC_Compiler_List.tl uu___7 in
                                          FStarC_Compiler_Effect.op_Colon_Equals
                                            in_progress uu___6);
                                         (match () with | () -> tm'))))))))
                  | uu___1 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible" in
                let rec aux uu___1 =
                  let uu___2 =
                    FStarC_Compiler_Effect.op_Bang not_unfolded_yet in
                  match uu___2 with
                  | x::uu___3 -> let _unused = unfold_abbrev x in aux ()
                  | uu___3 ->
                      let uu___4 =
                        FStarC_Compiler_Effect.op_Bang
                          rev_unfolded_type_abbrevs in
                      FStarC_Compiler_List.rev uu___4 in
                aux () in
              let filter_out_type_abbrevs l =
                FStarC_Compiler_List.filter
                  (fun lid ->
                     FStarC_Compiler_List.for_all
                       (fun lid' ->
                          let uu___1 = FStarC_Ident.lid_equals lid lid' in
                          Prims.op_Negation uu___1) type_abbrevs) l in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStarC_Compiler_Util.find_map unfolded_type_abbrevs
                    (fun x ->
                       match x.FStarC_Syntax_Syntax.sigel with
                       | FStarC_Syntax_Syntax.Sig_let
                           {
                             FStarC_Syntax_Syntax.lbs1 =
                               (uu___1,
                                {
                                  FStarC_Syntax_Syntax.lbname =
                                    FStar_Pervasives.Inr fv';
                                  FStarC_Syntax_Syntax.lbunivs = uu___2;
                                  FStarC_Syntax_Syntax.lbtyp = uu___3;
                                  FStarC_Syntax_Syntax.lbeff = uu___4;
                                  FStarC_Syntax_Syntax.lbdef = tm;
                                  FStarC_Syntax_Syntax.lbattrs = uu___5;
                                  FStarC_Syntax_Syntax.lbpos = uu___6;_}::[]);
                             FStarC_Syntax_Syntax.lids1 = uu___7;_}
                           when
                           FStarC_Ident.lid_equals
                             (fv'.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                             (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu___1 -> FStar_Pervasives_Native.None) in
                let unfold_fv t fv =
                  let uu___1 = find_in_unfolded fv in
                  match uu___1 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu___2 -> t in
                let unfold_in_sig x =
                  match x.FStarC_Syntax_Syntax.sigel with
                  | FStarC_Syntax_Syntax.Sig_inductive_typ
                      { FStarC_Syntax_Syntax.lid = lid;
                        FStarC_Syntax_Syntax.us = univs;
                        FStarC_Syntax_Syntax.params = bnd;
                        FStarC_Syntax_Syntax.num_uniform_params = num_uniform;
                        FStarC_Syntax_Syntax.t = ty;
                        FStarC_Syntax_Syntax.mutuals = mut;
                        FStarC_Syntax_Syntax.ds = dc;
                        FStarC_Syntax_Syntax.injective_type_params =
                          injective_type_params;_}
                      ->
                      let bnd' =
                        FStarC_Syntax_InstFV.inst_binders unfold_fv bnd in
                      let ty' = FStarC_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [{
                         FStarC_Syntax_Syntax.sigel =
                           (FStarC_Syntax_Syntax.Sig_inductive_typ
                              {
                                FStarC_Syntax_Syntax.lid = lid;
                                FStarC_Syntax_Syntax.us = univs;
                                FStarC_Syntax_Syntax.params = bnd';
                                FStarC_Syntax_Syntax.num_uniform_params =
                                  num_uniform;
                                FStarC_Syntax_Syntax.t = ty';
                                FStarC_Syntax_Syntax.mutuals = mut';
                                FStarC_Syntax_Syntax.ds = dc;
                                FStarC_Syntax_Syntax.injective_type_params =
                                  injective_type_params
                              });
                         FStarC_Syntax_Syntax.sigrng =
                           (x.FStarC_Syntax_Syntax.sigrng);
                         FStarC_Syntax_Syntax.sigquals =
                           (x.FStarC_Syntax_Syntax.sigquals);
                         FStarC_Syntax_Syntax.sigmeta =
                           (x.FStarC_Syntax_Syntax.sigmeta);
                         FStarC_Syntax_Syntax.sigattrs =
                           (x.FStarC_Syntax_Syntax.sigattrs);
                         FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                           (x.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                         FStarC_Syntax_Syntax.sigopts =
                           (x.FStarC_Syntax_Syntax.sigopts)
                       }]
                  | FStarC_Syntax_Syntax.Sig_datacon
                      { FStarC_Syntax_Syntax.lid1 = lid;
                        FStarC_Syntax_Syntax.us1 = univs;
                        FStarC_Syntax_Syntax.t1 = ty;
                        FStarC_Syntax_Syntax.ty_lid = res;
                        FStarC_Syntax_Syntax.num_ty_params = npars;
                        FStarC_Syntax_Syntax.mutuals1 = mut;
                        FStarC_Syntax_Syntax.injective_type_params1 =
                          injective_type_params;_}
                      ->
                      let ty' = FStarC_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [{
                         FStarC_Syntax_Syntax.sigel =
                           (FStarC_Syntax_Syntax.Sig_datacon
                              {
                                FStarC_Syntax_Syntax.lid1 = lid;
                                FStarC_Syntax_Syntax.us1 = univs;
                                FStarC_Syntax_Syntax.t1 = ty';
                                FStarC_Syntax_Syntax.ty_lid = res;
                                FStarC_Syntax_Syntax.num_ty_params = npars;
                                FStarC_Syntax_Syntax.mutuals1 = mut';
                                FStarC_Syntax_Syntax.injective_type_params1 =
                                  injective_type_params
                              });
                         FStarC_Syntax_Syntax.sigrng =
                           (x.FStarC_Syntax_Syntax.sigrng);
                         FStarC_Syntax_Syntax.sigquals =
                           (x.FStarC_Syntax_Syntax.sigquals);
                         FStarC_Syntax_Syntax.sigmeta =
                           (x.FStarC_Syntax_Syntax.sigmeta);
                         FStarC_Syntax_Syntax.sigattrs =
                           (x.FStarC_Syntax_Syntax.sigattrs);
                         FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                           (x.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                         FStarC_Syntax_Syntax.sigopts =
                           (x.FStarC_Syntax_Syntax.sigopts)
                       }]
                  | FStarC_Syntax_Syntax.Sig_let uu___1 -> []
                  | uu___1 ->
                      failwith
                        "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible" in
                FStarC_Compiler_List.collect unfold_in_sig sigelts in
              let new_members = filter_out_type_abbrevs members in
              let new_bundle =
                {
                  FStarC_Syntax_Syntax.sigel =
                    (FStarC_Syntax_Syntax.Sig_bundle
                       {
                         FStarC_Syntax_Syntax.ses =
                           inductives_with_abbrevs_unfolded;
                         FStarC_Syntax_Syntax.lids = new_members
                       });
                  FStarC_Syntax_Syntax.sigrng = rng;
                  FStarC_Syntax_Syntax.sigquals = quals;
                  FStarC_Syntax_Syntax.sigmeta =
                    FStarC_Syntax_Syntax.default_sigmeta;
                  FStarC_Syntax_Syntax.sigattrs = sigattrs1;
                  FStarC_Syntax_Syntax.sigopens_and_abbrevs = [];
                  FStarC_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                } in
              (new_bundle, unfolded_type_abbrevs)