open Prims
let (disentangle_abbrevs_from_bundle :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lident Prims.list ->
        FStar_Compiler_Range_Type.range ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun sigelts ->
    fun quals ->
      fun members ->
        fun rng ->
          let sigattrs =
            FStar_Compiler_List.collect
              (fun s ->
                 match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu___ ->
                     s.FStar_Syntax_Syntax.sigattrs
                 | FStar_Syntax_Syntax.Sig_let uu___ ->
                     s.FStar_Syntax_Syntax.sigattrs
                 | uu___ -> []) sigelts in
          let sigattrs1 = FStar_Syntax_Util.deduplicate_terms sigattrs in
          let type_abbrev_sigelts =
            FStar_Compiler_List.collect
              (fun x ->
                 match x.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_let
                     {
                       FStar_Syntax_Syntax.lbs1 =
                         (false,
                          {
                            FStar_Syntax_Syntax.lbname = FStar_Pervasives.Inr
                              uu___;
                            FStar_Syntax_Syntax.lbunivs = uu___1;
                            FStar_Syntax_Syntax.lbtyp = uu___2;
                            FStar_Syntax_Syntax.lbeff = uu___3;
                            FStar_Syntax_Syntax.lbdef = uu___4;
                            FStar_Syntax_Syntax.lbattrs = uu___5;
                            FStar_Syntax_Syntax.lbpos = uu___6;_}::[]);
                       FStar_Syntax_Syntax.lids1 = uu___7;_}
                     -> [x]
                 | FStar_Syntax_Syntax.Sig_let uu___ ->
                     failwith
                       "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                 | uu___ -> []) sigelts in
          match type_abbrev_sigelts with
          | [] ->
              ({
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      {
                        FStar_Syntax_Syntax.ses = sigelts;
                        FStar_Syntax_Syntax.lids = members
                      });
                 FStar_Syntax_Syntax.sigrng = rng;
                 FStar_Syntax_Syntax.sigquals = quals;
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = sigattrs1;
                 FStar_Syntax_Syntax.sigopens_and_abbrevs = [];
                 FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
               }, [])
          | uu___ ->
              let type_abbrevs =
                FStar_Compiler_List.map
                  (fun x ->
                     match x.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_let
                         {
                           FStar_Syntax_Syntax.lbs1 =
                             (uu___1,
                              {
                                FStar_Syntax_Syntax.lbname =
                                  FStar_Pervasives.Inr fv;
                                FStar_Syntax_Syntax.lbunivs = uu___2;
                                FStar_Syntax_Syntax.lbtyp = uu___3;
                                FStar_Syntax_Syntax.lbeff = uu___4;
                                FStar_Syntax_Syntax.lbdef = uu___5;
                                FStar_Syntax_Syntax.lbattrs = uu___6;
                                FStar_Syntax_Syntax.lbpos = uu___7;_}::[]);
                           FStar_Syntax_Syntax.lids1 = uu___8;_}
                         ->
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     | uu___1 ->
                         failwith
                           "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible")
                  type_abbrev_sigelts in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Compiler_Util.mk_ref [] in
                let in_progress = FStar_Compiler_Util.mk_ref [] in
                let not_unfolded_yet =
                  FStar_Compiler_Util.mk_ref type_abbrev_sigelts in
                let remove_not_unfolded lid =
                  let uu___1 =
                    let uu___2 =
                      FStar_Compiler_Effect.op_Bang not_unfolded_yet in
                    FStar_Compiler_List.filter
                      (fun x ->
                         match x.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_let
                             {
                               FStar_Syntax_Syntax.lbs1 =
                                 (uu___3,
                                  {
                                    FStar_Syntax_Syntax.lbname =
                                      FStar_Pervasives.Inr fv;
                                    FStar_Syntax_Syntax.lbunivs = uu___4;
                                    FStar_Syntax_Syntax.lbtyp = uu___5;
                                    FStar_Syntax_Syntax.lbeff = uu___6;
                                    FStar_Syntax_Syntax.lbdef = uu___7;
                                    FStar_Syntax_Syntax.lbattrs = uu___8;
                                    FStar_Syntax_Syntax.lbpos = uu___9;_}::[]);
                               FStar_Syntax_Syntax.lids1 = uu___10;_}
                             ->
                             let uu___11 =
                               FStar_Ident.lid_equals lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             Prims.op_Negation uu___11
                         | uu___3 -> true) uu___2 in
                  FStar_Compiler_Effect.op_Colon_Equals not_unfolded_yet
                    uu___1 in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        {
                          FStar_Syntax_Syntax.lbs1 =
                            (uu___1,
                             {
                               FStar_Syntax_Syntax.lbname =
                                 FStar_Pervasives.Inr fv';
                               FStar_Syntax_Syntax.lbunivs = uu___2;
                               FStar_Syntax_Syntax.lbtyp = uu___3;
                               FStar_Syntax_Syntax.lbeff = uu___4;
                               FStar_Syntax_Syntax.lbdef = uu___5;
                               FStar_Syntax_Syntax.lbattrs = uu___6;
                               FStar_Syntax_Syntax.lbpos = uu___7;_}::[]);
                          FStar_Syntax_Syntax.lids1 = uu___8;_}
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu___1 -> FStar_Pervasives_Native.None in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            {
                              FStar_Syntax_Syntax.lbs1 =
                                (uu___1,
                                 { FStar_Syntax_Syntax.lbname = uu___2;
                                   FStar_Syntax_Syntax.lbunivs = uu___3;
                                   FStar_Syntax_Syntax.lbtyp = uu___4;
                                   FStar_Syntax_Syntax.lbeff = uu___5;
                                   FStar_Syntax_Syntax.lbdef = tm;
                                   FStar_Syntax_Syntax.lbattrs = uu___6;
                                   FStar_Syntax_Syntax.lbpos = uu___7;_}::[]);
                              FStar_Syntax_Syntax.lids1 = uu___8;_};
                          FStar_Syntax_Syntax.sigrng = uu___9;
                          FStar_Syntax_Syntax.sigquals = uu___10;
                          FStar_Syntax_Syntax.sigmeta = uu___11;
                          FStar_Syntax_Syntax.sigattrs = uu___12;
                          FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___13;
                          FStar_Syntax_Syntax.sigopts = uu___14;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu___1 -> FStar_Pervasives_Native.None in
                  let uu___1 =
                    let uu___2 =
                      FStar_Compiler_Effect.op_Bang rev_unfolded_type_abbrevs in
                    FStar_Compiler_Util.find_map uu___2 replacee_term in
                  match uu___1 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None ->
                      let uu___2 =
                        FStar_Compiler_Util.find_map type_abbrev_sigelts
                          replacee in
                      (match uu___2 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu___3 =
                             let uu___4 =
                               FStar_Compiler_Effect.op_Bang in_progress in
                             FStar_Compiler_List.existsb
                               (fun x ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu___4 in
                           if uu___3
                           then
                             let msg =
                               let uu___4 =
                                 FStar_Ident.string_of_lid
                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               FStar_Compiler_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 uu___4 in
                             FStar_Errors.raise_error
                               FStar_Ident.hasrange_lident
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               FStar_Errors_Codes.Fatal_CycleInRecTypeAbbreviation
                               ()
                               (Obj.magic
                                  FStar_Errors_Msg.is_error_message_string)
                               (Obj.magic msg)
                           else unfold_abbrev se
                       | uu___3 -> t)
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let
                      { FStar_Syntax_Syntax.lbs1 = (false, lb::[]);
                        FStar_Syntax_Syntax.lids1 = uu___1;_}
                      ->
                      let quals1 =
                        FStar_Compiler_List.filter
                          (fun uu___2 ->
                             match uu___2 with
                             | FStar_Syntax_Syntax.Noeq -> false
                             | uu___3 -> true) x.FStar_Syntax_Syntax.sigquals in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Pervasives.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu___2 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible" in
                      ((let uu___3 =
                          let uu___4 =
                            FStar_Compiler_Effect.op_Bang in_progress in
                          lid :: uu___4 in
                        FStar_Compiler_Effect.op_Colon_Equals in_progress
                          uu___3);
                       (match () with
                        | () ->
                            (remove_not_unfolded lid;
                             (match () with
                              | () ->
                                  let ty' =
                                    FStar_Syntax_InstFV.inst unfold_abbrev_fv
                                      lb.FStar_Syntax_Syntax.lbtyp in
                                  let tm' =
                                    FStar_Syntax_InstFV.inst unfold_abbrev_fv
                                      lb.FStar_Syntax_Syntax.lbdef in
                                  let lb' =
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (lb.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (lb.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (lb.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm';
                                      FStar_Syntax_Syntax.lbattrs =
                                        (lb.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (lb.FStar_Syntax_Syntax.lbpos)
                                    } in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      {
                                        FStar_Syntax_Syntax.lbs1 =
                                          (false, [lb']);
                                        FStar_Syntax_Syntax.lids1 = [lid]
                                      } in
                                  ((let uu___5 =
                                      let uu___6 =
                                        FStar_Compiler_Effect.op_Bang
                                          rev_unfolded_type_abbrevs in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigelt';
                                        FStar_Syntax_Syntax.sigrng =
                                          (x.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          (x.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (x.FStar_Syntax_Syntax.sigattrs);
                                        FStar_Syntax_Syntax.sigopens_and_abbrevs
                                          =
                                          (x.FStar_Syntax_Syntax.sigopens_and_abbrevs);
                                        FStar_Syntax_Syntax.sigopts =
                                          (x.FStar_Syntax_Syntax.sigopts)
                                      } :: uu___6 in
                                    FStar_Compiler_Effect.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu___5);
                                   (match () with
                                    | () ->
                                        ((let uu___6 =
                                            let uu___7 =
                                              FStar_Compiler_Effect.op_Bang
                                                in_progress in
                                            FStar_Compiler_List.tl uu___7 in
                                          FStar_Compiler_Effect.op_Colon_Equals
                                            in_progress uu___6);
                                         (match () with | () -> tm'))))))))
                  | uu___1 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible" in
                let rec aux uu___1 =
                  let uu___2 = FStar_Compiler_Effect.op_Bang not_unfolded_yet in
                  match uu___2 with
                  | x::uu___3 -> let _unused = unfold_abbrev x in aux ()
                  | uu___3 ->
                      let uu___4 =
                        FStar_Compiler_Effect.op_Bang
                          rev_unfolded_type_abbrevs in
                      FStar_Compiler_List.rev uu___4 in
                aux () in
              let filter_out_type_abbrevs l =
                FStar_Compiler_List.filter
                  (fun lid ->
                     FStar_Compiler_List.for_all
                       (fun lid' ->
                          let uu___1 = FStar_Ident.lid_equals lid lid' in
                          Prims.op_Negation uu___1) type_abbrevs) l in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Compiler_Util.find_map unfolded_type_abbrevs
                    (fun x ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           {
                             FStar_Syntax_Syntax.lbs1 =
                               (uu___1,
                                {
                                  FStar_Syntax_Syntax.lbname =
                                    FStar_Pervasives.Inr fv';
                                  FStar_Syntax_Syntax.lbunivs = uu___2;
                                  FStar_Syntax_Syntax.lbtyp = uu___3;
                                  FStar_Syntax_Syntax.lbeff = uu___4;
                                  FStar_Syntax_Syntax.lbdef = tm;
                                  FStar_Syntax_Syntax.lbattrs = uu___5;
                                  FStar_Syntax_Syntax.lbpos = uu___6;_}::[]);
                             FStar_Syntax_Syntax.lids1 = uu___7;_}
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu___1 -> FStar_Pervasives_Native.None) in
                let unfold_fv t fv =
                  let uu___1 = find_in_unfolded fv in
                  match uu___1 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu___2 -> t in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      { FStar_Syntax_Syntax.lid = lid;
                        FStar_Syntax_Syntax.us = univs;
                        FStar_Syntax_Syntax.params = bnd;
                        FStar_Syntax_Syntax.num_uniform_params = num_uniform;
                        FStar_Syntax_Syntax.t = ty;
                        FStar_Syntax_Syntax.mutuals = mut;
                        FStar_Syntax_Syntax.ds = dc;
                        FStar_Syntax_Syntax.injective_type_params =
                          injective_type_params;_}
                      ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [{
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_inductive_typ
                              {
                                FStar_Syntax_Syntax.lid = lid;
                                FStar_Syntax_Syntax.us = univs;
                                FStar_Syntax_Syntax.params = bnd';
                                FStar_Syntax_Syntax.num_uniform_params =
                                  num_uniform;
                                FStar_Syntax_Syntax.t = ty';
                                FStar_Syntax_Syntax.mutuals = mut';
                                FStar_Syntax_Syntax.ds = dc;
                                FStar_Syntax_Syntax.injective_type_params =
                                  injective_type_params
                              });
                         FStar_Syntax_Syntax.sigrng =
                           (x.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (x.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (x.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (x.FStar_Syntax_Syntax.sigattrs);
                         FStar_Syntax_Syntax.sigopens_and_abbrevs =
                           (x.FStar_Syntax_Syntax.sigopens_and_abbrevs);
                         FStar_Syntax_Syntax.sigopts =
                           (x.FStar_Syntax_Syntax.sigopts)
                       }]
                  | FStar_Syntax_Syntax.Sig_datacon
                      { FStar_Syntax_Syntax.lid1 = lid;
                        FStar_Syntax_Syntax.us1 = univs;
                        FStar_Syntax_Syntax.t1 = ty;
                        FStar_Syntax_Syntax.ty_lid = res;
                        FStar_Syntax_Syntax.num_ty_params = npars;
                        FStar_Syntax_Syntax.mutuals1 = mut;
                        FStar_Syntax_Syntax.injective_type_params1 =
                          injective_type_params;_}
                      ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [{
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_datacon
                              {
                                FStar_Syntax_Syntax.lid1 = lid;
                                FStar_Syntax_Syntax.us1 = univs;
                                FStar_Syntax_Syntax.t1 = ty';
                                FStar_Syntax_Syntax.ty_lid = res;
                                FStar_Syntax_Syntax.num_ty_params = npars;
                                FStar_Syntax_Syntax.mutuals1 = mut';
                                FStar_Syntax_Syntax.injective_type_params1 =
                                  injective_type_params
                              });
                         FStar_Syntax_Syntax.sigrng =
                           (x.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (x.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (x.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (x.FStar_Syntax_Syntax.sigattrs);
                         FStar_Syntax_Syntax.sigopens_and_abbrevs =
                           (x.FStar_Syntax_Syntax.sigopens_and_abbrevs);
                         FStar_Syntax_Syntax.sigopts =
                           (x.FStar_Syntax_Syntax.sigopts)
                       }]
                  | FStar_Syntax_Syntax.Sig_let uu___1 -> []
                  | uu___1 ->
                      failwith
                        "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible" in
                FStar_Compiler_List.collect unfold_in_sig sigelts in
              let new_members = filter_out_type_abbrevs members in
              let new_bundle =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_bundle
                       {
                         FStar_Syntax_Syntax.ses =
                           inductives_with_abbrevs_unfolded;
                         FStar_Syntax_Syntax.lids = new_members
                       });
                  FStar_Syntax_Syntax.sigrng = rng;
                  FStar_Syntax_Syntax.sigquals = quals;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = sigattrs1;
                  FStar_Syntax_Syntax.sigopens_and_abbrevs = [];
                  FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                } in
              (new_bundle, unfolded_type_abbrevs)