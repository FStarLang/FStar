open Prims
let (disentangle_abbrevs_from_bundle :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lident Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun sigelts ->
    fun quals ->
      fun members ->
        fun rng ->
          let sigattrs =
            FStar_List.collect (fun s -> s.FStar_Syntax_Syntax.sigattrs)
              sigelts in
          let type_abbrev_sigelts =
            FStar_All.pipe_right sigelts
              (FStar_List.collect
                 (fun x ->
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((false,
                          {
                            FStar_Syntax_Syntax.lbname = FStar_Pervasives.Inr
                              uu___;
                            FStar_Syntax_Syntax.lbunivs = uu___1;
                            FStar_Syntax_Syntax.lbtyp = uu___2;
                            FStar_Syntax_Syntax.lbeff = uu___3;
                            FStar_Syntax_Syntax.lbdef = uu___4;
                            FStar_Syntax_Syntax.lbattrs = uu___5;
                            FStar_Syntax_Syntax.lbpos = uu___6;_}::[]),
                         uu___7)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu___, uu___1) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu___ -> [])) in
          match type_abbrev_sigelts with
          | [] ->
              ({
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle (sigelts, members));
                 FStar_Syntax_Syntax.sigrng = rng;
                 FStar_Syntax_Syntax.sigquals = quals;
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = sigattrs;
                 FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
               }, [])
          | uu___ ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu___1,
                              {
                                FStar_Syntax_Syntax.lbname =
                                  FStar_Pervasives.Inr fv;
                                FStar_Syntax_Syntax.lbunivs = uu___2;
                                FStar_Syntax_Syntax.lbtyp = uu___3;
                                FStar_Syntax_Syntax.lbeff = uu___4;
                                FStar_Syntax_Syntax.lbdef = uu___5;
                                FStar_Syntax_Syntax.lbattrs = uu___6;
                                FStar_Syntax_Syntax.lbpos = uu___7;_}::[]),
                             uu___8)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu___1 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible")) in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref [] in
                let in_progress = FStar_Util.mk_ref [] in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts in
                let remove_not_unfolded lid =
                  let uu___1 =
                    let uu___2 = FStar_ST.op_Bang not_unfolded_yet in
                    FStar_All.pipe_right uu___2
                      (FStar_List.filter
                         (fun x ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu___3,
                                  {
                                    FStar_Syntax_Syntax.lbname =
                                      FStar_Pervasives.Inr fv;
                                    FStar_Syntax_Syntax.lbunivs = uu___4;
                                    FStar_Syntax_Syntax.lbtyp = uu___5;
                                    FStar_Syntax_Syntax.lbeff = uu___6;
                                    FStar_Syntax_Syntax.lbdef = uu___7;
                                    FStar_Syntax_Syntax.lbattrs = uu___8;
                                    FStar_Syntax_Syntax.lbpos = uu___9;_}::[]),
                                 uu___10)
                                ->
                                let uu___11 =
                                  FStar_Ident.lid_equals lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                Prims.op_Negation uu___11
                            | uu___3 -> true)) in
                  FStar_ST.op_Colon_Equals not_unfolded_yet uu___1 in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu___1,
                          {
                            FStar_Syntax_Syntax.lbname = FStar_Pervasives.Inr
                              fv';
                            FStar_Syntax_Syntax.lbunivs = uu___2;
                            FStar_Syntax_Syntax.lbtyp = uu___3;
                            FStar_Syntax_Syntax.lbeff = uu___4;
                            FStar_Syntax_Syntax.lbdef = uu___5;
                            FStar_Syntax_Syntax.lbattrs = uu___6;
                            FStar_Syntax_Syntax.lbpos = uu___7;_}::[]),
                         uu___8)
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
                            ((uu___1,
                              { FStar_Syntax_Syntax.lbname = uu___2;
                                FStar_Syntax_Syntax.lbunivs = uu___3;
                                FStar_Syntax_Syntax.lbtyp = uu___4;
                                FStar_Syntax_Syntax.lbeff = uu___5;
                                FStar_Syntax_Syntax.lbdef = tm;
                                FStar_Syntax_Syntax.lbattrs = uu___6;
                                FStar_Syntax_Syntax.lbpos = uu___7;_}::[]),
                             uu___8);
                          FStar_Syntax_Syntax.sigrng = uu___9;
                          FStar_Syntax_Syntax.sigquals = uu___10;
                          FStar_Syntax_Syntax.sigmeta = uu___11;
                          FStar_Syntax_Syntax.sigattrs = uu___12;
                          FStar_Syntax_Syntax.sigopts = uu___13;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu___1 -> FStar_Pervasives_Native.None in
                  let uu___1 =
                    let uu___2 = FStar_ST.op_Bang rev_unfolded_type_abbrevs in
                    FStar_Util.find_map uu___2 replacee_term in
                  match uu___1 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None ->
                      let uu___2 =
                        FStar_Util.find_map type_abbrev_sigelts replacee in
                      (match uu___2 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu___3 =
                             let uu___4 = FStar_ST.op_Bang in_progress in
                             FStar_List.existsb
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
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 uu___4 in
                             let uu___4 =
                               FStar_Ident.range_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_CycleInRecTypeAbbreviation,
                                 msg) uu___4
                           else unfold_abbrev se
                       | uu___3 -> t)
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu___1) ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___2 ->
                                match uu___2 with
                                | FStar_Syntax_Syntax.Noeq -> false
                                | uu___3 -> true)) in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Pervasives.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu___2 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible" in
                      ((let uu___3 =
                          let uu___4 = FStar_ST.op_Bang in_progress in lid ::
                            uu___4 in
                        FStar_ST.op_Colon_Equals in_progress uu___3);
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
                                    let uu___4 = lb in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___4.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___4.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___4.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm';
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___4.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___4.FStar_Syntax_Syntax.lbpos)
                                    } in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid]) in
                                  ((let uu___5 =
                                      let uu___6 =
                                        FStar_ST.op_Bang
                                          rev_unfolded_type_abbrevs in
                                      (let uu___7 = x in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___7.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___7.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (uu___7.FStar_Syntax_Syntax.sigattrs);
                                         FStar_Syntax_Syntax.sigopts =
                                           (uu___7.FStar_Syntax_Syntax.sigopts)
                                       }) :: uu___6 in
                                    FStar_ST.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu___5);
                                   (match () with
                                    | () ->
                                        ((let uu___6 =
                                            let uu___7 =
                                              FStar_ST.op_Bang in_progress in
                                            FStar_List.tl uu___7 in
                                          FStar_ST.op_Colon_Equals
                                            in_progress uu___6);
                                         (match () with | () -> tm'))))))))
                  | uu___1 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible" in
                let rec aux uu___1 =
                  let uu___2 = FStar_ST.op_Bang not_unfolded_yet in
                  match uu___2 with
                  | x::uu___3 -> let _unused = unfold_abbrev x in aux ()
                  | uu___3 ->
                      let uu___4 = FStar_ST.op_Bang rev_unfolded_type_abbrevs in
                      FStar_List.rev uu___4 in
                aux () in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid ->
                     FStar_List.for_all
                       (fun lid' ->
                          let uu___1 = FStar_Ident.lid_equals lid lid' in
                          Prims.op_Negation uu___1) type_abbrevs) l in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu___1,
                             {
                               FStar_Syntax_Syntax.lbname =
                                 FStar_Pervasives.Inr fv';
                               FStar_Syntax_Syntax.lbunivs = uu___2;
                               FStar_Syntax_Syntax.lbtyp = uu___3;
                               FStar_Syntax_Syntax.lbeff = uu___4;
                               FStar_Syntax_Syntax.lbdef = tm;
                               FStar_Syntax_Syntax.lbattrs = uu___5;
                               FStar_Syntax_Syntax.lbpos = uu___6;_}::[]),
                            uu___7)
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
                      (lid, univs, bnd, ty, mut, dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___1 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___1.FStar_Syntax_Syntax.sigopts)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid, univs, ty, res, npars, mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___1 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___1.FStar_Syntax_Syntax.sigopts)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu___1, uu___2) -> []
                  | uu___1 ->
                      failwith
                        "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible" in
                FStar_List.collect unfold_in_sig sigelts in
              let new_members = filter_out_type_abbrevs members in
              let new_bundle =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_bundle
                       (inductives_with_abbrevs_unfolded, new_members));
                  FStar_Syntax_Syntax.sigrng = rng;
                  FStar_Syntax_Syntax.sigquals = quals;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = sigattrs;
                  FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                } in
              (new_bundle, unfolded_type_abbrevs)