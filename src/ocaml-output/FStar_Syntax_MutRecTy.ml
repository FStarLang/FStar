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
                            FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                              uu____68;
                            FStar_Syntax_Syntax.lbunivs = uu____69;
                            FStar_Syntax_Syntax.lbtyp = uu____70;
                            FStar_Syntax_Syntax.lbeff = uu____71;
                            FStar_Syntax_Syntax.lbdef = uu____72;
                            FStar_Syntax_Syntax.lbattrs = uu____73;
                            FStar_Syntax_Syntax.lbpos = uu____74;_}::[]),
                         uu____75)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu____94, uu____95) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____103 -> [])) in
          match type_abbrev_sigelts with
          | [] ->
              ({
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle (sigelts, members));
                 FStar_Syntax_Syntax.sigrng = rng;
                 FStar_Syntax_Syntax.sigquals = quals;
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = sigattrs
               }, [])
          | uu____116 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____137,
                              {
                                FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                  fv;
                                FStar_Syntax_Syntax.lbunivs = uu____139;
                                FStar_Syntax_Syntax.lbtyp = uu____140;
                                FStar_Syntax_Syntax.lbeff = uu____141;
                                FStar_Syntax_Syntax.lbdef = uu____142;
                                FStar_Syntax_Syntax.lbattrs = uu____143;
                                FStar_Syntax_Syntax.lbpos = uu____144;_}::[]),
                             uu____145)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____164 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible")) in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref [] in
                let in_progress = FStar_Util.mk_ref [] in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts in
                let remove_not_unfolded lid =
                  let uu____196 =
                    let uu____199 = FStar_ST.op_Bang not_unfolded_yet in
                    FStar_All.pipe_right uu____199
                      (FStar_List.filter
                         (fun x ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____242,
                                  {
                                    FStar_Syntax_Syntax.lbname =
                                      FStar_Util.Inr fv;
                                    FStar_Syntax_Syntax.lbunivs = uu____244;
                                    FStar_Syntax_Syntax.lbtyp = uu____245;
                                    FStar_Syntax_Syntax.lbeff = uu____246;
                                    FStar_Syntax_Syntax.lbdef = uu____247;
                                    FStar_Syntax_Syntax.lbattrs = uu____248;
                                    FStar_Syntax_Syntax.lbpos = uu____249;_}::[]),
                                 uu____250)
                                ->
                                let uu____269 =
                                  FStar_Ident.lid_equals lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                Prims.op_Negation uu____269
                            | uu____271 -> true)) in
                  FStar_ST.op_Colon_Equals not_unfolded_yet uu____196 in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____322,
                          { FStar_Syntax_Syntax.lbname = FStar_Util.Inr fv';
                            FStar_Syntax_Syntax.lbunivs = uu____324;
                            FStar_Syntax_Syntax.lbtyp = uu____325;
                            FStar_Syntax_Syntax.lbeff = uu____326;
                            FStar_Syntax_Syntax.lbdef = uu____327;
                            FStar_Syntax_Syntax.lbattrs = uu____328;
                            FStar_Syntax_Syntax.lbpos = uu____329;_}::[]),
                         uu____330)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu____349 -> FStar_Pervasives_Native.None in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____364,
                              { FStar_Syntax_Syntax.lbname = uu____365;
                                FStar_Syntax_Syntax.lbunivs = uu____366;
                                FStar_Syntax_Syntax.lbtyp = uu____367;
                                FStar_Syntax_Syntax.lbeff = uu____368;
                                FStar_Syntax_Syntax.lbdef = tm;
                                FStar_Syntax_Syntax.lbattrs = uu____370;
                                FStar_Syntax_Syntax.lbpos = uu____371;_}::[]),
                             uu____372);
                          FStar_Syntax_Syntax.sigrng = uu____373;
                          FStar_Syntax_Syntax.sigquals = uu____374;
                          FStar_Syntax_Syntax.sigmeta = uu____375;
                          FStar_Syntax_Syntax.sigattrs = uu____376;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____405 -> FStar_Pervasives_Native.None in
                  let uu____410 =
                    let uu____415 =
                      FStar_ST.op_Bang rev_unfolded_type_abbrevs in
                    FStar_Util.find_map uu____415 replacee_term in
                  match uu____410 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None ->
                      let uu____450 =
                        FStar_Util.find_map type_abbrev_sigelts replacee in
                      (match uu____450 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____454 =
                             let uu____456 = FStar_ST.op_Bang in_progress in
                             FStar_List.existsb
                               (fun x ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____456 in
                           if uu____454
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                             let uu____488 =
                               FStar_Ident.range_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_CycleInRecTypeAbbreviation,
                                 msg) uu____488
                           else unfold_abbrev se
                       | uu____492 -> t)
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____497)
                      ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___0_514 ->
                                match uu___0_514 with
                                | FStar_Syntax_Syntax.Noeq -> false
                                | uu____517 -> true)) in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____521 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible" in
                      ((let uu____528 =
                          let uu____531 = FStar_ST.op_Bang in_progress in lid
                            :: uu____531 in
                        FStar_ST.op_Colon_Equals in_progress uu____528);
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
                                    let uu___145_584 = lb in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___145_584.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___145_584.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___145_584.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm';
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___145_584.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___145_584.FStar_Syntax_Syntax.lbpos)
                                    } in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid]) in
                                  ((let uu____593 =
                                      let uu____596 =
                                        FStar_ST.op_Bang
                                          rev_unfolded_type_abbrevs in
                                      (let uu___149_623 = x in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___149_623.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___149_623.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (uu___149_623.FStar_Syntax_Syntax.sigattrs)
                                       }) :: uu____596 in
                                    FStar_ST.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu____593);
                                   (match () with
                                    | () ->
                                        ((let uu____648 =
                                            let uu____651 =
                                              FStar_ST.op_Bang in_progress in
                                            FStar_List.tl uu____651 in
                                          FStar_ST.op_Colon_Equals
                                            in_progress uu____648);
                                         (match () with | () -> tm'))))))))
                  | uu____700 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible" in
                let rec aux uu____709 =
                  let uu____710 = FStar_ST.op_Bang not_unfolded_yet in
                  match uu____710 with
                  | x::uu____739 -> let _unused = unfold_abbrev x in aux ()
                  | uu____743 ->
                      let uu____746 =
                        FStar_ST.op_Bang rev_unfolded_type_abbrevs in
                      FStar_List.rev uu____746 in
                aux () in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid ->
                     FStar_List.for_all
                       (fun lid' ->
                          let uu____789 = FStar_Ident.lid_equals lid lid' in
                          Prims.op_Negation uu____789) type_abbrevs) l in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____821,
                             {
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 fv';
                               FStar_Syntax_Syntax.lbunivs = uu____823;
                               FStar_Syntax_Syntax.lbtyp = uu____824;
                               FStar_Syntax_Syntax.lbeff = uu____825;
                               FStar_Syntax_Syntax.lbdef = tm;
                               FStar_Syntax_Syntax.lbattrs = uu____827;
                               FStar_Syntax_Syntax.lbpos = uu____828;_}::[]),
                            uu____829)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____850 -> FStar_Pervasives_Native.None) in
                let unfold_fv t fv =
                  let uu____864 = find_in_unfolded fv in
                  match uu____864 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____874 -> t in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univs, bnd, ty, mut, dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___204_909 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___204_909.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___204_909.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___204_909.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___204_909.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid, univs, ty, res, npars, mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___216_931 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___216_931.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___216_931.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___216_931.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___216_931.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu____935, uu____936) -> []
                  | uu____941 ->
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
                  FStar_Syntax_Syntax.sigattrs = sigattrs
                } in
              (new_bundle, unfolded_type_abbrevs)