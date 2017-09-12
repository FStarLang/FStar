open Prims
let disentangle_abbrevs_from_bundle:
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lident Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.sigelt Prims.list)
            FStar_Pervasives_Native.tuple2
  =
  fun sigelts  ->
    fun quals  ->
      fun members  ->
        fun rng  ->
          let sigattrs =
            FStar_List.collect (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
              sigelts in
          let type_abbrev_sigelts =
            FStar_All.pipe_right sigelts
              (FStar_List.collect
                 (fun x  ->
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((false
                          ,{
                             FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                               uu____63;
                             FStar_Syntax_Syntax.lbunivs = uu____64;
                             FStar_Syntax_Syntax.lbtyp = uu____65;
                             FStar_Syntax_Syntax.lbeff = uu____66;
                             FStar_Syntax_Syntax.lbdef = uu____67;_}::[]),uu____68)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu____87,uu____88) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____95 -> [])) in
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
          | uu____108 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____127,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____129;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____130;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____131;
                                          FStar_Syntax_Syntax.lbdef =
                                            uu____132;_}::[]),uu____133)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____152 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible")) in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref [] in
                let in_progress = FStar_Util.mk_ref [] in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts in
                let remove_not_unfolded lid =
                  let uu____181 =
                    let uu____184 = FStar_ST.op_Bang not_unfolded_yet in
                    FStar_All.pipe_right uu____184
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____232,{
                                              FStar_Syntax_Syntax.lbname =
                                                FStar_Util.Inr fv;
                                              FStar_Syntax_Syntax.lbunivs =
                                                uu____234;
                                              FStar_Syntax_Syntax.lbtyp =
                                                uu____235;
                                              FStar_Syntax_Syntax.lbeff =
                                                uu____236;
                                              FStar_Syntax_Syntax.lbdef =
                                                uu____237;_}::[]),uu____238)
                                ->
                                Prims.op_Negation
                                  (FStar_Ident.lid_equals lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                            | uu____257 -> true)) in
                  FStar_ST.op_Colon_Equals not_unfolded_yet uu____181 in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____308,{
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inr fv';
                                      FStar_Syntax_Syntax.lbunivs = uu____310;
                                      FStar_Syntax_Syntax.lbtyp = uu____311;
                                      FStar_Syntax_Syntax.lbeff = uu____312;
                                      FStar_Syntax_Syntax.lbdef = uu____313;_}::[]),uu____314)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu____333 -> FStar_Pervasives_Native.None in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____346,{
                                          FStar_Syntax_Syntax.lbname =
                                            uu____347;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____348;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____349;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____350;
                                          FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____352);
                          FStar_Syntax_Syntax.sigrng = uu____353;
                          FStar_Syntax_Syntax.sigquals = uu____354;
                          FStar_Syntax_Syntax.sigmeta = uu____355;
                          FStar_Syntax_Syntax.sigattrs = uu____356;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____385 -> FStar_Pervasives_Native.None in
                  let uu____390 =
                    let uu____395 =
                      FStar_ST.op_Bang rev_unfolded_type_abbrevs in
                    FStar_Util.find_map uu____395 replacee_term in
                  match uu____390 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None  ->
                      let uu____439 =
                        FStar_Util.find_map type_abbrev_sigelts replacee in
                      (match uu____439 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____443 =
                             let uu____444 = FStar_ST.op_Bang in_progress in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____444 in
                           if uu____443
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                             FStar_Exn.raise
                               (FStar_Errors.Error
                                  (msg,
                                    (FStar_Ident.range_of_lid
                                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                           else unfold_abbrev se
                       | uu____483 -> t)
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____488)
                      ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___215_509  ->
                                match uu___215_509 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____510 -> true)) in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____513 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible" in
                      ((let uu____519 =
                          let uu____522 = FStar_ST.op_Bang in_progress in lid
                            :: uu____522 in
                        FStar_ST.op_Colon_Equals in_progress uu____519);
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
                                    let uu___216_593 = lb in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___216_593.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___216_593.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___216_593.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm'
                                    } in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid]) in
                                  ((let uu____606 =
                                      let uu____609 =
                                        FStar_ST.op_Bang
                                          rev_unfolded_type_abbrevs in
                                      (let uu___217_645 = x in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___217_645.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___217_645.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (uu___217_645.FStar_Syntax_Syntax.sigattrs)
                                       }) :: uu____609 in
                                    FStar_ST.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu____606);
                                   (match () with
                                    | () ->
                                        ((let uu____679 =
                                            let uu____682 =
                                              FStar_ST.op_Bang in_progress in
                                            FStar_List.tl uu____682 in
                                          FStar_ST.op_Colon_Equals
                                            in_progress uu____679);
                                         (match () with | () -> tm'))))))))
                  | uu____749 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible" in
                let rec aux uu____755 =
                  let uu____756 = FStar_ST.op_Bang not_unfolded_yet in
                  match uu____756 with
                  | x::uu____794 -> let _unused = unfold_abbrev x in aux ()
                  | uu____798 ->
                      let uu____801 =
                        FStar_ST.op_Bang rev_unfolded_type_abbrevs in
                      FStar_List.rev uu____801 in
                aux () in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid  ->
                     FStar_List.for_all
                       (fun lid'  ->
                          Prims.op_Negation (FStar_Ident.lid_equals lid lid'))
                       type_abbrevs) l in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x  ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____876,{
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv';
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____878;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____879;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____880;
                                         FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____882)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____903 -> FStar_Pervasives_Native.None) in
                let unfold_fv t fv =
                  let uu____913 = find_in_unfolded fv in
                  match uu____913 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____923 -> t in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs1,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___218_956 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs1, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___218_956.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___218_956.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___218_956.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___218_956.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs1,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___219_976 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs1, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___219_976.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___219_976.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___219_976.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___219_976.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu____979,uu____980) -> []
                  | uu____985 ->
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