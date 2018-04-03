open Prims
let (disentangle_abbrevs_from_bundle :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lident Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.sigelt Prims.list)
            FStar_Pervasives_Native.tuple2)
  =
  fun sigelts  ->
    fun quals  ->
      fun members  ->
        fun rng  ->
          let sigattrs =
            FStar_List.collect (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
              sigelts
             in
          let type_abbrev_sigelts =
            FStar_All.pipe_right sigelts
              (FStar_List.collect
                 (fun x  ->
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((false
                          ,{
                             FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                               uu____61;
                             FStar_Syntax_Syntax.lbunivs = uu____62;
                             FStar_Syntax_Syntax.lbtyp = uu____63;
                             FStar_Syntax_Syntax.lbeff = uu____64;
                             FStar_Syntax_Syntax.lbdef = uu____65;
                             FStar_Syntax_Syntax.lbattrs = uu____66;
                             FStar_Syntax_Syntax.lbpos = uu____67;_}::[]),uu____68)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu____91,uu____92) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____99 -> []))
             in
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
          | uu____112 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____133,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____135;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____136;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____137;
                                          FStar_Syntax_Syntax.lbdef =
                                            uu____138;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____139;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____140;_}::[]),uu____141)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____164 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible"))
                 in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref []  in
                let in_progress = FStar_Util.mk_ref []  in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts
                   in
                let remove_not_unfolded lid =
                  let uu____193 =
                    let uu____196 = FStar_ST.op_Bang not_unfolded_yet  in
                    FStar_All.pipe_right uu____196
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____260,{
                                              FStar_Syntax_Syntax.lbname =
                                                FStar_Util.Inr fv;
                                              FStar_Syntax_Syntax.lbunivs =
                                                uu____262;
                                              FStar_Syntax_Syntax.lbtyp =
                                                uu____263;
                                              FStar_Syntax_Syntax.lbeff =
                                                uu____264;
                                              FStar_Syntax_Syntax.lbdef =
                                                uu____265;
                                              FStar_Syntax_Syntax.lbattrs =
                                                uu____266;
                                              FStar_Syntax_Syntax.lbpos =
                                                uu____267;_}::[]),uu____268)
                                ->
                                let uu____291 =
                                  FStar_Ident.lid_equals lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                Prims.op_Negation uu____291
                            | uu____292 -> true))
                     in
                  FStar_ST.op_Colon_Equals not_unfolded_yet uu____193  in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____356,{
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inr fv';
                                      FStar_Syntax_Syntax.lbunivs = uu____358;
                                      FStar_Syntax_Syntax.lbtyp = uu____359;
                                      FStar_Syntax_Syntax.lbeff = uu____360;
                                      FStar_Syntax_Syntax.lbdef = uu____361;
                                      FStar_Syntax_Syntax.lbattrs = uu____362;
                                      FStar_Syntax_Syntax.lbpos = uu____363;_}::[]),uu____364)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu____387 -> FStar_Pervasives_Native.None  in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____400,{
                                          FStar_Syntax_Syntax.lbname =
                                            uu____401;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____402;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____403;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____404;
                                          FStar_Syntax_Syntax.lbdef = tm;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____406;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____407;_}::[]),uu____408);
                          FStar_Syntax_Syntax.sigrng = uu____409;
                          FStar_Syntax_Syntax.sigquals = uu____410;
                          FStar_Syntax_Syntax.sigmeta = uu____411;
                          FStar_Syntax_Syntax.sigattrs = uu____412;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____445 -> FStar_Pervasives_Native.None  in
                  let uu____450 =
                    let uu____455 =
                      FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                    FStar_Util.find_map uu____455 replacee_term  in
                  match uu____450 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None  ->
                      let uu____512 =
                        FStar_Util.find_map type_abbrev_sigelts replacee  in
                      (match uu____512 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____516 =
                             let uu____517 = FStar_ST.op_Bang in_progress  in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____517
                              in
                           if uu____516
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                                in
                             let uu____568 =
                               FStar_Ident.range_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_CycleInRecTypeAbbreviation,
                                 msg) uu____568
                           else unfold_abbrev se
                       | uu____570 -> t)
                
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____575)
                      ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___29_596  ->
                                match uu___29_596 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____597 -> true))
                         in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____600 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible"
                         in
                      ((let uu____606 =
                          let uu____609 = FStar_ST.op_Bang in_progress  in
                          lid :: uu____609  in
                        FStar_ST.op_Colon_Equals in_progress uu____606);
                       (match () with
                        | () ->
                            (remove_not_unfolded lid;
                             (match () with
                              | () ->
                                  let ty' =
                                    FStar_Syntax_InstFV.inst unfold_abbrev_fv
                                      lb.FStar_Syntax_Syntax.lbtyp
                                     in
                                  let tm' =
                                    FStar_Syntax_InstFV.inst unfold_abbrev_fv
                                      lb.FStar_Syntax_Syntax.lbdef
                                     in
                                  let lb' =
                                    let uu___30_706 = lb  in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___30_706.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___30_706.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___30_706.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm';
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___30_706.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___30_706.FStar_Syntax_Syntax.lbpos)
                                    }  in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid])
                                     in
                                  ((let uu____719 =
                                      let uu____722 =
                                        FStar_ST.op_Bang
                                          rev_unfolded_type_abbrevs
                                         in
                                      (let uu___31_771 = x  in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___31_771.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___31_771.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (uu___31_771.FStar_Syntax_Syntax.sigattrs)
                                       }) :: uu____722
                                       in
                                    FStar_ST.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu____719);
                                   (match () with
                                    | () ->
                                        ((let uu____818 =
                                            let uu____821 =
                                              FStar_ST.op_Bang in_progress
                                               in
                                            FStar_List.tl uu____821  in
                                          FStar_ST.op_Colon_Equals
                                            in_progress uu____818);
                                         (match () with | () -> tm'))))))))
                  | uu____914 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible"
                 in
                let rec aux uu____920 =
                  let uu____921 = FStar_ST.op_Bang not_unfolded_yet  in
                  match uu____921 with
                  | x::uu____972 -> let _unused = unfold_abbrev x  in aux ()
                  | uu____976 ->
                      let uu____979 =
                        FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                      FStar_List.rev uu____979
                   in
                aux ()  in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid  ->
                     FStar_List.for_all
                       (fun lid'  ->
                          let uu____1042 = FStar_Ident.lid_equals lid lid'
                             in
                          Prims.op_Negation uu____1042) type_abbrevs) l
                 in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x  ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____1071,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv';
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____1073;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____1074;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____1075;
                                          FStar_Syntax_Syntax.lbdef = tm;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____1077;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____1078;_}::[]),uu____1079)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____1104 -> FStar_Pervasives_Native.None)
                   in
                let unfold_fv t fv =
                  let uu____1114 = find_in_unfolded fv  in
                  match uu____1114 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____1124 -> t  in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd  in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___32_1157 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___32_1157.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___32_1157.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___32_1157.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___32_1157.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___33_1177 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___33_1177.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___33_1177.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___33_1177.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___33_1177.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu____1180,uu____1181) -> []
                  | uu____1186 ->
                      failwith
                        "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible"
                   in
                FStar_List.collect unfold_in_sig sigelts  in
              let new_members = filter_out_type_abbrevs members  in
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
                }  in
              (new_bundle, unfolded_type_abbrevs)
  