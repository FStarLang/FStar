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
                               uu____69;
                             FStar_Syntax_Syntax.lbunivs = uu____70;
                             FStar_Syntax_Syntax.lbtyp = uu____71;
                             FStar_Syntax_Syntax.lbeff = uu____72;
                             FStar_Syntax_Syntax.lbdef = uu____73;
                             FStar_Syntax_Syntax.lbattrs = uu____74;
                             FStar_Syntax_Syntax.lbpos = uu____75;_}::[]),uu____76)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu____93,uu____94) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____101 -> []))
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
          | uu____114 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____135,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____137;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____138;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____139;
                                          FStar_Syntax_Syntax.lbdef =
                                            uu____140;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____141;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____142;_}::[]),uu____143)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____160 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible"))
                 in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref []  in
                let in_progress = FStar_Util.mk_ref []  in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts
                   in
                let remove_not_unfolded lid =
                  let uu____191 =
                    let uu____194 = FStar_ST.op_Bang not_unfolded_yet  in
                    FStar_All.pipe_right uu____194
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____258,{
                                              FStar_Syntax_Syntax.lbname =
                                                FStar_Util.Inr fv;
                                              FStar_Syntax_Syntax.lbunivs =
                                                uu____260;
                                              FStar_Syntax_Syntax.lbtyp =
                                                uu____261;
                                              FStar_Syntax_Syntax.lbeff =
                                                uu____262;
                                              FStar_Syntax_Syntax.lbdef =
                                                uu____263;
                                              FStar_Syntax_Syntax.lbattrs =
                                                uu____264;
                                              FStar_Syntax_Syntax.lbpos =
                                                uu____265;_}::[]),uu____266)
                                ->
                                let uu____283 =
                                  FStar_Ident.lid_equals lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                Prims.op_Negation uu____283
                            | uu____284 -> true))
                     in
                  FStar_ST.op_Colon_Equals not_unfolded_yet uu____191  in
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
                    | uu____381 -> FStar_Pervasives_Native.None  in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____396,{
                                          FStar_Syntax_Syntax.lbname =
                                            uu____397;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____398;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____399;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____400;
                                          FStar_Syntax_Syntax.lbdef = tm;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____402;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____403;_}::[]),uu____404);
                          FStar_Syntax_Syntax.sigrng = uu____405;
                          FStar_Syntax_Syntax.sigquals = uu____406;
                          FStar_Syntax_Syntax.sigmeta = uu____407;
                          FStar_Syntax_Syntax.sigattrs = uu____408;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____435 -> FStar_Pervasives_Native.None  in
                  let uu____440 =
                    let uu____445 =
                      FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                    FStar_Util.find_map uu____445 replacee_term  in
                  match uu____440 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None  ->
                      let uu____502 =
                        FStar_Util.find_map type_abbrev_sigelts replacee  in
                      (match uu____502 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____506 =
                             let uu____507 = FStar_ST.op_Bang in_progress  in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____507
                              in
                           if uu____506
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                                in
                             let uu____558 =
                               FStar_Ident.range_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_CycleInRecTypeAbbreviation,
                                 msg) uu____558
                           else unfold_abbrev se
                       | uu____560 -> t)
                
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____565)
                      ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___99_580  ->
                                match uu___99_580 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____581 -> true))
                         in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____584 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible"
                         in
                      ((let uu____590 =
                          let uu____593 = FStar_ST.op_Bang in_progress  in
                          lid :: uu____593  in
                        FStar_ST.op_Colon_Equals in_progress uu____590);
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
                                    let uu___100_690 = lb  in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___100_690.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___100_690.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___100_690.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm';
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___100_690.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___100_690.FStar_Syntax_Syntax.lbpos)
                                    }  in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid])
                                     in
                                  ((let uu____697 =
                                      let uu____700 =
                                        FStar_ST.op_Bang
                                          rev_unfolded_type_abbrevs
                                         in
                                      (let uu___101_749 = x  in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___101_749.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___101_749.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (uu___101_749.FStar_Syntax_Syntax.sigattrs)
                                       }) :: uu____700
                                       in
                                    FStar_ST.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu____697);
                                   (match () with
                                    | () ->
                                        ((let uu____796 =
                                            let uu____799 =
                                              FStar_ST.op_Bang in_progress
                                               in
                                            FStar_List.tl uu____799  in
                                          FStar_ST.op_Colon_Equals
                                            in_progress uu____796);
                                         (match () with | () -> tm'))))))))
                  | uu____892 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible"
                 in
                let rec aux uu____900 =
                  let uu____901 = FStar_ST.op_Bang not_unfolded_yet  in
                  match uu____901 with
                  | x::uu____952 -> let _unused = unfold_abbrev x  in aux ()
                  | uu____956 ->
                      let uu____959 =
                        FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                      FStar_List.rev uu____959
                   in
                aux ()  in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid  ->
                     FStar_List.for_all
                       (fun lid'  ->
                          let uu____1024 = FStar_Ident.lid_equals lid lid'
                             in
                          Prims.op_Negation uu____1024) type_abbrevs) l
                 in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x  ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____1055,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv';
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____1057;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____1058;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____1059;
                                          FStar_Syntax_Syntax.lbdef = tm;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____1061;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____1062;_}::[]),uu____1063)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____1082 -> FStar_Pervasives_Native.None)
                   in
                let unfold_fv t fv =
                  let uu____1096 = find_in_unfolded fv  in
                  match uu____1096 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____1106 -> t  in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd  in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___102_1141 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___102_1141.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___102_1141.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___102_1141.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___102_1141.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___103_1161 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___103_1161.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___103_1161.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___103_1161.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___103_1161.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu____1164,uu____1165) -> []
                  | uu____1170 ->
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
  