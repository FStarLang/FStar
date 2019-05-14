open Prims
let (disentangle_abbrevs_from_bundle :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lident Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list))
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
                               uu____159;
                             FStar_Syntax_Syntax.lbunivs = uu____160;
                             FStar_Syntax_Syntax.lbtyp = uu____161;
                             FStar_Syntax_Syntax.lbeff = uu____162;
                             FStar_Syntax_Syntax.lbdef = uu____163;
                             FStar_Syntax_Syntax.lbattrs = uu____164;
                             FStar_Syntax_Syntax.lbpos = uu____165;_}::[]),uu____166)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu____253,uu____254) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____275 -> []))
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
          | uu____332 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____389,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____391;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____392;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____393;
                                          FStar_Syntax_Syntax.lbdef =
                                            uu____394;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____395;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____396;_}::[]),uu____397)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____478 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible"))
                 in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref []  in
                let in_progress = FStar_Util.mk_ref []  in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts
                   in
                let remove_not_unfolded lid =
                  let uu____564 =
                    let uu____572 = FStar_ST.op_Bang not_unfolded_yet  in
                    FStar_All.pipe_right uu____572
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____650,{
                                              FStar_Syntax_Syntax.lbname =
                                                FStar_Util.Inr fv;
                                              FStar_Syntax_Syntax.lbunivs =
                                                uu____652;
                                              FStar_Syntax_Syntax.lbtyp =
                                                uu____653;
                                              FStar_Syntax_Syntax.lbeff =
                                                uu____654;
                                              FStar_Syntax_Syntax.lbdef =
                                                uu____655;
                                              FStar_Syntax_Syntax.lbattrs =
                                                uu____656;
                                              FStar_Syntax_Syntax.lbpos =
                                                uu____657;_}::[]),uu____658)
                                ->
                                let uu____735 =
                                  FStar_Ident.lid_equals lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                Prims.op_Negation uu____735
                            | uu____741 -> true))
                     in
                  FStar_ST.op_Colon_Equals not_unfolded_yet uu____564  in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____853,{
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inr fv';
                                      FStar_Syntax_Syntax.lbunivs = uu____855;
                                      FStar_Syntax_Syntax.lbtyp = uu____856;
                                      FStar_Syntax_Syntax.lbeff = uu____857;
                                      FStar_Syntax_Syntax.lbdef = uu____858;
                                      FStar_Syntax_Syntax.lbattrs = uu____859;
                                      FStar_Syntax_Syntax.lbpos = uu____860;_}::[]),uu____861)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu____951 -> FStar_Pervasives_Native.None  in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____989,{
                                          FStar_Syntax_Syntax.lbname =
                                            uu____990;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____991;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____992;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____993;
                                          FStar_Syntax_Syntax.lbdef = tm;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____995;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____996;_}::[]),uu____997);
                          FStar_Syntax_Syntax.sigrng = uu____998;
                          FStar_Syntax_Syntax.sigquals = uu____999;
                          FStar_Syntax_Syntax.sigmeta = uu____1000;
                          FStar_Syntax_Syntax.sigattrs = uu____1001;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____1100 -> FStar_Pervasives_Native.None  in
                  let uu____1114 =
                    let uu____1123 =
                      FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                    FStar_Util.find_map uu____1123 replacee_term  in
                  match uu____1114 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None  ->
                      let uu____1198 =
                        FStar_Util.find_map type_abbrev_sigelts replacee  in
                      (match uu____1198 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____1231 =
                             let uu____1233 = FStar_ST.op_Bang in_progress
                                in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____1233
                              in
                           if uu____1231
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                                in
                             let uu____1297 =
                               FStar_Ident.range_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_CycleInRecTypeAbbreviation,
                                 msg) uu____1297
                           else unfold_abbrev se
                       | uu____1309 -> t)
                
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1328)
                      ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___0_1381  ->
                                match uu___0_1381 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____1384 -> true))
                         in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____1415 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible"
                         in
                      ((let uu____1434 =
                          let uu____1441 = FStar_ST.op_Bang in_progress  in
                          lid :: uu____1441  in
                        FStar_ST.op_Colon_Equals in_progress uu____1434);
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
                                    let uu___145_1556 = lb  in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___145_1556.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___145_1556.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___145_1556.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm';
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___145_1556.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___145_1556.FStar_Syntax_Syntax.lbpos)
                                    }  in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid])
                                     in
                                  ((let uu____1612 =
                                      let uu____1620 =
                                        FStar_ST.op_Bang
                                          rev_unfolded_type_abbrevs
                                         in
                                      (let uu___149_1667 = x  in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___149_1667.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___149_1667.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (uu___149_1667.FStar_Syntax_Syntax.sigattrs)
                                       }) :: uu____1620
                                       in
                                    FStar_ST.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu____1612);
                                   (match () with
                                    | () ->
                                        ((let uu____1716 =
                                            let uu____1723 =
                                              FStar_ST.op_Bang in_progress
                                               in
                                            FStar_List.tl uu____1723  in
                                          FStar_ST.op_Colon_Equals
                                            in_progress uu____1716);
                                         (match () with | () -> tm'))))))))
                  | uu____1800 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible"
                 in
                let rec aux uu____1818 =
                  let uu____1819 = FStar_ST.op_Bang not_unfolded_yet  in
                  match uu____1819 with
                  | x::uu____1868 -> let _unused = unfold_abbrev x  in aux ()
                  | uu____1895 ->
                      let uu____1903 =
                        FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                      FStar_List.rev uu____1903
                   in
                aux ()  in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid  ->
                     FStar_List.for_all
                       (fun lid'  ->
                          let uu____1994 = FStar_Ident.lid_equals lid lid'
                             in
                          Prims.op_Negation uu____1994) type_abbrevs) l
                 in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x  ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____2059,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv';
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____2061;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____2062;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____2063;
                                          FStar_Syntax_Syntax.lbdef = tm;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____2065;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____2066;_}::[]),uu____2067)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____2158 -> FStar_Pervasives_Native.None)
                   in
                let unfold_fv t fv =
                  let uu____2198 = find_in_unfolded fv  in
                  match uu____2198 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____2224 -> t  in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd  in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___204_2332 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___204_2332.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___204_2332.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___204_2332.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___204_2332.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___216_2434 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___216_2434.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___216_2434.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___216_2434.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___216_2434.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu____2469,uu____2470) -> []
                  | uu____2488 ->
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
  