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
                               uu____68;
                             FStar_Syntax_Syntax.lbunivs = uu____69;
                             FStar_Syntax_Syntax.lbtyp = uu____70;
                             FStar_Syntax_Syntax.lbeff = uu____71;
                             FStar_Syntax_Syntax.lbdef = uu____72;
                             FStar_Syntax_Syntax.lbattrs = uu____73;
                             FStar_Syntax_Syntax.lbpos = uu____74;_}::[]),uu____75)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu____94,uu____95) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____103 -> []))
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
                 FStar_Syntax_Syntax.sigattrs = sigattrs;
                 FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
               }, [])
          | uu____116 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____137,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____139;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____140;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____141;
                                          FStar_Syntax_Syntax.lbdef =
                                            uu____142;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____143;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____144;_}::[]),uu____145)
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
                  let uu____196 =
                    let uu____199 = FStar_ST.op_Bang not_unfolded_yet  in
                    FStar_All.pipe_right uu____199
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____242,{
                                              FStar_Syntax_Syntax.lbname =
                                                FStar_Util.Inr fv;
                                              FStar_Syntax_Syntax.lbunivs =
                                                uu____244;
                                              FStar_Syntax_Syntax.lbtyp =
                                                uu____245;
                                              FStar_Syntax_Syntax.lbeff =
                                                uu____246;
                                              FStar_Syntax_Syntax.lbdef =
                                                uu____247;
                                              FStar_Syntax_Syntax.lbattrs =
                                                uu____248;
                                              FStar_Syntax_Syntax.lbpos =
                                                uu____249;_}::[]),uu____250)
                                ->
                                let uu____269 =
                                  FStar_Ident.lid_equals lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                Prims.op_Negation uu____269
                            | uu____271 -> true))
                     in
                  FStar_ST.op_Colon_Equals not_unfolded_yet uu____196  in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____322,{
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inr fv';
                                      FStar_Syntax_Syntax.lbunivs = uu____324;
                                      FStar_Syntax_Syntax.lbtyp = uu____325;
                                      FStar_Syntax_Syntax.lbeff = uu____326;
                                      FStar_Syntax_Syntax.lbdef = uu____327;
                                      FStar_Syntax_Syntax.lbattrs = uu____328;
                                      FStar_Syntax_Syntax.lbpos = uu____329;_}::[]),uu____330)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu____349 -> FStar_Pervasives_Native.None  in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____364,{
                                          FStar_Syntax_Syntax.lbname =
                                            uu____365;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____366;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____367;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____368;
                                          FStar_Syntax_Syntax.lbdef = tm;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____370;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____371;_}::[]),uu____372);
                          FStar_Syntax_Syntax.sigrng = uu____373;
                          FStar_Syntax_Syntax.sigquals = uu____374;
                          FStar_Syntax_Syntax.sigmeta = uu____375;
                          FStar_Syntax_Syntax.sigattrs = uu____376;
                          FStar_Syntax_Syntax.sigopts = uu____377;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____408 -> FStar_Pervasives_Native.None  in
                  let uu____413 =
                    let uu____418 =
                      FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                    FStar_Util.find_map uu____418 replacee_term  in
                  match uu____413 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None  ->
                      let uu____453 =
                        FStar_Util.find_map type_abbrev_sigelts replacee  in
                      (match uu____453 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____457 =
                             let uu____459 = FStar_ST.op_Bang in_progress  in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____459
                              in
                           if uu____457
                           then
                             let msg =
                               let uu____490 =
                                 FStar_Ident.string_of_lid
                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  in
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 uu____490
                                in
                             let uu____493 =
                               FStar_Ident.range_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_CycleInRecTypeAbbreviation,
                                 msg) uu____493
                           else unfold_abbrev se
                       | uu____497 -> t)
                
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____502)
                      ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___0_519  ->
                                match uu___0_519 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____522 -> true))
                         in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____526 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible"
                         in
                      ((let uu____533 =
                          let uu____536 = FStar_ST.op_Bang in_progress  in
                          lid :: uu____536  in
                        FStar_ST.op_Colon_Equals in_progress uu____533);
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
                                    let uu___146_589 = lb  in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___146_589.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___146_589.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___146_589.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm';
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___146_589.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___146_589.FStar_Syntax_Syntax.lbpos)
                                    }  in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid])
                                     in
                                  ((let uu____598 =
                                      let uu____601 =
                                        FStar_ST.op_Bang
                                          rev_unfolded_type_abbrevs
                                         in
                                      (let uu___150_628 = x  in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___150_628.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___150_628.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (uu___150_628.FStar_Syntax_Syntax.sigattrs);
                                         FStar_Syntax_Syntax.sigopts =
                                           (uu___150_628.FStar_Syntax_Syntax.sigopts)
                                       }) :: uu____601
                                       in
                                    FStar_ST.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu____598);
                                   (match () with
                                    | () ->
                                        ((let uu____653 =
                                            let uu____656 =
                                              FStar_ST.op_Bang in_progress
                                               in
                                            FStar_List.tl uu____656  in
                                          FStar_ST.op_Colon_Equals
                                            in_progress uu____653);
                                         (match () with | () -> tm'))))))))
                  | uu____705 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible"
                 in
                let rec aux uu____714 =
                  let uu____715 = FStar_ST.op_Bang not_unfolded_yet  in
                  match uu____715 with
                  | x::uu____744 -> let _unused = unfold_abbrev x  in aux ()
                  | uu____748 ->
                      let uu____751 =
                        FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                      FStar_List.rev uu____751
                   in
                aux ()  in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid  ->
                     FStar_List.for_all
                       (fun lid'  ->
                          let uu____794 = FStar_Ident.lid_equals lid lid'  in
                          Prims.op_Negation uu____794) type_abbrevs) l
                 in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x  ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____826,{
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv';
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____828;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____829;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____830;
                                         FStar_Syntax_Syntax.lbdef = tm;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____832;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____833;_}::[]),uu____834)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____855 -> FStar_Pervasives_Native.None)
                   in
                let unfold_fv t fv =
                  let uu____869 = find_in_unfolded fv  in
                  match uu____869 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____879 -> t  in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd  in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___205_914 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___205_914.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___205_914.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___205_914.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___205_914.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___205_914.FStar_Syntax_Syntax.sigopts)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___217_936 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___217_936.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___217_936.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___217_936.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___217_936.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___217_936.FStar_Syntax_Syntax.sigopts)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu____940,uu____941) -> []
                  | uu____946 ->
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
                  FStar_Syntax_Syntax.sigattrs = sigattrs;
                  FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                }  in
              (new_bundle, unfolded_type_abbrevs)
  