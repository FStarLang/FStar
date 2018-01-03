open Prims
let disentangle_abbrevs_from_bundle :
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
                               uu____59;
                             FStar_Syntax_Syntax.lbunivs = uu____60;
                             FStar_Syntax_Syntax.lbtyp = uu____61;
                             FStar_Syntax_Syntax.lbeff = uu____62;
                             FStar_Syntax_Syntax.lbdef = uu____63;_}::[]),uu____64)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu____83,uu____84) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____91 -> []))
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
          | uu____104 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____123,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____125;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____126;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____127;
                                          FStar_Syntax_Syntax.lbdef =
                                            uu____128;_}::[]),uu____129)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____148 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible"))
                 in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref []  in
                let in_progress = FStar_Util.mk_ref []  in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts
                   in
                let remove_not_unfolded lid =
                  let uu____177 =
                    let uu____180 = FStar_ST.op_Bang not_unfolded_yet  in
                    FStar_All.pipe_right uu____180
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____270,{
                                              FStar_Syntax_Syntax.lbname =
                                                FStar_Util.Inr fv;
                                              FStar_Syntax_Syntax.lbunivs =
                                                uu____272;
                                              FStar_Syntax_Syntax.lbtyp =
                                                uu____273;
                                              FStar_Syntax_Syntax.lbeff =
                                                uu____274;
                                              FStar_Syntax_Syntax.lbdef =
                                                uu____275;_}::[]),uu____276)
                                ->
                                Prims.op_Negation
                                  (FStar_Ident.lid_equals lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                            | uu____295 -> true))
                     in
                  FStar_ST.op_Colon_Equals not_unfolded_yet uu____177  in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____388,{
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inr fv';
                                      FStar_Syntax_Syntax.lbunivs = uu____390;
                                      FStar_Syntax_Syntax.lbtyp = uu____391;
                                      FStar_Syntax_Syntax.lbeff = uu____392;
                                      FStar_Syntax_Syntax.lbdef = uu____393;_}::[]),uu____394)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu____413 -> FStar_Pervasives_Native.None  in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____426,{
                                          FStar_Syntax_Syntax.lbname =
                                            uu____427;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____428;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____429;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____430;
                                          FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____432);
                          FStar_Syntax_Syntax.sigrng = uu____433;
                          FStar_Syntax_Syntax.sigquals = uu____434;
                          FStar_Syntax_Syntax.sigmeta = uu____435;
                          FStar_Syntax_Syntax.sigattrs = uu____436;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____465 -> FStar_Pervasives_Native.None  in
                  let uu____470 =
                    let uu____475 =
                      FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                    FStar_Util.find_map uu____475 replacee_term  in
                  match uu____470 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None  ->
                      let uu____561 =
                        FStar_Util.find_map type_abbrev_sigelts replacee  in
                      (match uu____561 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____565 =
                             let uu____566 = FStar_ST.op_Bang in_progress  in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____566
                              in
                           if uu____565
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                                in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_CycleInRecTypeAbbreviation,
                                 msg)
                               (FStar_Ident.range_of_lid
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                           else unfold_abbrev se
                       | uu____647 -> t)
                
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____652)
                      ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___26_673  ->
                                match uu___26_673 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____674 -> true))
                         in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____677 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible"
                         in
                      ((let uu____683 =
                          let uu____686 = FStar_ST.op_Bang in_progress  in
                          lid :: uu____686  in
                        FStar_ST.op_Colon_Equals in_progress uu____683);
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
                                    let uu___27_841 = lb  in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___27_841.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___27_841.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___27_841.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm'
                                    }  in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid])
                                     in
                                  ((let uu____854 =
                                      let uu____857 =
                                        FStar_ST.op_Bang
                                          rev_unfolded_type_abbrevs
                                         in
                                      (let uu___28_935 = x  in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___28_935.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___28_935.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (uu___28_935.FStar_Syntax_Syntax.sigattrs)
                                       }) :: uu____857
                                       in
                                    FStar_ST.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu____854);
                                   (match () with
                                    | () ->
                                        ((let uu____1011 =
                                            let uu____1014 =
                                              FStar_ST.op_Bang in_progress
                                               in
                                            FStar_List.tl uu____1014  in
                                          FStar_ST.op_Colon_Equals
                                            in_progress uu____1011);
                                         (match () with | () -> tm'))))))))
                  | uu____1165 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible"
                 in
                let rec aux uu____1171 =
                  let uu____1172 = FStar_ST.op_Bang not_unfolded_yet  in
                  match uu____1172 with
                  | x::uu____1252 -> let _unused = unfold_abbrev x  in aux ()
                  | uu____1256 ->
                      let uu____1259 =
                        FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                      FStar_List.rev uu____1259
                   in
                aux ()  in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid  ->
                     FStar_List.for_all
                       (fun lid'  ->
                          Prims.op_Negation (FStar_Ident.lid_equals lid lid'))
                       type_abbrevs) l
                 in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x  ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____1376,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv';
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____1378;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____1379;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____1380;
                                          FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____1382)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____1403 -> FStar_Pervasives_Native.None)
                   in
                let unfold_fv t fv =
                  let uu____1413 = find_in_unfolded fv  in
                  match uu____1413 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____1423 -> t  in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd  in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___29_1456 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___29_1456.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___29_1456.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___29_1456.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___29_1456.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___30_1476 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___30_1476.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___30_1476.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___30_1476.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___30_1476.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu____1479,uu____1480) -> []
                  | uu____1485 ->
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
  