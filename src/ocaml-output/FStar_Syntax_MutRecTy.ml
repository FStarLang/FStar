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
                               uu____44700;
                             FStar_Syntax_Syntax.lbunivs = uu____44701;
                             FStar_Syntax_Syntax.lbtyp = uu____44702;
                             FStar_Syntax_Syntax.lbeff = uu____44703;
                             FStar_Syntax_Syntax.lbdef = uu____44704;
                             FStar_Syntax_Syntax.lbattrs = uu____44705;
                             FStar_Syntax_Syntax.lbpos = uu____44706;_}::[]),uu____44707)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu____44726,uu____44727)
                        ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____44735 -> []))
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
          | uu____44748 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____44769,{
                                            FStar_Syntax_Syntax.lbname =
                                              FStar_Util.Inr fv;
                                            FStar_Syntax_Syntax.lbunivs =
                                              uu____44771;
                                            FStar_Syntax_Syntax.lbtyp =
                                              uu____44772;
                                            FStar_Syntax_Syntax.lbeff =
                                              uu____44773;
                                            FStar_Syntax_Syntax.lbdef =
                                              uu____44774;
                                            FStar_Syntax_Syntax.lbattrs =
                                              uu____44775;
                                            FStar_Syntax_Syntax.lbpos =
                                              uu____44776;_}::[]),uu____44777)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____44796 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible"))
                 in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref []  in
                let in_progress = FStar_Util.mk_ref []  in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts
                   in
                let remove_not_unfolded lid =
                  let uu____44828 =
                    let uu____44831 = FStar_ST.op_Bang not_unfolded_yet  in
                    FStar_All.pipe_right uu____44831
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____44896,{
                                                FStar_Syntax_Syntax.lbname =
                                                  FStar_Util.Inr fv;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uu____44898;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____44899;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____44900;
                                                FStar_Syntax_Syntax.lbdef =
                                                  uu____44901;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____44902;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____44903;_}::[]),uu____44904)
                                ->
                                let uu____44923 =
                                  FStar_Ident.lid_equals lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                Prims.op_Negation uu____44923
                            | uu____44925 -> true))
                     in
                  FStar_ST.op_Colon_Equals not_unfolded_yet uu____44828  in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____44998,{
                                        FStar_Syntax_Syntax.lbname =
                                          FStar_Util.Inr fv';
                                        FStar_Syntax_Syntax.lbunivs =
                                          uu____45000;
                                        FStar_Syntax_Syntax.lbtyp =
                                          uu____45001;
                                        FStar_Syntax_Syntax.lbeff =
                                          uu____45002;
                                        FStar_Syntax_Syntax.lbdef =
                                          uu____45003;
                                        FStar_Syntax_Syntax.lbattrs =
                                          uu____45004;
                                        FStar_Syntax_Syntax.lbpos =
                                          uu____45005;_}::[]),uu____45006)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu____45025 -> FStar_Pervasives_Native.None  in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____45040,{
                                            FStar_Syntax_Syntax.lbname =
                                              uu____45041;
                                            FStar_Syntax_Syntax.lbunivs =
                                              uu____45042;
                                            FStar_Syntax_Syntax.lbtyp =
                                              uu____45043;
                                            FStar_Syntax_Syntax.lbeff =
                                              uu____45044;
                                            FStar_Syntax_Syntax.lbdef = tm;
                                            FStar_Syntax_Syntax.lbattrs =
                                              uu____45046;
                                            FStar_Syntax_Syntax.lbpos =
                                              uu____45047;_}::[]),uu____45048);
                          FStar_Syntax_Syntax.sigrng = uu____45049;
                          FStar_Syntax_Syntax.sigquals = uu____45050;
                          FStar_Syntax_Syntax.sigmeta = uu____45051;
                          FStar_Syntax_Syntax.sigattrs = uu____45052;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____45081 -> FStar_Pervasives_Native.None  in
                  let uu____45086 =
                    let uu____45091 =
                      FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                    FStar_Util.find_map uu____45091 replacee_term  in
                  match uu____45086 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None  ->
                      let uu____45148 =
                        FStar_Util.find_map type_abbrev_sigelts replacee  in
                      (match uu____45148 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____45152 =
                             let uu____45154 = FStar_ST.op_Bang in_progress
                                in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____45154
                              in
                           if uu____45152
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                                in
                             let uu____45208 =
                               FStar_Ident.range_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_CycleInRecTypeAbbreviation,
                                 msg) uu____45208
                           else unfold_abbrev se
                       | uu____45212 -> t)
                
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____45217)
                      ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___402_45234  ->
                                match uu___402_45234 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____45237 -> true))
                         in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____45241 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible"
                         in
                      ((let uu____45248 =
                          let uu____45251 = FStar_ST.op_Bang in_progress  in
                          lid :: uu____45251  in
                        FStar_ST.op_Colon_Equals in_progress uu____45248);
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
                                    let uu___547_45348 = lb  in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___547_45348.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___547_45348.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___547_45348.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm';
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___547_45348.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___547_45348.FStar_Syntax_Syntax.lbpos)
                                    }  in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid])
                                     in
                                  ((let uu____45357 =
                                      let uu____45360 =
                                        FStar_ST.op_Bang
                                          rev_unfolded_type_abbrevs
                                         in
                                      (let uu___551_45409 = x  in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___551_45409.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___551_45409.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (uu___551_45409.FStar_Syntax_Syntax.sigattrs)
                                       }) :: uu____45360
                                       in
                                    FStar_ST.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu____45357);
                                   (match () with
                                    | () ->
                                        ((let uu____45456 =
                                            let uu____45459 =
                                              FStar_ST.op_Bang in_progress
                                               in
                                            FStar_List.tl uu____45459  in
                                          FStar_ST.op_Colon_Equals
                                            in_progress uu____45456);
                                         (match () with | () -> tm'))))))))
                  | uu____45552 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible"
                 in
                let rec aux uu____45561 =
                  let uu____45562 = FStar_ST.op_Bang not_unfolded_yet  in
                  match uu____45562 with
                  | x::uu____45613 ->
                      let _unused = unfold_abbrev x  in aux ()
                  | uu____45617 ->
                      let uu____45620 =
                        FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                      FStar_List.rev uu____45620
                   in
                aux ()  in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid  ->
                     FStar_List.for_all
                       (fun lid'  ->
                          let uu____45685 = FStar_Ident.lid_equals lid lid'
                             in
                          Prims.op_Negation uu____45685) type_abbrevs) l
                 in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x  ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____45717,{
                                           FStar_Syntax_Syntax.lbname =
                                             FStar_Util.Inr fv';
                                           FStar_Syntax_Syntax.lbunivs =
                                             uu____45719;
                                           FStar_Syntax_Syntax.lbtyp =
                                             uu____45720;
                                           FStar_Syntax_Syntax.lbeff =
                                             uu____45721;
                                           FStar_Syntax_Syntax.lbdef = tm;
                                           FStar_Syntax_Syntax.lbattrs =
                                             uu____45723;
                                           FStar_Syntax_Syntax.lbpos =
                                             uu____45724;_}::[]),uu____45725)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____45746 -> FStar_Pervasives_Native.None)
                   in
                let unfold_fv t fv =
                  let uu____45760 = find_in_unfolded fv  in
                  match uu____45760 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____45770 -> t  in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd  in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___606_45805 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___606_45805.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___606_45805.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___606_45805.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___606_45805.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___618_45827 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___618_45827.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___618_45827.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___618_45827.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___618_45827.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu____45831,uu____45832) ->
                      []
                  | uu____45837 ->
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
  