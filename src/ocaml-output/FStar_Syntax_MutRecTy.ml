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
                               uu____44631;
                             FStar_Syntax_Syntax.lbunivs = uu____44632;
                             FStar_Syntax_Syntax.lbtyp = uu____44633;
                             FStar_Syntax_Syntax.lbeff = uu____44634;
                             FStar_Syntax_Syntax.lbdef = uu____44635;
                             FStar_Syntax_Syntax.lbattrs = uu____44636;
                             FStar_Syntax_Syntax.lbpos = uu____44637;_}::[]),uu____44638)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu____44657,uu____44658)
                        ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____44666 -> []))
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
          | uu____44679 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____44700,{
                                            FStar_Syntax_Syntax.lbname =
                                              FStar_Util.Inr fv;
                                            FStar_Syntax_Syntax.lbunivs =
                                              uu____44702;
                                            FStar_Syntax_Syntax.lbtyp =
                                              uu____44703;
                                            FStar_Syntax_Syntax.lbeff =
                                              uu____44704;
                                            FStar_Syntax_Syntax.lbdef =
                                              uu____44705;
                                            FStar_Syntax_Syntax.lbattrs =
                                              uu____44706;
                                            FStar_Syntax_Syntax.lbpos =
                                              uu____44707;_}::[]),uu____44708)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____44727 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible"))
                 in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref []  in
                let in_progress = FStar_Util.mk_ref []  in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts
                   in
                let remove_not_unfolded lid =
                  let uu____44759 =
                    let uu____44762 = FStar_ST.op_Bang not_unfolded_yet  in
                    FStar_All.pipe_right uu____44762
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____44827,{
                                                FStar_Syntax_Syntax.lbname =
                                                  FStar_Util.Inr fv;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uu____44829;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____44830;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____44831;
                                                FStar_Syntax_Syntax.lbdef =
                                                  uu____44832;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____44833;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____44834;_}::[]),uu____44835)
                                ->
                                let uu____44854 =
                                  FStar_Ident.lid_equals lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                Prims.op_Negation uu____44854
                            | uu____44856 -> true))
                     in
                  FStar_ST.op_Colon_Equals not_unfolded_yet uu____44759  in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____44929,{
                                        FStar_Syntax_Syntax.lbname =
                                          FStar_Util.Inr fv';
                                        FStar_Syntax_Syntax.lbunivs =
                                          uu____44931;
                                        FStar_Syntax_Syntax.lbtyp =
                                          uu____44932;
                                        FStar_Syntax_Syntax.lbeff =
                                          uu____44933;
                                        FStar_Syntax_Syntax.lbdef =
                                          uu____44934;
                                        FStar_Syntax_Syntax.lbattrs =
                                          uu____44935;
                                        FStar_Syntax_Syntax.lbpos =
                                          uu____44936;_}::[]),uu____44937)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu____44956 -> FStar_Pervasives_Native.None  in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____44971,{
                                            FStar_Syntax_Syntax.lbname =
                                              uu____44972;
                                            FStar_Syntax_Syntax.lbunivs =
                                              uu____44973;
                                            FStar_Syntax_Syntax.lbtyp =
                                              uu____44974;
                                            FStar_Syntax_Syntax.lbeff =
                                              uu____44975;
                                            FStar_Syntax_Syntax.lbdef = tm;
                                            FStar_Syntax_Syntax.lbattrs =
                                              uu____44977;
                                            FStar_Syntax_Syntax.lbpos =
                                              uu____44978;_}::[]),uu____44979);
                          FStar_Syntax_Syntax.sigrng = uu____44980;
                          FStar_Syntax_Syntax.sigquals = uu____44981;
                          FStar_Syntax_Syntax.sigmeta = uu____44982;
                          FStar_Syntax_Syntax.sigattrs = uu____44983;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____45012 -> FStar_Pervasives_Native.None  in
                  let uu____45017 =
                    let uu____45022 =
                      FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                    FStar_Util.find_map uu____45022 replacee_term  in
                  match uu____45017 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None  ->
                      let uu____45079 =
                        FStar_Util.find_map type_abbrev_sigelts replacee  in
                      (match uu____45079 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____45083 =
                             let uu____45085 = FStar_ST.op_Bang in_progress
                                in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____45085
                              in
                           if uu____45083
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                                in
                             let uu____45139 =
                               FStar_Ident.range_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_CycleInRecTypeAbbreviation,
                                 msg) uu____45139
                           else unfold_abbrev se
                       | uu____45143 -> t)
                
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____45148)
                      ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___402_45165  ->
                                match uu___402_45165 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____45168 -> true))
                         in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____45172 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible"
                         in
                      ((let uu____45179 =
                          let uu____45182 = FStar_ST.op_Bang in_progress  in
                          lid :: uu____45182  in
                        FStar_ST.op_Colon_Equals in_progress uu____45179);
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
                                    let uu___547_45279 = lb  in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___547_45279.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___547_45279.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___547_45279.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm';
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___547_45279.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___547_45279.FStar_Syntax_Syntax.lbpos)
                                    }  in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid])
                                     in
                                  ((let uu____45288 =
                                      let uu____45291 =
                                        FStar_ST.op_Bang
                                          rev_unfolded_type_abbrevs
                                         in
                                      (let uu___551_45340 = x  in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___551_45340.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___551_45340.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (uu___551_45340.FStar_Syntax_Syntax.sigattrs)
                                       }) :: uu____45291
                                       in
                                    FStar_ST.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu____45288);
                                   (match () with
                                    | () ->
                                        ((let uu____45387 =
                                            let uu____45390 =
                                              FStar_ST.op_Bang in_progress
                                               in
                                            FStar_List.tl uu____45390  in
                                          FStar_ST.op_Colon_Equals
                                            in_progress uu____45387);
                                         (match () with | () -> tm'))))))))
                  | uu____45483 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible"
                 in
                let rec aux uu____45492 =
                  let uu____45493 = FStar_ST.op_Bang not_unfolded_yet  in
                  match uu____45493 with
                  | x::uu____45544 ->
                      let _unused = unfold_abbrev x  in aux ()
                  | uu____45548 ->
                      let uu____45551 =
                        FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                      FStar_List.rev uu____45551
                   in
                aux ()  in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid  ->
                     FStar_List.for_all
                       (fun lid'  ->
                          let uu____45616 = FStar_Ident.lid_equals lid lid'
                             in
                          Prims.op_Negation uu____45616) type_abbrevs) l
                 in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x  ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____45648,{
                                           FStar_Syntax_Syntax.lbname =
                                             FStar_Util.Inr fv';
                                           FStar_Syntax_Syntax.lbunivs =
                                             uu____45650;
                                           FStar_Syntax_Syntax.lbtyp =
                                             uu____45651;
                                           FStar_Syntax_Syntax.lbeff =
                                             uu____45652;
                                           FStar_Syntax_Syntax.lbdef = tm;
                                           FStar_Syntax_Syntax.lbattrs =
                                             uu____45654;
                                           FStar_Syntax_Syntax.lbpos =
                                             uu____45655;_}::[]),uu____45656)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____45677 -> FStar_Pervasives_Native.None)
                   in
                let unfold_fv t fv =
                  let uu____45691 = find_in_unfolded fv  in
                  match uu____45691 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____45701 -> t  in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd  in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___606_45736 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___606_45736.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___606_45736.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___606_45736.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___606_45736.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___618_45758 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___618_45758.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___618_45758.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___618_45758.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___618_45758.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu____45762,uu____45763) ->
                      []
                  | uu____45768 ->
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
  