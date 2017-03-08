open Prims
let disentangle_abbrevs_from_bundle:
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lident Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.sigelt* FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sigelts  ->
    fun quals  ->
      fun members  ->
        fun rng  ->
          let type_abbrev_sigelts =
            FStar_All.pipe_right sigelts
              (FStar_List.collect
                 (fun x  ->
                    match x with
                    | FStar_Syntax_Syntax.Sig_let
                        ((false
                          ,{
                             FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                               uu____31;
                             FStar_Syntax_Syntax.lbunivs = uu____32;
                             FStar_Syntax_Syntax.lbtyp = uu____33;
                             FStar_Syntax_Syntax.lbeff = uu____34;
                             FStar_Syntax_Syntax.lbdef = uu____35;_}::[]),uu____36,uu____37,uu____38,uu____39)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let
                        (uu____55,uu____56,uu____57,uu____58,uu____59) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____67 -> [])) in
          match type_abbrev_sigelts with
          | [] ->
              ((FStar_Syntax_Syntax.Sig_bundle (sigelts, quals, members, rng)),
                [])
          | uu____75 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun uu___200_81  ->
                        match uu___200_81 with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____82,{
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____84;
                                         FStar_Syntax_Syntax.lbtyp = uu____85;
                                         FStar_Syntax_Syntax.lbeff = uu____86;
                                         FStar_Syntax_Syntax.lbdef = uu____87;_}::[]),uu____88,uu____89,uu____90,uu____91)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____111 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible")) in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref [] in
                let in_progress = FStar_Util.mk_ref [] in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts in
                let remove_not_unfolded lid =
                  let uu____133 =
                    let uu____135 = FStar_ST.read not_unfolded_yet in
                    FStar_All.pipe_right uu____135
                      (FStar_List.filter
                         (fun uu___201_142  ->
                            match uu___201_142 with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____143,{
                                              FStar_Syntax_Syntax.lbname =
                                                FStar_Util.Inr fv;
                                              FStar_Syntax_Syntax.lbunivs =
                                                uu____145;
                                              FStar_Syntax_Syntax.lbtyp =
                                                uu____146;
                                              FStar_Syntax_Syntax.lbeff =
                                                uu____147;
                                              FStar_Syntax_Syntax.lbdef =
                                                uu____148;_}::[]),uu____149,uu____150,uu____151,uu____152)
                                ->
                                Prims.op_Negation
                                  (FStar_Ident.lid_equals lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                            | uu____172 -> true)) in
                  FStar_ST.write not_unfolded_yet uu____133 in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____192,{
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inr fv';
                                      FStar_Syntax_Syntax.lbunivs = uu____194;
                                      FStar_Syntax_Syntax.lbtyp = uu____195;
                                      FStar_Syntax_Syntax.lbeff = uu____196;
                                      FStar_Syntax_Syntax.lbdef = uu____197;_}::[]),uu____198,uu____199,uu____200,uu____201)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> Some x
                    | uu____225 -> None in
                  let replacee_term x =
                    match replacee x with
                    | Some (FStar_Syntax_Syntax.Sig_let
                        ((uu____236,{ FStar_Syntax_Syntax.lbname = uu____237;
                                      FStar_Syntax_Syntax.lbunivs = uu____238;
                                      FStar_Syntax_Syntax.lbtyp = uu____239;
                                      FStar_Syntax_Syntax.lbeff = uu____240;
                                      FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____242,uu____243,uu____244,uu____245))
                        -> Some tm
                    | uu____265 -> None in
                  let uu____269 =
                    let uu____273 = FStar_ST.read rev_unfolded_type_abbrevs in
                    FStar_Util.find_map uu____273 replacee_term in
                  match uu____269 with
                  | Some x -> x
                  | None  ->
                      let uu____287 =
                        FStar_Util.find_map type_abbrev_sigelts replacee in
                      (match uu____287 with
                       | Some se ->
                           let uu____290 =
                             let uu____291 = FStar_ST.read in_progress in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____291 in
                           if uu____290
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                             Prims.raise
                               (FStar_Errors.Error
                                  (msg,
                                    (FStar_Ident.range_of_lid
                                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                           else unfold_abbrev se
                       | uu____311 -> t)
                and unfold_abbrev uu___203_313 =
                  match uu___203_313 with
                  | FStar_Syntax_Syntax.Sig_let
                      ((false ,lb::[]),rng,uu____316,quals,attr) ->
                      let quals =
                        FStar_All.pipe_right quals
                          (FStar_List.filter
                             (fun uu___202_333  ->
                                match uu___202_333 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____334 -> true)) in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____341 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible" in
                      ((let uu____345 =
                          let uu____347 = FStar_ST.read in_progress in lid ::
                            uu____347 in
                        FStar_ST.write in_progress uu____345);
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
                                    let uu___205_359 = lb in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___205_359.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___205_359.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___205_359.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm'
                                    } in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), rng, [lid], quals,
                                        attr) in
                                  ((let uu____369 =
                                      let uu____371 =
                                        FStar_ST.read
                                          rev_unfolded_type_abbrevs in
                                      sigelt' :: uu____371 in
                                    FStar_ST.write rev_unfolded_type_abbrevs
                                      uu____369);
                                   (match () with
                                    | () ->
                                        ((let uu____380 =
                                            let uu____382 =
                                              FStar_ST.read in_progress in
                                            FStar_List.tl uu____382 in
                                          FStar_ST.write in_progress
                                            uu____380);
                                         (match () with | () -> tm'))))))))
                  | uu____390 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible" in
                let rec aux uu____395 =
                  let uu____396 = FStar_ST.read not_unfolded_yet in
                  match uu____396 with
                  | x::uu____403 -> let _unused = unfold_abbrev x in aux ()
                  | uu____406 ->
                      let uu____408 = FStar_ST.read rev_unfolded_type_abbrevs in
                      FStar_List.rev uu____408 in
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
                       match x with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____437,{
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv';
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____439;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____440;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____441;
                                         FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____443,uu____444,uu____445,uu____446)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> Some tm
                       | uu____472 -> None) in
                let unfold_fv t fv =
                  let uu____482 = find_in_unfolded fv in
                  match uu____482 with | Some t' -> t' | uu____491 -> t in
                let unfold_in_sig uu___204_499 =
                  match uu___204_499 with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs,bnd,ty,mut,dc,quals,rng) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid, univs, bnd', ty', mut', dc, quals, rng)]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs,ty,res,npars,quals,mut,rng) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [FStar_Syntax_Syntax.Sig_datacon
                         (lid, univs, ty', res, npars, quals, mut', rng)]
                  | FStar_Syntax_Syntax.Sig_let
                      (uu____539,uu____540,uu____541,uu____542,uu____543) ->
                      []
                  | uu____550 ->
                      failwith
                        "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible" in
                FStar_List.collect unfold_in_sig sigelts in
              let new_members = filter_out_type_abbrevs members in
              let new_bundle =
                FStar_Syntax_Syntax.Sig_bundle
                  (inductives_with_abbrevs_unfolded, quals, new_members, rng) in
              (new_bundle, unfolded_type_abbrevs)