open Prims
let interleave:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list
  =
  fun iface  ->
    fun impl  ->
      let id_eq_lid i l =
        i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText in
      let is_val x d =
        match d.FStar_Parser_AST.d with
        | FStar_Parser_AST.Val (y,uu____28) ->
            x.FStar_Ident.idText = y.FStar_Ident.idText
        | uu____29 -> false in
      let is_type1 x d =
        match d.FStar_Parser_AST.d with
        | FStar_Parser_AST.Tycon (uu____37,tys) ->
            FStar_All.pipe_right tys
              (FStar_Util.for_some
                 (fun uu____54  ->
                    match uu____54 with
                    | (t,uu____59) ->
                        (FStar_Parser_AST.id_of_tycon t) =
                          x.FStar_Ident.idText))
        | uu____62 -> false in
      let is_let x d =
        match d.FStar_Parser_AST.d with
        | FStar_Parser_AST.TopLevelLet (uu____70,defs) ->
            let uu____78 = FStar_Parser_AST.lids_of_let defs in
            FStar_All.pipe_right uu____78 (FStar_Util.for_some (id_eq_lid x))
        | FStar_Parser_AST.Tycon (uu____81,tys) ->
            let uu____91 =
              FStar_All.pipe_right tys
                (FStar_List.map
                   (fun uu____101  ->
                      match uu____101 with | (x1,uu____106) -> x1)) in
            FStar_All.pipe_right uu____91
              (FStar_Util.for_some
                 (fun uu___125_110  ->
                    match uu___125_110 with
                    | FStar_Parser_AST.TyconAbbrev
                        (id',uu____112,uu____113,uu____114) ->
                        x.FStar_Ident.idText = id'.FStar_Ident.idText
                    | uu____119 -> false))
        | uu____120 -> false in
      let prefix_until_let x ds =
        FStar_All.pipe_right ds (FStar_Util.prefix_until (is_let x)) in
      let aux_ml iface1 impl1 =
        let rec interleave_vals vals impl2 =
          match vals with
          | [] -> impl2
          | { FStar_Parser_AST.d = FStar_Parser_AST.Val (x,uu____170);
              FStar_Parser_AST.drange = uu____171;
              FStar_Parser_AST.doc = uu____172;
              FStar_Parser_AST.quals = uu____173;
              FStar_Parser_AST.attrs = uu____174;_}::remaining_vals ->
              let d = FStar_List.hd vals in
              let lopt = prefix_until_let x impl2 in
              (match lopt with
               | None  ->
                   Prims.raise
                     (FStar_Errors.Error
                        ((Prims.strcat "No definition found for "
                            x.FStar_Ident.idText),
                          (d.FStar_Parser_AST.drange)))
               | Some (prefix1,let_x,rest_impl) ->
                   let impl3 =
                     FStar_List.append prefix1
                       (FStar_List.append [d; let_x] rest_impl) in
                   interleave_vals remaining_vals impl3)
          | uu____207::remaining_vals -> interleave_vals remaining_vals impl2 in
        interleave_vals iface1 impl1 in
      let rec aux out iface1 impl1 =
        match iface1 with
        | [] ->
            let uu____230 =
              FStar_All.pipe_right (FStar_List.rev out) FStar_List.flatten in
            FStar_List.append uu____230 impl1
        | d::ds ->
            (match d.FStar_Parser_AST.d with
             | FStar_Parser_AST.Tycon (uu____240,tys) when
                 FStar_All.pipe_right tys
                   (FStar_Util.for_some
                      (fun uu___126_257  ->
                         match uu___126_257 with
                         | (FStar_Parser_AST.TyconAbstract
                            uu____261,uu____262) -> true
                         | uu____270 -> false))
                 ->
                 Prims.raise
                   (FStar_Errors.Error
                      ("Interface contains an abstract 'type' declaration; use 'val' instead",
                        (d.FStar_Parser_AST.drange)))
             | FStar_Parser_AST.Val (x,t) ->
                 ((let uu____278 =
                     FStar_All.pipe_right impl1
                       (FStar_List.tryFind
                          (fun d1  -> (is_val x d1) || (is_type1 x d1))) in
                   match uu____278 with
                   | None  -> ()
                   | Some
                       { FStar_Parser_AST.d = FStar_Parser_AST.Val uu____283;
                         FStar_Parser_AST.drange = r;
                         FStar_Parser_AST.doc = uu____285;
                         FStar_Parser_AST.quals = uu____286;
                         FStar_Parser_AST.attrs = uu____287;_}
                       ->
                       let uu____291 =
                         let uu____292 =
                           let uu____295 =
                             let uu____296 =
                               FStar_Parser_AST.decl_to_string d in
                             FStar_Util.format1
                               "%s is repeated in the implementation"
                               uu____296 in
                           (uu____295, r) in
                         FStar_Errors.Error uu____292 in
                       Prims.raise uu____291
                   | Some i ->
                       let uu____298 =
                         let uu____299 =
                           let uu____302 =
                             let uu____303 =
                               FStar_Parser_AST.decl_to_string d in
                             FStar_Util.format1
                               "%s in the interface is implemented with a 'type'"
                               uu____303 in
                           (uu____302, (i.FStar_Parser_AST.drange)) in
                         FStar_Errors.Error uu____299 in
                       Prims.raise uu____298);
                  (let uu____304 = prefix_until_let x iface1 in
                   match uu____304 with
                   | Some uu____312 ->
                       let uu____323 =
                         let uu____324 =
                           let uu____327 =
                             FStar_Util.format2
                               "'val %s' and 'let %s' cannot both be provided in an interface"
                               x.FStar_Ident.idText x.FStar_Ident.idText in
                           (uu____327, (d.FStar_Parser_AST.drange)) in
                         FStar_Errors.Error uu____324 in
                       Prims.raise uu____323
                   | None  ->
                       let lopt = prefix_until_let x impl1 in
                       (match lopt with
                        | None  ->
                            let uu____347 =
                              FStar_All.pipe_right d.FStar_Parser_AST.quals
                                (FStar_List.contains
                                   FStar_Parser_AST.Assumption) in
                            if uu____347
                            then aux ([d] :: out) ds impl1
                            else
                              Prims.raise
                                (FStar_Errors.Error
                                   ((Prims.strcat "No definition found for "
                                       x.FStar_Ident.idText),
                                     (d.FStar_Parser_AST.drange)))
                        | Some (prefix1,let_x,rest_impl) ->
                            let uu____364 =
                              FStar_All.pipe_right d.FStar_Parser_AST.quals
                                (FStar_List.contains
                                   FStar_Parser_AST.Assumption) in
                            if uu____364
                            then
                              let uu____366 =
                                let uu____367 =
                                  let uu____370 =
                                    let uu____371 =
                                      FStar_Range.string_of_range
                                        let_x.FStar_Parser_AST.drange in
                                    FStar_Util.format2
                                      "Assumed declaration %s is defined at %s"
                                      x.FStar_Ident.idText uu____371 in
                                  (uu____370, (d.FStar_Parser_AST.drange)) in
                                FStar_Errors.Error uu____367 in
                              Prims.raise uu____366
                            else
                              (let remaining_iface_vals =
                                 FStar_All.pipe_right ds
                                   (FStar_List.collect
                                      (fun d1  ->
                                         match d1.FStar_Parser_AST.d with
                                         | FStar_Parser_AST.Val
                                             (x1,uu____381) -> [x1]
                                         | uu____382 -> [])) in
                               let uu____383 =
                                 FStar_All.pipe_right prefix1
                                   (FStar_List.tryFind
                                      (fun d1  ->
                                         FStar_All.pipe_right
                                           remaining_iface_vals
                                           (FStar_Util.for_some
                                              (fun x1  -> is_let x1 d1)))) in
                               match uu____383 with
                               | Some d1 ->
                                   let uu____392 =
                                     let uu____393 =
                                       let uu____396 =
                                         let uu____397 =
                                           FStar_Parser_AST.decl_to_string d1 in
                                         let uu____398 =
                                           FStar_Parser_AST.decl_to_string
                                             let_x in
                                         FStar_Util.format2
                                           "%s is out of order with %s"
                                           uu____397 uu____398 in
                                       (uu____396,
                                         (d1.FStar_Parser_AST.drange)) in
                                     FStar_Errors.Error uu____393 in
                                   Prims.raise uu____392
                               | uu____400 ->
                                   (match let_x.FStar_Parser_AST.d with
                                    | FStar_Parser_AST.TopLevelLet
                                        (uu____403,defs) ->
                                        let def_lids =
                                          FStar_Parser_AST.lids_of_let defs in
                                        let iface_prefix_opt =
                                          FStar_All.pipe_right iface1
                                            (FStar_Util.prefix_until
                                               (fun d1  ->
                                                  match d1.FStar_Parser_AST.d
                                                  with
                                                  | FStar_Parser_AST.Val
                                                      (y,uu____429) ->
                                                      let uu____430 =
                                                        FStar_All.pipe_right
                                                          def_lids
                                                          (FStar_Util.for_some
                                                             (id_eq_lid y)) in
                                                      Prims.op_Negation
                                                        uu____430
                                                  | uu____432 -> true)) in
                                        let uu____433 =
                                          match iface_prefix_opt with
                                          | None  -> (iface1, [])
                                          | Some
                                              (all_vals_for_defs,first_non_val,rest_iface)
                                              ->
                                              (all_vals_for_defs,
                                                (first_non_val ::
                                                rest_iface)) in
                                        (match uu____433 with
                                         | (all_vals_for_defs,rest_iface) ->
                                             let hoist =
                                               FStar_List.append prefix1
                                                 (FStar_List.append
                                                    all_vals_for_defs 
                                                    [let_x]) in
                                             aux (hoist :: out) rest_iface
                                               rest_impl)
                                    | uu____473 -> failwith "Impossible")))))
             | uu____475 -> aux ([d] :: out) ds impl1) in
      let uu____477 = FStar_Options.ml_ish () in
      if uu____477 then aux_ml iface impl else aux [] iface impl