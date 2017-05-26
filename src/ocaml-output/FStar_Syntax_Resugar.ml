open Prims
let bv_as_unique_ident: FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name =
      if
        FStar_Util.starts_with FStar_Ident.reserved_prefix
          (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      then
        let uu____5 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____5
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___195_37  ->
          match uu___195_37 with
          | (uu____41,Some (FStar_Syntax_Syntax.Implicit uu____42)) -> false
          | uu____44 -> true))
let resugar_arg_qual:
  FStar_Syntax_Syntax.arg_qualifier option ->
    FStar_Parser_AST.arg_qualifier option option
  =
  fun q  ->
    match q with
    | None  -> Some None
    | Some (FStar_Syntax_Syntax.Implicit b) ->
        if b then None else Some (Some FStar_Parser_AST.Implicit)
    | Some (FStar_Syntax_Syntax.Equality ) ->
        Some (Some FStar_Parser_AST.Equality)
let rec universe_to_int:
  Prims.int ->
    FStar_Syntax_Syntax.universe -> (Prims.int* FStar_Syntax_Syntax.universe)
  =
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____78 -> (n1, u)
let rec resugar_universe:
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1 (FStar_Parser_AST.Const (FStar_Const.Const_int ("0", None))) r
      | FStar_Syntax_Syntax.U_succ uu____97 ->
          let uu____98 = universe_to_int (Prims.parse_int "0") u in
          (match uu____98 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____103 =
                      let uu____104 =
                        let uu____105 =
                          let uu____111 = FStar_Util.string_of_int n1 in
                          (uu____111, None) in
                        FStar_Const.Const_int uu____105 in
                      FStar_Parser_AST.Const uu____104 in
                    mk1 uu____103 r
                | uu____117 ->
                    let e1 =
                      let uu____119 =
                        let uu____120 =
                          let uu____121 =
                            let uu____127 = FStar_Util.string_of_int n1 in
                            (uu____127, None) in
                          FStar_Const.Const_int uu____121 in
                        FStar_Parser_AST.Const uu____120 in
                      mk1 uu____119 r in
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____137 ->
               let t =
                 let uu____140 =
                   let uu____141 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____141 in
                 mk1 uu____140 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____144 =
                        let uu____145 =
                          let uu____149 = resugar_universe x r in
                          (acc, uu____149, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____145 in
                      mk1 uu____144 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____151 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____156 =
              let uu____159 =
                let uu____160 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____160 in
              (uu____159, r) in
            FStar_Ident.mk_ident uu____156 in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op: Prims.string -> (Prims.string* Prims.int) option =
  fun s  ->
    let name_of_op uu___196_173 =
      match uu___196_173 with
      | "Amp" -> Some ("&", (Prims.parse_int "0"))
      | "At" -> Some ("@", (Prims.parse_int "0"))
      | "Plus" -> Some ("+", (Prims.parse_int "0"))
      | "Minus" -> Some ("-", (Prims.parse_int "0"))
      | "Subtraction" -> Some ("-", (Prims.parse_int "2"))
      | "Slash" -> Some ("/", (Prims.parse_int "0"))
      | "Less" -> Some ("<", (Prims.parse_int "0"))
      | "Equals" -> Some ("=", (Prims.parse_int "0"))
      | "Greater" -> Some (">", (Prims.parse_int "0"))
      | "Underscore" -> Some ("_", (Prims.parse_int "0"))
      | "Bar" -> Some ("|", (Prims.parse_int "0"))
      | "Bang" -> Some ("!", (Prims.parse_int "0"))
      | "Hat" -> Some ("^", (Prims.parse_int "0"))
      | "Percent" -> Some ("%", (Prims.parse_int "0"))
      | "Star" -> Some ("*", (Prims.parse_int "0"))
      | "Question" -> Some ("?", (Prims.parse_int "0"))
      | "Colon" -> Some (":", (Prims.parse_int "0"))
      | uu____211 -> None in
    match s with
    | "op_String_Assignment" -> Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" -> Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" -> Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" -> Some (".()", (Prims.parse_int "0"))
    | uu____225 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____231 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____231 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____238 ->
               let op =
                 let uu____241 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | Some (op,uu____258) -> Prims.strcat acc op
                        | None  -> failwith "wrong composed operator format")
                   "" uu____241 in
               Some (op, (Prims.parse_int "0")))
        else None
let rec resugar_term_as_op:
  FStar_Syntax_Syntax.term -> (Prims.string* Prims.int) option =
  fun t  ->
    let infix_prim_ops =
      [(FStar_Syntax_Const.op_Addition, "+");
      (FStar_Syntax_Const.op_Subtraction, "-");
      (FStar_Syntax_Const.op_Minus, "-");
      (FStar_Syntax_Const.op_Multiply, "*");
      (FStar_Syntax_Const.op_Division, "/");
      (FStar_Syntax_Const.op_Modulus, "%");
      (FStar_Syntax_Const.read_lid, "!");
      (FStar_Syntax_Const.list_append_lid, "@");
      (FStar_Syntax_Const.list_tot_append_lid, "@");
      (FStar_Syntax_Const.strcat_lid, "^");
      (FStar_Syntax_Const.pipe_right_lid, "|>");
      (FStar_Syntax_Const.pipe_left_lid, "<|");
      (FStar_Syntax_Const.op_Eq, "=");
      (FStar_Syntax_Const.op_ColonEq, ":=");
      (FStar_Syntax_Const.op_notEq, "<>");
      (FStar_Syntax_Const.not_lid, "~");
      (FStar_Syntax_Const.op_And, "&&");
      (FStar_Syntax_Const.op_Or, "||");
      (FStar_Syntax_Const.op_LTE, "<=");
      (FStar_Syntax_Const.op_GTE, ">=");
      (FStar_Syntax_Const.op_LT, "<");
      (FStar_Syntax_Const.op_GT, ">");
      (FStar_Syntax_Const.op_Modulus, "mod");
      (FStar_Syntax_Const.and_lid, "/\\");
      (FStar_Syntax_Const.or_lid, "\\/");
      (FStar_Syntax_Const.imp_lid, "==>");
      (FStar_Syntax_Const.iff_lid, "<==>");
      (FStar_Syntax_Const.precedes_lid, "<<");
      (FStar_Syntax_Const.eq2_lid, "==");
      (FStar_Syntax_Const.eq3_lid, "===");
      (FStar_Syntax_Const.forall_lid, "forall");
      (FStar_Syntax_Const.exists_lid, "exists");
      (FStar_Syntax_Const.salloc_lid, "alloc")] in
    let fallback fv =
      let uu____356 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  -> FStar_Syntax_Syntax.fv_eq_lid fv (fst d))) in
      match uu____356 with
      | Some op -> Some ((snd op), (Prims.parse_int "0"))
      | uu____381 ->
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr in
          let str =
            if length1 = (Prims.parse_int "0")
            then
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
            else
              FStar_Util.substring_from
                ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                (length1 + (Prims.parse_int "1")) in
          if FStar_Util.starts_with str "dtuple"
          then Some ("dtuple", (Prims.parse_int "0"))
          else
            if FStar_Util.starts_with str "tuple"
            then Some ("tuple", (Prims.parse_int "0"))
            else
              if FStar_Util.starts_with str "try_with"
              then Some ("try_with", (Prims.parse_int "0"))
              else
                (let uu____424 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.sread_lid in
                 if uu____424
                 then
                   Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else None) in
    let uu____437 =
      let uu____438 = FStar_Syntax_Subst.compress t in
      uu____438.FStar_Syntax_Syntax.n in
    match uu____437 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr in
        let s =
          if length1 = (Prims.parse_int "0")
          then
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          else
            FStar_Util.substring_from
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
              (length1 + (Prims.parse_int "1")) in
        let uu____466 = string_to_op s in
        (match uu____466 with | Some t1 -> Some t1 | uu____480 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____490 -> None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____496 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____500 -> true
    | uu____501 -> false
let is_disj_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_disj uu____505 -> true
    | uu____509 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____537 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____537 in
    let var a r =
      let uu____545 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____545 in
    let uu____546 =
      let uu____547 = FStar_Syntax_Subst.compress t in
      uu____547.FStar_Syntax_Syntax.n in
    match uu____546 with
    | FStar_Syntax_Syntax.Tm_delayed uu____550 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____573 = let uu____575 = bv_as_unique_ident x in [uu____575] in
          FStar_Ident.lid_of_ids uu____573 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____578 = let uu____580 = bv_as_unique_ident x in [uu____580] in
          FStar_Ident.lid_of_ids uu____578 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr in
        let s =
          if length1 = (Prims.parse_int "0")
          then a.FStar_Ident.str
          else
            FStar_Util.substring_from a.FStar_Ident.str
              (length1 + (Prims.parse_int "1")) in
        let is_prefix = Prims.strcat FStar_Ident.reserved_prefix "is_" in
        if FStar_Util.starts_with s is_prefix
        then
          let rest =
            FStar_Util.substring_from s (FStar_String.length is_prefix) in
          let uu____604 =
            let uu____605 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____605 in
          mk1 uu____604
        else
          if
            FStar_Util.starts_with s FStar_Syntax_Util.field_projector_prefix
          then
            (let rest =
               FStar_Util.substring_from s
                 (FStar_String.length
                    FStar_Syntax_Util.field_projector_prefix) in
             let r =
               FStar_Util.split rest FStar_Syntax_Util.field_projector_sep in
             match r with
             | fst1::snd1::[] ->
                 let l =
                   FStar_Ident.lid_of_path [fst1] t.FStar_Syntax_Syntax.pos in
                 let r1 =
                   FStar_Ident.mk_ident (snd1, (t.FStar_Syntax_Syntax.pos)) in
                 mk1 (FStar_Parser_AST.Projector (l, r1))
             | uu____616 -> failwith "wrong projector format")
          else
            (let uu____619 =
               ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid))
                 ||
                 (let uu____620 =
                    let uu____621 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____621 in
                  let uu____622 = FStar_String.get s (Prims.parse_int "0") in
                  uu____620 <> uu____622) in
             if uu____619
             then
               let uu____623 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____623
             else
               (let uu____625 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____625))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____632 = FStar_Options.print_universes () in
        if uu____632
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____636 =
                   let uu____637 =
                     let uu____641 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____641, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____637 in
                 mk1 uu____636) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____644 = FStar_Syntax_Syntax.is_teff t in
        if uu____644
        then
          let uu____645 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____645
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____648 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____648
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____649 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____649
         | uu____650 ->
             let uu____651 = FStar_Options.print_universes () in
             if uu____651
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____662 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____662))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____665) ->
        let uu____688 = FStar_Syntax_Subst.open_term xs body in
        (match uu____688 with
         | (xs1,body1) ->
             let xs2 =
               let uu____694 = FStar_Options.print_implicits () in
               if uu____694 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____701  ->
                       match uu____701 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____721 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____721 with
         | (xs1,body1) ->
             let xs2 =
               let uu____727 = FStar_Options.print_implicits () in
               if uu____727 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____732 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____732 FStar_List.rev in
             let rec aux body3 uu___197_745 =
               match uu___197_745 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____758 =
          let uu____761 =
            let uu____762 = FStar_Syntax_Syntax.mk_binder x in [uu____762] in
          FStar_Syntax_Subst.open_term uu____761 phi in
        (match uu____758 with
         | (x1,phi1) ->
             let b =
               let uu____766 = FStar_List.hd x1 in
               resugar_binder uu____766 t.FStar_Syntax_Syntax.pos in
             let uu____769 =
               let uu____770 =
                 let uu____773 = resugar_term phi1 in (b, uu____773) in
               FStar_Parser_AST.Refine uu____770 in
             mk1 uu____769)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___198_803 =
          match uu___198_803 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____850 -> failwith "last of an empty list" in
        let rec last_two uu___199_874 =
          match uu___199_874 with
          | []|_::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____937::t1 -> last_two t1 in
        let rec last_three uu___200_965 =
          match uu___200_965 with
          | []|_::[]|_::_::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1055::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1091  ->
                    match uu____1091 with | (e2,qual) -> resugar_term e2)) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 mk1
                   (FStar_Parser_AST.App (acc, x, FStar_Parser_AST.Nothing)))
            e2 args2 in
        let args1 =
          let uu____1105 = FStar_Options.print_implicits () in
          if uu____1105 then args else filter_imp args in
        let uu____1114 = resugar_term_as_op e in
        (match uu____1114 with
         | None  -> resugar_as_app e args1
         | Some ("tuple",uu____1120) ->
             (match args1 with
              | (fst1,uu____1124)::(snd1,uu____1126)::rest ->
                  let e1 =
                    let uu____1150 =
                      let uu____1151 =
                        let uu____1155 =
                          let uu____1157 = resugar_term fst1 in
                          let uu____1158 =
                            let uu____1160 = resugar_term snd1 in
                            [uu____1160] in
                          uu____1157 :: uu____1158 in
                        ((FStar_Ident.id_of_text "*"), uu____1155) in
                      FStar_Parser_AST.Op uu____1151 in
                    mk1 uu____1150 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1165  ->
                         match uu____1165 with
                         | (x,uu____1169) ->
                             let uu____1170 =
                               let uu____1171 =
                                 let uu____1175 =
                                   let uu____1177 =
                                     let uu____1179 = resugar_term x in
                                     [uu____1179] in
                                   e1 :: uu____1177 in
                                 ((FStar_Ident.id_of_text "*"), uu____1175) in
                               FStar_Parser_AST.Op uu____1171 in
                             mk1 uu____1170) e1 rest
              | uu____1181 -> resugar_as_app e args1)
         | Some ("dtuple",uu____1187) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1209)::[] -> b
               | uu____1222 -> failwith "wrong arguments to dtuple" in
             let uu____1230 =
               let uu____1231 = FStar_Syntax_Subst.compress body in
               uu____1231.FStar_Syntax_Syntax.n in
             (match uu____1230 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1236) ->
                  let uu____1259 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1259 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1265 = FStar_Options.print_implicits () in
                         if uu____1265 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (FStar_List.map
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1273 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1284  ->
                            match uu____1284 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | Some ("dtuple",uu____1292) -> resugar_as_app e args1
         | Some (ref_read,uu____1296) when
             ref_read = FStar_Syntax_Const.sread_lid.FStar_Ident.str ->
             let uu____1299 = FStar_List.hd args1 in
             (match uu____1299 with
              | (t1,uu____1309) ->
                  let uu____1314 =
                    let uu____1315 = FStar_Syntax_Subst.compress t1 in
                    uu____1315.FStar_Syntax_Syntax.n in
                  (match uu____1314 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____1328 =
                         let uu____1329 =
                           let uu____1332 = resugar_term t1 in
                           (uu____1332, f) in
                         FStar_Parser_AST.Project uu____1329 in
                       mk1 uu____1328
                   | uu____1333 -> resugar_term t1))
         | Some ("try_with",uu____1334) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1350 =
               match new_args with
               | (a1,uu____1364)::(a2,uu____1366)::[] -> (a1, a2)
               | uu____1391 -> failwith "wrong arguments to try_with" in
             (match uu____1350 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1417 =
                      let uu____1418 = FStar_Syntax_Subst.compress term in
                      uu____1418.FStar_Syntax_Syntax.n in
                    match uu____1417 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1423) ->
                        let uu____1446 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1446 with | (x1,e2) -> e2)
                    | uu____1451 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1453 = decomp body in resugar_term uu____1453 in
                  let handler1 =
                    let uu____1455 = decomp handler in
                    resugar_term uu____1455 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1461,uu____1462,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1479,uu____1480,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1493 =
                          let uu____1494 =
                            let uu____1499 = resugar_body t11 in
                            (uu____1499, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1494 in
                        mk1 uu____1493
                    | uu____1501 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1534 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | Some ("try_with",uu____1550) -> resugar_as_app e args1
         | Some (op,uu____1554) when (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body)|FStar_Parser_AST.QForall
                 (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1601 -> (xs, pat, t1) in
             let resugar body =
               let uu____1609 =
                 let uu____1610 = FStar_Syntax_Subst.compress body in
                 uu____1610.FStar_Syntax_Syntax.n in
               match uu____1609 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1615) ->
                   let uu____1638 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1638 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1644 = FStar_Options.print_implicits () in
                          if uu____1644 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (FStar_List.map
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____1650 =
                          let uu____1655 =
                            let uu____1656 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1656.FStar_Syntax_Syntax.n in
                          match uu____1655 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____1696  ->
                                                 match uu____1696 with
                                                 | (e2,uu____1700) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1703) ->
                                    let uu____1704 =
                                      let uu____1706 =
                                        let uu____1707 = name s r in
                                        mk1 uu____1707 in
                                      [uu____1706] in
                                    [uu____1704]
                                | uu____1710 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1715 ->
                              let uu____1716 = resugar_term body2 in
                              ([], uu____1716) in
                        (match uu____1650 with
                         | (pats,body3) ->
                             let uu____1726 = uncurry xs3 pats body3 in
                             (match uu____1726 with
                              | (xs4,pats1,body4) ->
                                  let xs5 =
                                    FStar_All.pipe_right xs4 FStar_List.rev in
                                  if op = "forall"
                                  then
                                    mk1
                                      (FStar_Parser_AST.QForall
                                         (xs5, pats1, body4))
                                  else
                                    mk1
                                      (FStar_Parser_AST.QExists
                                         (xs5, pats1, body4)))))
               | uu____1753 ->
                   if op = "forall"
                   then
                     let uu____1754 =
                       let uu____1755 =
                         let uu____1762 = resugar_term body in
                         ([], [[]], uu____1762) in
                       FStar_Parser_AST.QForall uu____1755 in
                     mk1 uu____1754
                   else
                     (let uu____1769 =
                        let uu____1770 =
                          let uu____1777 = resugar_term body in
                          ([], [[]], uu____1777) in
                        FStar_Parser_AST.QExists uu____1770 in
                      mk1 uu____1769) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____1797)::[] -> resugar b
                | uu____1810 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | Some ("alloc",uu____1817) ->
             let uu____1820 = FStar_List.hd args1 in
             (match uu____1820 with | (e1,uu____1830) -> resugar_term e1)
         | Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1857  ->
                       match uu____1857 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_28 when _0_28 = (Prims.parse_int "0") ->
                  let uu____1862 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1862 with
                   | _0_29 when
                       (_0_29 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1870 =
                         let uu____1871 =
                           let uu____1875 =
                             let uu____1877 = last1 args1 in
                             resugar uu____1877 in
                           (op1, uu____1875) in
                         FStar_Parser_AST.Op uu____1871 in
                       mk1 uu____1870
                   | _0_30 when
                       (_0_30 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1889 =
                         let uu____1890 =
                           let uu____1894 =
                             let uu____1896 = last_two args1 in
                             resugar uu____1896 in
                           (op1, uu____1894) in
                         FStar_Parser_AST.Op uu____1890 in
                       mk1 uu____1889
                   | _0_31 when
                       (_0_31 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____1908 =
                         let uu____1909 =
                           let uu____1913 =
                             let uu____1915 = last_three args1 in
                             resugar uu____1915 in
                           (op1, uu____1913) in
                         FStar_Parser_AST.Op uu____1909 in
                       mk1 uu____1908
                   | uu____1920 -> resugar_as_app e args1)
              | _0_32 when
                  (_0_32 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____1928 =
                    let uu____1929 =
                      let uu____1933 =
                        let uu____1935 = last_two args1 in resugar uu____1935 in
                      (op1, uu____1933) in
                    FStar_Parser_AST.Op uu____1929 in
                  mk1 uu____1928
              | uu____1940 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____1943,t1)::[]) when
        let uu____1994 = is_disj_pat pat in Prims.op_Negation uu____1994 ->
        let bnds =
          let uu____1999 =
            let uu____2002 = resugar_pat pat in
            let uu____2003 = resugar_term e in (uu____2002, uu____2003) in
          [uu____1999] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____2014,t1)::(pat2,uu____2017,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2092 =
          let uu____2093 =
            let uu____2097 = resugar_term e in
            let uu____2098 = resugar_term t1 in
            let uu____2099 = resugar_term t2 in
            (uu____2097, uu____2098, uu____2099) in
          FStar_Parser_AST.If uu____2093 in
        mk1 uu____2092
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2139 =
          match uu____2139 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | None  -> None
                | Some e1 ->
                    let uu____2158 = resugar_term e1 in Some uu____2158 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____2161 =
          let uu____2162 =
            let uu____2170 = resugar_term e in
            let uu____2171 = FStar_List.map resugar_branch branches in
            (uu____2170, uu____2171) in
          FStar_Parser_AST.Match uu____2162 in
        mk1 uu____2161
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2193) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____2246 =
          let uu____2247 =
            let uu____2252 = resugar_term e in (uu____2252, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____2247 in
        mk1 uu____2246
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____2270 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____2270 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2286 =
                 let uu____2289 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2289 in
               match uu____2286 with
               | (univs1,td) ->
                   let uu____2296 =
                     let uu____2303 =
                       let uu____2304 = FStar_Syntax_Subst.compress td in
                       uu____2304.FStar_Syntax_Syntax.n in
                     match uu____2303 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2313,(t1,uu____2315)::(d,uu____2317)::[]) ->
                         (t1, d)
                     | uu____2351 -> failwith "wrong let binding format" in
                   (match uu____2296 with
                    | (typ,def) ->
                        let uu____2372 =
                          let uu____2376 =
                            let uu____2377 = FStar_Syntax_Subst.compress def in
                            uu____2377.FStar_Syntax_Syntax.n in
                          match uu____2376 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2385) ->
                              let uu____2408 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2408 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2417 =
                                       FStar_Options.print_implicits () in
                                     if uu____2417 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2419 -> ([], def, false) in
                        (match uu____2372 with
                         | (binders,term,is_pat_app) ->
                             let universe_to_string univs2 =
                               let uu____2440 =
                                 FStar_Options.print_universes () in
                               if uu____2440
                               then
                                 let uu____2441 =
                                   FStar_List.map
                                     (fun x  -> x.FStar_Ident.idText) univs2 in
                                 FStar_All.pipe_right uu____2441
                                   (FStar_String.concat ", ")
                               else "" in
                             let uu____2446 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2457 =
                                     let uu____2458 =
                                       let uu____2459 =
                                         let uu____2463 =
                                           bv_as_unique_ident bv in
                                         (uu____2463, None) in
                                       FStar_Parser_AST.PatVar uu____2459 in
                                     mk_pat uu____2458 in
                                   (uu____2457, term) in
                             (match uu____2446 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (FStar_List.map
                                           (fun uu____2480  ->
                                              match uu____2480 with
                                              | (bv,uu____2484) ->
                                                  let uu____2485 =
                                                    let uu____2486 =
                                                      let uu____2490 =
                                                        bv_as_unique_ident bv in
                                                      (uu____2490, None) in
                                                    FStar_Parser_AST.PatVar
                                                      uu____2486 in
                                                  mk_pat uu____2485)) in
                                    let uu____2492 =
                                      let uu____2495 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2495) in
                                    let uu____2497 =
                                      universe_to_string univs1 in
                                    (uu____2492, uu____2497)
                                  else
                                    (let uu____2501 =
                                       let uu____2504 = resugar_term term1 in
                                       (pat, uu____2504) in
                                     let uu____2505 =
                                       universe_to_string univs1 in
                                     (uu____2501, uu____2505))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 = FStar_List.map FStar_Pervasives.fst r in
             let comments = FStar_List.map FStar_Pervasives.snd r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2544) ->
        let s =
          let uu____2558 =
            let uu____2559 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2559 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2558 in
        let uu____2563 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2563
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___201_2573 =
          match uu___201_2573 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2574 =
                let uu____2575 = FStar_Syntax_Subst.compress e in
                uu____2575.FStar_Syntax_Syntax.n in
              (match uu____2574 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2601 =
                       let uu____2602 = FStar_Syntax_Subst.compress h in
                       uu____2602.FStar_Syntax_Syntax.n in
                     match uu____2601 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2609 = FStar_Syntax_Syntax.lid_of_fv fv in
                         (uu____2609, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2617 = aux h1 in
                         (match uu____2617 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2629 -> failwith "wrong Data_app head format" in
                   let uu____2633 = aux head1 in
                   (match uu____2633 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____2648 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos in
                               (uu____2648, FStar_Parser_AST.UnivApp))
                            universes in
                        let args1 =
                          FStar_List.map
                            (fun uu____2657  ->
                               match uu____2657 with
                               | (t1,uu____2663) ->
                                   let uu____2664 = resugar_term t1 in
                                   (uu____2664, FStar_Parser_AST.Nothing))
                            args in
                        let uu____2665 =
                          FStar_Syntax_Util.is_tuple_data_lid' head2 in
                        if uu____2665
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2670 = FStar_Options.print_universes () in
                           if uu____2670
                           then
                             mk1
                               (FStar_Parser_AST.Construct
                                  (head2,
                                    (FStar_List.append args1 universes1)))
                           else
                             mk1 (FStar_Parser_AST.Construct (head2, args1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____2680,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2686,uu____2687) -> resugar_term e
                    | uu____2692 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2693 -> failwith "wrong Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2699,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2715 =
                      let uu____2716 =
                        let uu____2721 = resugar_seq t11 in
                        (uu____2721, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2716 in
                    mk1 uu____2715
                | uu____2723 -> t1 in
              resugar_seq term
          | FStar_Syntax_Syntax.Primop 
            |FStar_Syntax_Syntax.Masked_effect 
             |FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term e
          | FStar_Syntax_Syntax.Mutable_alloc  ->
              let term = resugar_term e in
              (match term.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier ,l,t1)
                   ->
                   mk1
                     (FStar_Parser_AST.Let (FStar_Parser_AST.Mutable, l, t1))
               | uu____2736 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant None in
              let uu____2738 =
                let uu____2739 = FStar_Syntax_Subst.compress e in
                uu____2739.FStar_Syntax_Syntax.n in
              (match uu____2738 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2743;
                      FStar_Syntax_Syntax.pos = uu____2744;
                      FStar_Syntax_Syntax.vars = uu____2745;_},(term,uu____2747)::[])
                   -> resugar_term term
               | uu____2769 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2791  ->
                       match uu____2791 with
                       | (x,uu____2795) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2797,p) ->
             let uu____2799 =
               let uu____2800 =
                 let uu____2804 = resugar_term e in (uu____2804, l, p) in
               FStar_Parser_AST.Labeled uu____2800 in
             mk1 uu____2799
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1)
           |FStar_Syntax_Syntax.Meta_monadic_lift (name1,_,t1) ->
             let uu____2818 =
               let uu____2819 =
                 let uu____2824 = resugar_term e in
                 let uu____2825 =
                   let uu____2826 =
                     let uu____2827 =
                       let uu____2833 =
                         let uu____2837 =
                           let uu____2840 = resugar_term t1 in
                           (uu____2840, FStar_Parser_AST.Nothing) in
                         [uu____2837] in
                       (name1, uu____2833) in
                     FStar_Parser_AST.Construct uu____2827 in
                   mk1 uu____2826 in
                 (uu____2824, uu____2825, None) in
               FStar_Parser_AST.Ascribed uu____2819 in
             mk1 uu____2818)
    | FStar_Syntax_Syntax.Tm_unknown  -> mk1 FStar_Parser_AST.Wild
and resugar_comp: FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term =
  fun c  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (typ,u) ->
        let t = resugar_term typ in
        (match u with
         | None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Syntax_Const.effect_Tot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | Some u1 ->
             let uu____2871 = FStar_Options.print_universes () in
             if uu____2871
             then
               let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Syntax_Const.effect_Tot_lid,
                      [(u2, FStar_Parser_AST.UnivApp);
                      (t, FStar_Parser_AST.Nothing)]))
             else
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Syntax_Const.effect_Tot_lid,
                      [(t, FStar_Parser_AST.Nothing)])))
    | FStar_Syntax_Syntax.GTotal (typ,u) ->
        let t = resugar_term typ in
        (match u with
         | None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Syntax_Const.effect_GTot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | Some u1 ->
             let uu____2907 = FStar_Options.print_universes () in
             if uu____2907
             then
               let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Syntax_Const.effect_GTot_lid,
                      [(u2, FStar_Parser_AST.UnivApp);
                      (t, FStar_Parser_AST.Nothing)]))
             else
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Syntax_Const.effect_GTot_lid,
                      [(t, FStar_Parser_AST.Nothing)])))
    | FStar_Syntax_Syntax.Comp c1 ->
        let result =
          let uu____2930 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____2930, FStar_Parser_AST.Nothing) in
        let uu____2931 = FStar_Options.print_effect_args () in
        if uu____2931
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Syntax_Const.effect_Lemma_lid
            then
              let rec aux l uu___202_2971 =
                match uu___202_2971 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Syntax_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3013 -> aux l tl1
                     | uu____3018 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____3038  ->
                 match uu____3038 with
                 | (e,uu____3044) ->
                     let uu____3045 = resugar_term e in
                     (uu____3045, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___203_3059 =
            match uu___203_3059 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3079 = resugar_term e in
                       (uu____3079, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3082 -> aux l tl1) in
          let decrease = aux [] c1.FStar_Syntax_Syntax.flags in
          mk1
            (FStar_Parser_AST.Construct
               ((c1.FStar_Syntax_Syntax.effect_name),
                 (FStar_List.append (result :: decrease) args1)))
        else
          mk1
            (FStar_Parser_AST.Construct
               ((c1.FStar_Syntax_Syntax.effect_name), [result]))
and resugar_binder:
  FStar_Syntax_Syntax.binder -> FStar_Range.range -> FStar_Parser_AST.binder
  =
  fun b  ->
    fun r  ->
      let uu____3106 = b in
      match uu____3106 with
      | (x,imp) ->
          let e = resugar_term x.FStar_Syntax_Syntax.sort in
          (match e.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Wild  ->
               let uu____3110 =
                 let uu____3111 = bv_as_unique_ident x in
                 FStar_Parser_AST.Variable uu____3111 in
               FStar_Parser_AST.mk_binder uu____3110 r
                 FStar_Parser_AST.Type_level None
           | uu____3112 ->
               let uu____3113 = FStar_Syntax_Syntax.is_null_bv x in
               if uu____3113
               then
                 FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                   FStar_Parser_AST.Type_level None
               else
                 (let uu____3115 =
                    let uu____3116 =
                      let uu____3119 = bv_as_unique_ident x in
                      (uu____3119, e) in
                    FStar_Parser_AST.Annotated uu____3116 in
                  FStar_Parser_AST.mk_binder uu____3115 r
                    FStar_Parser_AST.Type_level None))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual -> FStar_Parser_AST.pattern option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3127 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3127 in
      let uu____3128 =
        let uu____3129 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3129.FStar_Syntax_Syntax.n in
      match uu____3128 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____3135 = mk1 FStar_Parser_AST.PatWild in Some uu____3135
          else
            (let uu____3137 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3137
               (fun aq  ->
                  let uu____3143 =
                    let uu____3144 =
                      let uu____3145 =
                        let uu____3149 = bv_as_unique_ident x in
                        (uu____3149, aq) in
                      FStar_Parser_AST.PatVar uu____3145 in
                    mk1 uu____3144 in
                  Some uu____3143))
      | uu____3151 ->
          let uu____3152 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3152
            (fun aq  ->
               let pat =
                 let uu____3159 =
                   let uu____3160 =
                     let uu____3164 = bv_as_unique_ident x in
                     (uu____3164, aq) in
                   FStar_Parser_AST.PatVar uu____3160 in
                 mk1 uu____3159 in
               let uu____3166 = FStar_Options.print_bound_var_types () in
               if uu____3166
               then
                 let uu____3168 =
                   let uu____3169 =
                     let uu____3170 =
                       let uu____3173 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3173) in
                     FStar_Parser_AST.PatAscribed uu____3170 in
                   mk1 uu____3169 in
                 Some uu____3168
               else Some pat)
and resugar_pat: FStar_Syntax_Syntax.pat -> FStar_Parser_AST.pattern =
  fun p  ->
    let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p in
    let rec aux p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant c ->
          mk1 (FStar_Parser_AST.PatConst c)
      | FStar_Syntax_Syntax.Pat_disj args ->
          let args1 = FStar_List.map (fun p2  -> aux p2) args in
          mk1 (FStar_Parser_AST.PatOr args1)
      | FStar_Syntax_Syntax.Pat_cons (fv,[]) ->
          mk1
            (FStar_Parser_AST.PatName
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
      | FStar_Syntax_Syntax.Pat_cons (fv,args) when
          FStar_Ident.lid_equals
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Syntax_Const.cons_lid
          ->
          let args1 =
            FStar_List.map
              (fun uu____3226  -> match uu____3226 with | (p2,b) -> aux p2)
              args in
          mk1 (FStar_Parser_AST.PatList args1)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) when
          (FStar_Syntax_Util.is_tuple_data_lid'
             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
            ||
            (FStar_Syntax_Util.is_dtuple_data_lid'
               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
          ->
          let args1 =
            FStar_List.map
              (fun uu____3255  -> match uu____3255 with | (p2,b) -> aux p2)
              args in
          let uu____3260 =
            FStar_Syntax_Util.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3260
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3268;
             FStar_Syntax_Syntax.fv_delta = uu____3269;
             FStar_Syntax_Syntax.fv_qual = Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3290 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3290 FStar_List.rev in
          let args1 =
            let uu____3299 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3309  ->
                      match uu____3309 with | (p2,b) -> aux p2)) in
            FStar_All.pipe_right uu____3299 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3351 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3351
            | (hd1::tl1,hd2::tl2) ->
                let uu____3365 = map21 tl1 tl2 in (hd1, hd2) :: uu____3365 in
          let args2 =
            let uu____3375 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3375 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3403  -> match uu____3403 with | (p2,b) -> aux p2)
              args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3414 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3414 with
           | Some (op,uu____3419) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | None  ->
               let uu____3424 =
                 let uu____3425 =
                   let uu____3429 = bv_as_unique_ident v1 in
                   (uu____3429, None) in
                 FStar_Parser_AST.PatVar uu____3425 in
               mk1 uu____3424)
      | FStar_Syntax_Syntax.Pat_wild uu____3431 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3439 =
              let uu____3440 =
                let uu____3444 = bv_as_unique_ident bv in (uu____3444, None) in
              FStar_Parser_AST.PatVar uu____3440 in
            mk1 uu____3439 in
          let uu____3446 = FStar_Options.print_bound_var_types () in
          if uu____3446
          then
            let uu____3447 =
              let uu____3448 =
                let uu____3451 = resugar_term term in (pat, uu____3451) in
              FStar_Parser_AST.PatAscribed uu____3448 in
            mk1 uu____3447
          else pat in
    aux p
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier -> FStar_Parser_AST.qualifier option =
  fun uu___204_3456  ->
    match uu___204_3456 with
    | FStar_Syntax_Syntax.Assumption  -> Some FStar_Parser_AST.Assumption
    | FStar_Syntax_Syntax.New  -> Some FStar_Parser_AST.New
    | FStar_Syntax_Syntax.Private  -> Some FStar_Parser_AST.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
        Some FStar_Parser_AST.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default  ->
        if true then None else Some FStar_Parser_AST.Visible
    | FStar_Syntax_Syntax.Irreducible  -> Some FStar_Parser_AST.Irreducible
    | FStar_Syntax_Syntax.Abstract  -> Some FStar_Parser_AST.Abstract
    | FStar_Syntax_Syntax.Inline_for_extraction  ->
        Some FStar_Parser_AST.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract  -> Some FStar_Parser_AST.NoExtract
    | FStar_Syntax_Syntax.Noeq  -> Some FStar_Parser_AST.Noeq
    | FStar_Syntax_Syntax.Unopteq  -> Some FStar_Parser_AST.Unopteq
    | FStar_Syntax_Syntax.TotalEffect  -> Some FStar_Parser_AST.TotalEffect
    | FStar_Syntax_Syntax.Logic  ->
        if true then None else Some FStar_Parser_AST.Logic
    | FStar_Syntax_Syntax.Reifiable  -> Some FStar_Parser_AST.Reifiable
    | FStar_Syntax_Syntax.Reflectable uu____3462 ->
        Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3463 -> None
    | FStar_Syntax_Syntax.Projector uu____3464 -> None
    | FStar_Syntax_Syntax.RecordType uu____3467 -> None
    | FStar_Syntax_Syntax.RecordConstructor uu____3472 -> None
    | FStar_Syntax_Syntax.Action uu____3477 -> None
    | FStar_Syntax_Syntax.ExceptionConstructor  -> None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> None
    | FStar_Syntax_Syntax.Effect  -> Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___205_3480  ->
    match uu___205_3480 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.LightOff  -> FStar_Parser_AST.LightOff
let resugar_typ:
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelts* FStar_Parser_AST.tycon)
  =
  fun datacon_ses  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (tylid,uvs,bs,t,uu____3502,datacons) ->
          let uu____3508 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3519,uu____3520,uu____3521,inductive_lid,uu____3523,uu____3524)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3527 -> failwith "unexpected")) in
          (match uu____3508 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3538 = FStar_Options.print_implicits () in
                 if uu____3538 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____3545 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___206_3547  ->
                           match uu___206_3547 with
                           | FStar_Syntax_Syntax.RecordType uu____3548 ->
                               true
                           | uu____3553 -> false)) in
                 if uu____3545
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____3581,univs1,term,uu____3584,num,uu____3586)
                         ->
                         let uu____3589 =
                           let uu____3590 = FStar_Syntax_Subst.compress term in
                           uu____3590.FStar_Syntax_Syntax.n in
                         (match uu____3589 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3599) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3630  ->
                                        match uu____3630 with
                                        | (b,qual) ->
                                            let uu____3639 =
                                              let uu____3640 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3640 in
                                            let uu____3641 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____3639, uu____3641, None))) in
                              FStar_List.append mfields fields
                          | uu____3647 -> failwith "unexpected")
                     | uu____3653 -> failwith "unexpected" in
                   let fields =
                     FStar_List.fold_left resugar_datacon_as_fields []
                       current_datacons in
                   FStar_Parser_AST.TyconRecord
                     ((tylid.FStar_Ident.ident), bs2, None, fields)
                 else
                   (let resugar_datacon constructors se1 =
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (l,univs1,term,uu____3720,num,uu____3722) ->
                          let c =
                            let uu____3732 =
                              let uu____3734 = resugar_term term in
                              Some uu____3734 in
                            ((l.FStar_Ident.ident), uu____3732, None, false) in
                          c :: constructors
                      | uu____3743 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2, None, constructors)) in
               (other_datacons, tyc))
      | uu____3782 ->
          failwith
            "Impossible : only Sig_inductive_typ can be resugared as types"
let mk_decl:
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Parser_AST.decl' -> FStar_Parser_AST.decl
  =
  fun r  ->
    fun q  ->
      fun d'  ->
        let uu____3796 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = None;
          FStar_Parser_AST.quals = uu____3796;
          FStar_Parser_AST.attrs = []
        }
let decl'_to_decl:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl' -> FStar_Parser_AST.decl
  =
  fun se  ->
    fun d'  ->
      mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals
        d'
let resugar_tscheme':
  Prims.string -> FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl =
  fun name  ->
    fun ts  ->
      let uu____3809 = ts in
      match uu____3809 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____3815 =
            let uu____3816 =
              let uu____3823 =
                let uu____3828 =
                  let uu____3832 =
                    let uu____3833 =
                      let uu____3840 = resugar_term typ in
                      (name1, [], None, uu____3840) in
                    FStar_Parser_AST.TyconAbbrev uu____3833 in
                  (uu____3832, None) in
                [uu____3828] in
              (false, uu____3823) in
            FStar_Parser_AST.Tycon uu____3816 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____3815
let resugar_tscheme: FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl =
  fun ts  -> resugar_tscheme' "tsheme" ts
let resugar_eff_decl:
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let resugar_action d for_free1 =
            let action_params =
              FStar_Syntax_Subst.open_binders
                d.FStar_Syntax_Syntax.action_params in
            let uu____3879 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____3879 with
            | (bs,action_defn) ->
                let uu____3884 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____3884 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____3890 = FStar_Options.print_implicits () in
                       if uu____3890
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____3894 =
                         FStar_All.pipe_right action_params1
                           (FStar_List.map (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____3894 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____3903 =
                           let uu____3909 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____3909,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____3903 in
                       let t =
                         FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un in
                       mk_decl r q
                         (FStar_Parser_AST.Tycon
                            (false,
                              [((FStar_Parser_AST.TyconAbbrev
                                   (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                     action_params2, None, t)), None)]))
                     else
                       mk_decl r q
                         (FStar_Parser_AST.Tycon
                            (false,
                              [((FStar_Parser_AST.TyconAbbrev
                                   (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                     action_params2, None, action_defn1)),
                                 None)]))) in
          let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident in
          let uu____3948 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____3948 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____3954 = FStar_Options.print_implicits () in
                if uu____3954 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____3958 =
                  FStar_All.pipe_right eff_binders1
                    (FStar_List.map (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____3958 FStar_List.rev in
              let eff_typ1 = resugar_term eff_typ in
              let ret_wp =
                resugar_tscheme' "ret_wp" ed.FStar_Syntax_Syntax.ret_wp in
              let bind_wp =
                resugar_tscheme' "bind_wp" ed.FStar_Syntax_Syntax.ret_wp in
              let if_then_else1 =
                resugar_tscheme' "if_then_else"
                  ed.FStar_Syntax_Syntax.if_then_else in
              let ite_wp =
                resugar_tscheme' "ite_wp" ed.FStar_Syntax_Syntax.ite_wp in
              let stronger =
                resugar_tscheme' "stronger" ed.FStar_Syntax_Syntax.stronger in
              let close_wp =
                resugar_tscheme' "close_wp" ed.FStar_Syntax_Syntax.close_wp in
              let assert_p =
                resugar_tscheme' "assert_p" ed.FStar_Syntax_Syntax.assert_p in
              let assume_p =
                resugar_tscheme' "assume_p" ed.FStar_Syntax_Syntax.assume_p in
              let null_wp =
                resugar_tscheme' "null_wp" ed.FStar_Syntax_Syntax.null_wp in
              let trivial =
                resugar_tscheme' "trivial" ed.FStar_Syntax_Syntax.trivial in
              let repr =
                resugar_tscheme' "repr" ([], (ed.FStar_Syntax_Syntax.repr)) in
              let return_repr =
                resugar_tscheme' "return_repr"
                  ed.FStar_Syntax_Syntax.return_repr in
              let bind_repr =
                resugar_tscheme' "bind_repr" ed.FStar_Syntax_Syntax.bind_repr in
              let mandatory_members_decls =
                if for_free
                then [repr; return_repr; bind_repr]
                else
                  [repr;
                  return_repr;
                  bind_repr;
                  ret_wp;
                  bind_wp;
                  if_then_else1;
                  ite_wp;
                  stronger;
                  close_wp;
                  assert_p;
                  assume_p;
                  null_wp;
                  trivial] in
              let actions =
                FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions
                  (FStar_List.map (fun a  -> resugar_action a false)) in
              let decls = FStar_List.append mandatory_members_decls actions in
              mk_decl r q
                (FStar_Parser_AST.NewEffect
                   (FStar_Parser_AST.DefineEffect
                      (eff_name, eff_binders2, eff_typ1, decls)))
let resugar_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Parser_AST.decl option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3999) ->
        let uu____4004 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ _
                    |FStar_Syntax_Syntax.Sig_declare_typ _ -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4017 -> false
                  | uu____4025 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____4004 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4045 se1 =
               match uu____4045 with
               | (datacon_ses1,tycons) ->
                   let uu____4060 = resugar_typ datacon_ses1 se1 in
                   (match uu____4060 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4069 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4069 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4088 =
                         let uu____4089 =
                           let uu____4090 =
                             let uu____4097 =
                               FStar_List.map (fun tyc  -> (tyc, None))
                                 tycons in
                             (false, uu____4097) in
                           FStar_Parser_AST.Tycon uu____4090 in
                         decl'_to_decl se uu____4089 in
                       Some uu____4088
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4114,uu____4115,uu____4116,uu____4117,uu____4118)
                            ->
                            let uu____4121 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident), None)) in
                            Some uu____4121
                        | uu____4123 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4125 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4129,attrs) ->
        let uu____4135 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___207_4137  ->
                  match uu___207_4137 with
                  | FStar_Syntax_Syntax.Projector (_,_)
                    |FStar_Syntax_Syntax.Discriminator _ -> true
                  | uu____4141 -> false)) in
        if uu____4135
        then None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e None se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____4166) ->
               let uu____4173 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               Some uu____4173
           | uu____4177 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,fml) ->
        let uu____4181 =
          let uu____4182 =
            let uu____4183 =
              let uu____4186 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4186) in
            FStar_Parser_AST.Assume uu____4183 in
          decl'_to_decl se uu____4182 in
        Some uu____4181
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4188 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4188
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4190 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4190
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | Some (uu____4197,t) ->
              let uu____4204 = resugar_term t in Some uu____4204
          | uu____4205 -> None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | Some (uu____4210,t) ->
              let uu____4217 = resugar_term t in Some uu____4217
          | uu____4218 -> None in
        let op =
          match (lift_wp, lift) with
          | (Some t,None ) -> FStar_Parser_AST.NonReifiableLift t
          | (Some wp,Some t) -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (None ,Some t) -> FStar_Parser_AST.LiftForFree t
          | uu____4233 -> failwith "Should not happen hopefully" in
        let uu____4238 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        Some uu____4238
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4246 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4246 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4253 = FStar_Options.print_implicits () in
               if uu____4253 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (FStar_List.map
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____4259 =
               let uu____4260 =
                 let uu____4261 =
                   let uu____4268 =
                     let uu____4273 =
                       let uu____4277 =
                         let uu____4278 =
                           let uu____4285 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3, None, uu____4285) in
                         FStar_Parser_AST.TyconAbbrev uu____4278 in
                       (uu____4277, None) in
                     [uu____4273] in
                   (false, uu____4268) in
                 FStar_Parser_AST.Tycon uu____4261 in
               decl'_to_decl se uu____4260 in
             Some uu____4259)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4300 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        Some uu____4300
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4304 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___208_4306  ->
                  match uu___208_4306 with
                  | FStar_Syntax_Syntax.Projector (_,_)
                    |FStar_Syntax_Syntax.Discriminator _ -> true
                  | uu____4310 -> false)) in
        if uu____4304
        then None
        else
          (let uu____4313 =
             let uu____4314 =
               let uu____4315 =
                 let uu____4318 = resugar_term t in
                 ((lid.FStar_Ident.ident), uu____4318) in
               FStar_Parser_AST.Val uu____4315 in
             decl'_to_decl se uu____4314 in
           Some uu____4313)
    | FStar_Syntax_Syntax.Sig_inductive_typ _
      |FStar_Syntax_Syntax.Sig_datacon _|FStar_Syntax_Syntax.Sig_main _ ->
        None