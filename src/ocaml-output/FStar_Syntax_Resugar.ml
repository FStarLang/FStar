open Prims
let bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name =
      if
        FStar_Util.starts_with FStar_Ident.reserved_prefix
          (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      then
        let uu____5 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____5
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___198_37  ->
          match uu___198_37 with
          | (uu____41,Some (FStar_Syntax_Syntax.Implicit uu____42)) -> false
          | uu____44 -> true))
  
let resugar_arg_qual :
  FStar_Syntax_Syntax.arg_qualifier Prims.option ->
    FStar_Parser_AST.arg_qualifier Prims.option
  =
  fun q  ->
    match q with
    | None  -> None
    | Some (FStar_Syntax_Syntax.Implicit b) -> Some FStar_Parser_AST.Implicit
    | Some (FStar_Syntax_Syntax.Equality ) -> Some FStar_Parser_AST.Equality
  
let rec universe_to_int :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe)
  =
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____68 -> (n1, u)
  
let rec resugar_universe :
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un  in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1 (FStar_Parser_AST.Const (FStar_Const.Const_int ("0", None))) r
      | FStar_Syntax_Syntax.U_succ uu____87 ->
          let uu____88 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____88 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____93 =
                      let uu____94 =
                        let uu____95 =
                          let uu____101 = FStar_Util.string_of_int n1  in
                          (uu____101, None)  in
                        FStar_Const.Const_int uu____95  in
                      FStar_Parser_AST.Const uu____94  in
                    mk1 uu____93 r
                | uu____107 ->
                    let e1 =
                      let uu____109 =
                        let uu____110 =
                          let uu____111 =
                            let uu____117 = FStar_Util.string_of_int n1  in
                            (uu____117, None)  in
                          FStar_Const.Const_int uu____111  in
                        FStar_Parser_AST.Const uu____110  in
                      mk1 uu____109 r  in
                    let e2 = resugar_universe u1 r  in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____127 ->
               let t =
                 let uu____130 =
                   let uu____131 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____131  in
                 mk1 uu____130 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____134 =
                        let uu____135 =
                          let uu____139 = resugar_universe x r  in
                          (acc, uu____139, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____135  in
                      mk1 uu____134 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____141 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____146 =
              let uu____149 =
                let uu____150 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____150  in
              (uu____149, r)  in
            FStar_Ident.mk_ident uu____146  in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
  
let string_to_op : Prims.string -> Prims.string Prims.option =
  fun s  ->
    let name_of_op uu___199_159 =
      match uu___199_159 with
      | "Amp" -> Some "&"
      | "At" -> Some "@"
      | "Plus" -> Some "+"
      | "Minus" -> Some "-"
      | "Subtraction" -> Some "-"
      | "Slash" -> Some "/"
      | "Less" -> Some "<"
      | "Equals" -> Some "="
      | "Greater" -> Some ">"
      | "Underscore" -> Some "_"
      | "Bar" -> Some "|"
      | "Bang" -> Some "!"
      | "Hat" -> Some "^"
      | "Percent" -> Some "%"
      | "Star" -> Some "*"
      | "Question" -> Some "?"
      | "Colon" -> Some ":"
      | uu____161 -> None  in
    match s with
    | "op_String_Assignment" -> Some ".[]<-"
    | "op_Array_Assignment" -> Some ".()<-"
    | "op_String_Access" -> Some ".[]"
    | "op_Array_Access" -> Some ".()"
    | uu____163 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____167 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____167 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____172 ->
               let op =
                 let uu____175 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | Some op -> Prims.strcat acc op
                        | None  -> failwith "wrong composed operator format")
                   "" uu____175
                  in
               Some op)
        else None
  
let rec resugar_term_as_op :
  FStar_Syntax_Syntax.term -> Prims.string Prims.option =
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
      (FStar_Syntax_Const.salloc_lid, "alloc")]  in
    let fallback fv =
      let uu____267 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  -> FStar_Syntax_Syntax.fv_eq_lid fv (Prims.fst d)))
         in
      match uu____267 with
      | Some op -> Some (Prims.snd op)
      | uu____288 ->
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let str =
            if length1 = (Prims.parse_int "0")
            then
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
            else
              FStar_Util.substring_from
                ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                (length1 + (Prims.parse_int "1"))
             in
          if FStar_Util.starts_with str "dtuple"
          then Some "dtuple"
          else
            if FStar_Util.starts_with str "tuple"
            then Some "tuple"
            else
              if FStar_Util.starts_with str "try_with"
              then Some "try_with"
              else
                (let uu____319 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.sread_lid
                    in
                 if uu____319
                 then
                   Some
                     (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str)
                 else None)
       in
    let uu____326 =
      let uu____327 = FStar_Syntax_Subst.compress t  in
      uu____327.FStar_Syntax_Syntax.n  in
    match uu____326 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
           in
        let s =
          if length1 = (Prims.parse_int "0")
          then
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          else
            FStar_Util.substring_from
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
              (length1 + (Prims.parse_int "1"))
           in
        let uu____353 = string_to_op s  in
        (match uu____353 with | Some t1 -> Some t1 | uu____357 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____365 -> None
  
let is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____369 -> false
  
let is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____373 -> true
    | uu____374 -> false
  
let rec resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un
       in
    let name a r =
      let uu____401 = FStar_Ident.lid_of_path [a] r  in
      FStar_Parser_AST.Name uu____401  in
    let var a r =
      let uu____409 = FStar_Ident.lid_of_path [a] r  in
      FStar_Parser_AST.Var uu____409  in
    let uu____410 =
      let uu____411 = FStar_Syntax_Subst.compress t  in
      uu____411.FStar_Syntax_Syntax.n  in
    match uu____410 with
    | FStar_Syntax_Syntax.Tm_delayed uu____414 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____437 =
            let uu____439 = bv_as_unique_ident x  in [uu____439]  in
          FStar_Ident.lid_of_ids uu____437  in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____442 =
            let uu____444 = bv_as_unique_ident x  in [uu____444]  in
          FStar_Ident.lid_of_ids uu____442  in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
           in
        let s =
          if length1 = (Prims.parse_int "0")
          then a.FStar_Ident.str
          else
            FStar_Util.substring_from a.FStar_Ident.str
              (length1 + (Prims.parse_int "1"))
           in
        let is_prefix = Prims.strcat FStar_Ident.reserved_prefix "is_"  in
        if FStar_Util.starts_with s is_prefix
        then
          let rest =
            FStar_Util.substring_from s (FStar_String.length is_prefix)  in
          let uu____468 =
            let uu____469 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
            FStar_Parser_AST.Discrim uu____469  in
          mk1 uu____468
        else
          if
            FStar_Util.starts_with s FStar_Syntax_Util.field_projector_prefix
          then
            (let rest =
               FStar_Util.substring_from s
                 (FStar_String.length
                    FStar_Syntax_Util.field_projector_prefix)
                in
             let r =
               FStar_Util.split rest FStar_Syntax_Util.field_projector_sep
                in
             match r with
             | fst1::snd1::[] ->
                 let l =
                   FStar_Ident.lid_of_path [fst1] t.FStar_Syntax_Syntax.pos
                    in
                 let r1 =
                   FStar_Ident.mk_ident (snd1, (t.FStar_Syntax_Syntax.pos))
                    in
                 mk1 (FStar_Parser_AST.Projector (l, r1))
             | uu____480 -> failwith "wrong projector format")
          else
            (let uu____483 =
               ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid))
                 ||
                 (let uu____484 =
                    let uu____485 = FStar_String.get s (Prims.parse_int "0")
                       in
                    FStar_Char.uppercase uu____485  in
                  let uu____486 = FStar_String.get s (Prims.parse_int "0")
                     in
                  uu____484 <> uu____486)
                in
             if uu____483
             then
               let uu____487 = var s t.FStar_Syntax_Syntax.pos  in
               mk1 uu____487
             else
               (let uu____489 = name s t.FStar_Syntax_Syntax.pos  in
                mk1 uu____489))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____496 = FStar_Options.print_universes ()  in
        if uu____496
        then
          let e1 = resugar_term e  in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____500 =
                   let uu____501 =
                     let uu____505 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos  in
                     (acc, uu____505, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____501  in
                 mk1 uu____500) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____508 = FStar_Syntax_Syntax.is_teff t  in
        if uu____508
        then
          let uu____509 = name "Effect" t.FStar_Syntax_Syntax.pos  in
          mk1 uu____509
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____512 = name "Type0" t.FStar_Syntax_Syntax.pos  in
             mk1 uu____512
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____513 = name "Type" t.FStar_Syntax_Syntax.pos  in
             mk1 uu____513
         | uu____514 ->
             let uu____515 = FStar_Options.print_universes ()  in
             if uu____515
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos  in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos
                  in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____526 = name "Type" t.FStar_Syntax_Syntax.pos  in
                mk1 uu____526))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____529) ->
        let uu____552 = FStar_Syntax_Subst.open_term xs body  in
        (match uu____552 with
         | (xs1,body1) ->
             let xs2 =
               let uu____558 = FStar_Options.print_implicits ()  in
               if uu____558 then xs1 else filter_imp xs1  in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.map
                    (fun uu____565  ->
                       match uu____565 with
                       | (x,qual) -> resugar_bv_as_pat x qual))
                in
             let body2 = resugar_term body1  in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____584 = FStar_Syntax_Subst.open_comp xs body  in
        (match uu____584 with
         | (xs1,body1) ->
             let xs2 =
               let uu____590 = FStar_Options.print_implicits ()  in
               if uu____590 then xs1 else filter_imp xs1  in
             let body2 = resugar_comp body1  in
             let xs3 =
               let uu____595 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun uu____600  ->
                         match uu____600 with
                         | (b,qual) ->
                             resugar_bv_as_binder b t.FStar_Syntax_Syntax.pos))
                  in
               FStar_All.pipe_right uu____595 FStar_List.rev  in
             let rec aux body3 uu___200_614 =
               match uu___200_614 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3))
                      in
                   aux body4 tl1
                in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____627 =
          let uu____630 =
            let uu____631 = FStar_Syntax_Syntax.mk_binder x  in [uu____631]
             in
          FStar_Syntax_Subst.open_term uu____630 phi  in
        (match uu____627 with
         | (x1,phi1) ->
             let uu____634 = FStar_List.hd x1  in
             (match uu____634 with
              | (b,uu____640) ->
                  let b1 = resugar_bv_as_binder b t.FStar_Syntax_Syntax.pos
                     in
                  let uu____642 =
                    let uu____643 =
                      let uu____646 = resugar_term phi1  in (b1, uu____646)
                       in
                    FStar_Parser_AST.Refine uu____643  in
                  mk1 uu____642))
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___201_676 =
          match uu___201_676 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____723 -> failwith "last of an empty list"  in
        let rec last_two uu___202_747 =
          match uu___202_747 with
          | []|_::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____810::t1 -> last_two t1  in
        let rec last_three uu___203_838 =
          match uu___203_838 with
          | []|_::[]|_::_::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____928::t1 -> last_three t1  in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____964  ->
                    match uu____964 with | (e2,qual) -> resugar_term e2))
             in
          let e2 = resugar_term e1  in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 mk1
                   (FStar_Parser_AST.App (acc, x, FStar_Parser_AST.Nothing)))
            e2 args2
           in
        let args1 =
          let uu____978 = FStar_Options.print_implicits ()  in
          if uu____978 then args else filter_imp args  in
        let uu____987 = resugar_term_as_op e  in
        (match uu____987 with
         | None  -> resugar_as_app e args1
         | Some "tuple" ->
             (match args1 with
              | (fst1,uu____990)::(snd1,uu____992)::rest ->
                  let e1 =
                    let uu____1016 =
                      let uu____1017 =
                        let uu____1021 =
                          let uu____1023 = resugar_term fst1  in
                          let uu____1024 =
                            let uu____1026 = resugar_term snd1  in
                            [uu____1026]  in
                          uu____1023 :: uu____1024  in
                        ((FStar_Ident.id_of_text "*"), uu____1021)  in
                      FStar_Parser_AST.Op uu____1017  in
                    mk1 uu____1016  in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1031  ->
                         match uu____1031 with
                         | (x,uu____1035) ->
                             let uu____1036 =
                               let uu____1037 =
                                 let uu____1041 =
                                   let uu____1043 =
                                     let uu____1045 = resugar_term x  in
                                     [uu____1045]  in
                                   e1 :: uu____1043  in
                                 ((FStar_Ident.id_of_text "*"), uu____1041)
                                  in
                               FStar_Parser_AST.Op uu____1037  in
                             mk1 uu____1036) e1 rest
              | uu____1047 -> resugar_as_app e args1)
         | Some "dtuple" when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1  in
             let body =
               match args2 with
               | (b,uu____1072)::[] -> b
               | uu____1085 -> failwith "wrong arguments to dtuple"  in
             let uu____1093 =
               let uu____1094 = FStar_Syntax_Subst.compress body  in
               uu____1094.FStar_Syntax_Syntax.n  in
             (match uu____1093 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1099) ->
                  let uu____1122 = FStar_Syntax_Subst.open_term xs body1  in
                  (match uu____1122 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1128 = FStar_Options.print_implicits ()
                            in
                         if uu____1128 then xs1 else filter_imp xs1  in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (FStar_List.map
                              (fun uu____1135  ->
                                 match uu____1135 with
                                 | (b,qual) ->
                                     resugar_bv_as_binder b
                                       t.FStar_Syntax_Syntax.pos))
                          in
                       let body3 = resugar_term body2  in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1142 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1153  ->
                            match uu____1153 with
                            | (e1,qual) -> resugar_term e1))
                     in
                  let e1 = resugar_term e  in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | Some "dtuple" -> resugar_as_app e args1
         | Some ref_read when
             ref_read = FStar_Syntax_Const.sread_lid.FStar_Ident.str ->
             let uu____1162 = FStar_List.hd args1  in
             (match uu____1162 with
              | (t1,uu____1172) ->
                  let uu____1177 =
                    let uu____1178 = FStar_Syntax_Subst.compress t1  in
                    uu____1178.FStar_Syntax_Syntax.n  in
                  (match uu____1177 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____1191 =
                         let uu____1192 =
                           let uu____1195 = resugar_term t1  in
                           (uu____1195, f)  in
                         FStar_Parser_AST.Project uu____1192  in
                       mk1 uu____1191
                   | uu____1196 -> resugar_term t1))
         | Some "try_with" when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1  in
             let uu____1210 =
               match new_args with
               | (a1,uu____1224)::(a2,uu____1226)::[] -> (a1, a2)
               | uu____1251 -> failwith "wrong arguments to try_with"  in
             (match uu____1210 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1277 =
                      let uu____1278 = FStar_Syntax_Subst.compress term  in
                      uu____1278.FStar_Syntax_Syntax.n  in
                    match uu____1277 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1283) ->
                        let uu____1306 = FStar_Syntax_Subst.open_term x e1
                           in
                        (match uu____1306 with | (x1,e2) -> e2)
                    | uu____1311 ->
                        failwith "wrong argument format to try_with"
                     in
                  let body1 =
                    let uu____1313 = decomp body  in resugar_term uu____1313
                     in
                  let handler1 =
                    let uu____1315 = decomp handler  in
                    resugar_term uu____1315  in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1321,uu____1322,b)::[]) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1344 =
                          let uu____1345 =
                            let uu____1350 = resugar_body t11  in
                            (uu____1350, t2, t3)  in
                          FStar_Parser_AST.Ascribed uu____1345  in
                        mk1 uu____1344
                    | uu____1352 ->
                        failwith "unexpected body format to try_with"
                     in
                  let e1 = resugar_body body1  in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1385 -> []  in
                  let branches = resugar_branches handler1  in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | Some "try_with" -> resugar_as_app e args1
         | Some op when (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body)|FStar_Parser_AST.QForall
                 (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1446 -> (xs, pat, t1)  in
             let resugar body =
               let uu____1454 =
                 let uu____1455 = FStar_Syntax_Subst.compress body  in
                 uu____1455.FStar_Syntax_Syntax.n  in
               match uu____1454 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1460) ->
                   let uu____1483 = FStar_Syntax_Subst.open_term xs body1  in
                   (match uu____1483 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1489 = FStar_Options.print_implicits ()
                             in
                          if uu____1489 then xs1 else filter_imp xs1  in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (FStar_List.map
                               (fun uu____1496  ->
                                  match uu____1496 with
                                  | (b,qual) ->
                                      resugar_bv_as_binder b
                                        t.FStar_Syntax_Syntax.pos))
                           in
                        let uu____1501 =
                          let uu____1506 =
                            let uu____1507 =
                              FStar_Syntax_Subst.compress body2  in
                            uu____1507.FStar_Syntax_Syntax.n  in
                          match uu____1506 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1  in
                              let resugar_pats pats =
                                FStar_List.map
                                  (fun es  ->
                                     FStar_All.pipe_right es
                                       (FStar_List.map
                                          (fun uu____1549  ->
                                             match uu____1549 with
                                             | (e2,uu____1553) ->
                                                 resugar_term e2))) pats
                                 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    resugar_pats pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1568) ->
                                    let uu____1569 =
                                      let uu____1571 =
                                        let uu____1572 = name s r  in
                                        mk1 uu____1572  in
                                      [uu____1571]  in
                                    [uu____1569]
                                | uu____1575 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists"
                                 in
                              (pats, body3)
                          | uu____1580 ->
                              let uu____1581 = resugar_term body2  in
                              ([], uu____1581)
                           in
                        (match uu____1501 with
                         | (pats,body3) ->
                             let uu____1591 = uncurry xs3 pats body3  in
                             (match uu____1591 with
                              | (xs4,pats1,body4) ->
                                  let xs5 =
                                    FStar_All.pipe_right xs4 FStar_List.rev
                                     in
                                  if op = "forall"
                                  then
                                    mk1
                                      (FStar_Parser_AST.QForall
                                         (xs5, pats1, body4))
                                  else
                                    mk1
                                      (FStar_Parser_AST.QExists
                                         (xs5, pats1, body4)))))
               | uu____1618 ->
                   if op = "forall"
                   then
                     let uu____1619 =
                       let uu____1620 =
                         let uu____1627 = resugar_term body  in
                         ([], [[]], uu____1627)  in
                       FStar_Parser_AST.QForall uu____1620  in
                     mk1 uu____1619
                   else
                     (let uu____1634 =
                        let uu____1635 =
                          let uu____1642 = resugar_term body  in
                          ([], [[]], uu____1642)  in
                        FStar_Parser_AST.QExists uu____1635  in
                      mk1 uu____1634)
                in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1  in
               (match args2 with
                | (b,uu____1662)::[] -> resugar b
                | uu____1675 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | Some "alloc" ->
             let uu____1682 = FStar_List.hd args1  in
             (match uu____1682 with | (e1,uu____1692) -> resugar_term e1)
         | Some op ->
             let op1 = FStar_Ident.id_of_text op  in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1716  ->
                       match uu____1716 with | (e1,qual) -> resugar_term e1))
                in
             let uu____1721 =
               FStar_Parser_ToDocument.handleable_args_length op1  in
             (match uu____1721 with
              | _0_27 when
                  (_0_27 = (Prims.parse_int "1")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "0"))
                  ->
                  let uu____1729 =
                    let uu____1730 =
                      let uu____1734 =
                        let uu____1736 = last1 args1  in resugar uu____1736
                         in
                      (op1, uu____1734)  in
                    FStar_Parser_AST.Op uu____1730  in
                  mk1 uu____1729
              | _0_28 when
                  (_0_28 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____1748 =
                    let uu____1749 =
                      let uu____1753 =
                        let uu____1755 = last_two args1  in
                        resugar uu____1755  in
                      (op1, uu____1753)  in
                    FStar_Parser_AST.Op uu____1749  in
                  mk1 uu____1748
              | _0_29 when
                  (_0_29 = (Prims.parse_int "3")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "2"))
                  ->
                  let uu____1767 =
                    let uu____1768 =
                      let uu____1772 =
                        let uu____1774 = last_three args1  in
                        resugar uu____1774  in
                      (op1, uu____1772)  in
                    FStar_Parser_AST.Op uu____1768  in
                  mk1 uu____1767
              | uu____1779 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____1782,t1)::(pat2,uu____1785,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____1860 =
          let uu____1861 =
            let uu____1865 = resugar_term e  in
            let uu____1866 = resugar_term t1  in
            let uu____1867 = resugar_term t2  in
            (uu____1865, uu____1866, uu____1867)  in
          FStar_Parser_AST.If uu____1861  in
        mk1 uu____1860
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____1907 =
          match uu____1907 with
          | (pat,wopt,b) ->
              let pat1 = resugar_match_pat pat  in
              let wopt1 =
                match wopt with
                | None  -> None
                | Some e1 ->
                    let uu____1926 = resugar_term e1  in Some uu____1926
                 in
              let b1 = resugar_term b  in (pat1, wopt1, b1)
           in
        let uu____1929 =
          let uu____1930 =
            let uu____1938 = resugar_term e  in
            let uu____1939 = FStar_List.map resugar_branch branches  in
            (uu____1938, uu____1939)  in
          FStar_Parser_AST.Match uu____1930  in
        mk1 uu____1929
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____1961) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1  in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt  in
        let uu____2014 =
          let uu____2015 =
            let uu____2020 = resugar_term e  in (uu____2020, term, tac_opt1)
             in
          FStar_Parser_AST.Ascribed uu____2015  in
        mk1 uu____2014
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
        let uu____2038 = FStar_Syntax_Subst.open_let_rec bnds body  in
        (match uu____2038 with
         | (bnd,body1) ->
             let resugar_one_binding bnd1 =
               let uu____2054 =
                 let uu____2057 =
                   FStar_Syntax_Util.mk_conj bnd1.FStar_Syntax_Syntax.lbtyp
                     bnd1.FStar_Syntax_Syntax.lbdef
                    in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd1.FStar_Syntax_Syntax.lbunivs uu____2057
                  in
               match uu____2054 with
               | (univs1,td) ->
                   let uu____2064 =
                     let uu____2071 =
                       let uu____2072 = FStar_Syntax_Subst.compress td  in
                       uu____2072.FStar_Syntax_Syntax.n  in
                     match uu____2071 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2081,(t1,uu____2083)::(d,uu____2085)::[]) ->
                         (t1, d)
                     | uu____2119 -> failwith "wrong let binding format"  in
                   (match uu____2064 with
                    | (typ,def) ->
                        let uu____2140 =
                          let uu____2144 =
                            let uu____2145 = FStar_Syntax_Subst.compress def
                               in
                            uu____2145.FStar_Syntax_Syntax.n  in
                          match uu____2144 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2153) ->
                              let uu____2176 =
                                FStar_Syntax_Subst.open_term b t1  in
                              (match uu____2176 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2185 =
                                       FStar_Options.print_implicits ()  in
                                     if uu____2185 then b1 else filter_imp b1
                                      in
                                   (b2, t2, true))
                          | uu____2187 -> ([], def, false)  in
                        (match uu____2140 with
                         | (binders,term,is_pat_app) ->
                             let universe_to_string univs2 =
                               let uu____2208 =
                                 FStar_Options.print_universes ()  in
                               if uu____2208
                               then
                                 let uu____2209 =
                                   FStar_List.map
                                     (fun x  -> x.FStar_Ident.idText) univs2
                                    in
                                 FStar_All.pipe_right uu____2209
                                   (FStar_String.concat ", ")
                               else ""  in
                             let uu____2214 =
                               match bnd1.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2225 =
                                     let uu____2228 =
                                       let uu____2229 =
                                         FStar_Syntax_Syntax.mk_binder bv  in
                                       [uu____2229]  in
                                     FStar_Syntax_Subst.open_term uu____2228
                                       term
                                      in
                                   (match uu____2225 with
                                    | (x,term1) ->
                                        let uu____2234 = FStar_List.hd x  in
                                        (match uu____2234 with
                                         | (bv1,uu____2242) ->
                                             let uu____2243 =
                                               let uu____2244 =
                                                 let uu____2245 =
                                                   let uu____2249 =
                                                     bv_as_unique_ident bv1
                                                      in
                                                   (uu____2249, None)  in
                                                 FStar_Parser_AST.PatVar
                                                   uu____2245
                                                  in
                                               mk_pat uu____2244  in
                                             (uu____2243, term1)))
                                in
                             (match uu____2214 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (FStar_List.map
                                           (fun uu____2266  ->
                                              match uu____2266 with
                                              | (bv,uu____2270) ->
                                                  let uu____2271 =
                                                    let uu____2272 =
                                                      let uu____2276 =
                                                        bv_as_unique_ident bv
                                                         in
                                                      (uu____2276, None)  in
                                                    FStar_Parser_AST.PatVar
                                                      uu____2272
                                                     in
                                                  mk_pat uu____2271))
                                       in
                                    let uu____2278 =
                                      let uu____2281 = resugar_term term1  in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2281)
                                       in
                                    let uu____2283 =
                                      universe_to_string univs1  in
                                    (uu____2278, uu____2283)
                                  else
                                    (let uu____2287 =
                                       let uu____2290 = resugar_term term1
                                          in
                                       (pat, uu____2290)  in
                                     let uu____2291 =
                                       universe_to_string univs1  in
                                     (uu____2287, uu____2291)))))
                in
             let r = FStar_List.map resugar_one_binding bnds  in
             let bnds1 = FStar_List.map Prims.fst r  in
             let comments = FStar_List.map Prims.snd r  in
             let body2 = resugar_term body1  in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds1, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2330) ->
        let s =
          let uu____2344 =
            let uu____2345 = FStar_Unionfind.uvar_id u  in
            FStar_All.pipe_right uu____2345 FStar_Util.string_of_int  in
          Prims.strcat "uu___unification_ " uu____2344  in
        let uu____2349 = var s t.FStar_Syntax_Syntax.pos  in mk1 uu____2349
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___204_2359 =
          match uu___204_2359 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2360 =
                let uu____2361 = FStar_Syntax_Subst.compress e  in
                uu____2361.FStar_Syntax_Syntax.n  in
              (match uu____2360 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2387 =
                       let uu____2388 = FStar_Syntax_Subst.compress h  in
                       uu____2388.FStar_Syntax_Syntax.n  in
                     match uu____2387 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2395 = FStar_Syntax_Syntax.lid_of_fv fv
                            in
                         (uu____2395, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2403 = aux h1  in
                         (match uu____2403 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2415 -> failwith "wrong Data_app head format"
                      in
                   let uu____2419 = aux head1  in
                   (match uu____2419 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____2434 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos
                                  in
                               (uu____2434, FStar_Parser_AST.UnivApp))
                            universes
                           in
                        let args1 =
                          FStar_List.map
                            (fun uu____2443  ->
                               match uu____2443 with
                               | (t1,uu____2449) ->
                                   let uu____2450 = resugar_term t1  in
                                   (uu____2450, FStar_Parser_AST.Nothing))
                            args
                           in
                        if FStar_Syntax_Util.is_tuple_data_lid' head2
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2455 = FStar_Options.print_universes ()
                              in
                           if uu____2455
                           then
                             mk1
                               (FStar_Parser_AST.Construct
                                  (head2,
                                    (FStar_List.append args1 universes1)))
                           else
                             mk1 (FStar_Parser_AST.Construct (head2, args1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____2465,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2471,uu____2472) -> resugar_term e
                    | uu____2477 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2478 -> failwith "wrong Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e  in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2484,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2500 =
                      let uu____2501 =
                        let uu____2506 = resugar_seq t11  in
                        (uu____2506, t2, t3)  in
                      FStar_Parser_AST.Ascribed uu____2501  in
                    mk1 uu____2500
                | uu____2508 -> t1  in
              resugar_seq term
          | FStar_Syntax_Syntax.Primop 
            |FStar_Syntax_Syntax.Masked_effect 
             |FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term e
          | FStar_Syntax_Syntax.Mutable_alloc  ->
              let term = resugar_term e  in
              (match term.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier ,l,t1)
                   ->
                   mk1
                     (FStar_Parser_AST.Let (FStar_Parser_AST.Mutable, l, t1))
               | uu____2521 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant None
                 in
              let uu____2523 =
                let uu____2524 = FStar_Syntax_Subst.compress e  in
                uu____2524.FStar_Syntax_Syntax.n  in
              (match uu____2523 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2528;
                      FStar_Syntax_Syntax.pos = uu____2529;
                      FStar_Syntax_Syntax.vars = uu____2530;_},(term,uu____2532)::[])
                   -> resugar_term term
               | uu____2554 -> failwith "mutable_rval should have app term")
           in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2576  ->
                       match uu____2576 with
                       | (x,uu____2580) -> resugar_term x))
                in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2582,p) ->
             let uu____2584 =
               let uu____2585 =
                 let uu____2589 = resugar_term e  in (uu____2589, l, p)  in
               FStar_Parser_AST.Labeled uu____2585  in
             mk1 uu____2584
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1)
           |FStar_Syntax_Syntax.Meta_monadic_lift (name1,_,t1) ->
             let uu____2603 =
               let uu____2604 =
                 let uu____2609 = resugar_term e  in
                 let uu____2610 =
                   let uu____2611 =
                     let uu____2612 =
                       let uu____2618 =
                         let uu____2622 =
                           let uu____2625 = resugar_term t1  in
                           (uu____2625, FStar_Parser_AST.Nothing)  in
                         [uu____2622]  in
                       (name1, uu____2618)  in
                     FStar_Parser_AST.Construct uu____2612  in
                   mk1 uu____2611  in
                 (uu____2609, uu____2610, None)  in
               FStar_Parser_AST.Ascribed uu____2604  in
             mk1 uu____2603)
    | FStar_Syntax_Syntax.Tm_unknown  -> mk1 FStar_Parser_AST.Wild

and resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term =
  fun c  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un
       in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (typ,u) ->
        let t = resugar_term typ  in
        (match u with
         | None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Syntax_Const.effect_Tot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | Some u1 ->
             let uu____2656 = FStar_Options.print_universes ()  in
             if uu____2656
             then
               let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
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
        let t = resugar_term typ  in
        (match u with
         | None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Syntax_Const.effect_GTot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | Some u1 ->
             let uu____2692 = FStar_Options.print_universes ()  in
             if uu____2692
             then
               let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
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
          let uu____2715 = resugar_term c1.FStar_Syntax_Syntax.result_typ  in
          (uu____2715, FStar_Parser_AST.Nothing)  in
        let uu____2716 = FStar_Options.print_effect_args ()  in
        if uu____2716
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs
             in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Syntax_Const.effect_Lemma_lid
            then
              let rec aux l uu___205_2756 =
                match uu___205_2756 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Syntax_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____2798 -> aux l tl1
                     | uu____2803 -> aux ((t, aq) :: l) tl1)
                 in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args  in
          let args1 =
            FStar_List.map
              (fun uu____2823  ->
                 match uu____2823 with
                 | (e,uu____2829) ->
                     let uu____2830 = resugar_term e  in
                     (uu____2830, FStar_Parser_AST.Nothing)) args
             in
          let rec aux l uu___206_2844 =
            match uu___206_2844 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____2864 = resugar_term e  in
                       (uu____2864, FStar_Parser_AST.Nothing)  in
                     aux (e1 :: l) tl1
                 | uu____2867 -> aux l tl1)
             in
          let decrease = aux [] c1.FStar_Syntax_Syntax.flags  in
          mk1
            (FStar_Parser_AST.Construct
               ((c1.FStar_Syntax_Syntax.effect_name),
                 (FStar_List.append (result :: decrease) args1)))
        else
          mk1
            (FStar_Parser_AST.Construct
               ((c1.FStar_Syntax_Syntax.effect_name), [result]))

and resugar_bv_as_binder :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Parser_AST.binder =
  fun x  ->
    fun r  ->
      let e = resugar_term x.FStar_Syntax_Syntax.sort  in
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Wild  ->
          let uu____2892 =
            let uu____2893 = bv_as_unique_ident x  in
            FStar_Parser_AST.Variable uu____2893  in
          FStar_Parser_AST.mk_binder uu____2892 r FStar_Parser_AST.Type_level
            None
      | uu____2894 ->
          let uu____2895 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____2895
          then
            FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
              FStar_Parser_AST.Type_level None
          else
            (let uu____2897 =
               let uu____2898 =
                 let uu____2901 = bv_as_unique_ident x  in (uu____2901, e)
                  in
               FStar_Parser_AST.Annotated uu____2898  in
             FStar_Parser_AST.mk_binder uu____2897 r
               FStar_Parser_AST.Type_level None)

and resugar_bv_as_pat :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual -> FStar_Parser_AST.pattern
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____2908 = FStar_Syntax_Syntax.range_of_bv x  in
        FStar_Parser_AST.mk_pattern a uu____2908  in
      let uu____2909 =
        let uu____2910 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
        uu____2910.FStar_Syntax_Syntax.n  in
      match uu____2909 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix
             in
          if i = (Prims.parse_int "0")
          then mk1 FStar_Parser_AST.PatWild
          else
            (let uu____2915 =
               let uu____2916 =
                 let uu____2920 = bv_as_unique_ident x  in
                 let uu____2921 = resugar_arg_qual qual  in
                 (uu____2920, uu____2921)  in
               FStar_Parser_AST.PatVar uu____2916  in
             mk1 uu____2915)
      | uu____2924 ->
          let pat =
            let uu____2926 =
              let uu____2927 =
                let uu____2931 = bv_as_unique_ident x  in
                let uu____2932 = resugar_arg_qual qual  in
                (uu____2931, uu____2932)  in
              FStar_Parser_AST.PatVar uu____2927  in
            mk1 uu____2926  in
          let uu____2935 = FStar_Options.print_bound_var_types ()  in
          if uu____2935
          then
            let uu____2936 =
              let uu____2937 =
                let uu____2940 = resugar_term x.FStar_Syntax_Syntax.sort  in
                (pat, uu____2940)  in
              FStar_Parser_AST.PatAscribed uu____2937  in
            mk1 uu____2936
          else pat

and resugar_match_pat : FStar_Syntax_Syntax.pat -> FStar_Parser_AST.pattern =
  fun p  ->
    let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p  in
    let rec aux p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant c ->
          mk1 (FStar_Parser_AST.PatConst c)
      | FStar_Syntax_Syntax.Pat_disj args ->
          let args1 = FStar_List.map (fun p2  -> aux p2) args  in
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
              (fun uu____2993  -> match uu____2993 with | (p2,b) -> aux p2)
              args
             in
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
              (fun uu____3022  -> match uu____3022 with | (p2,b) -> aux p2)
              args
             in
          if
            FStar_Syntax_Util.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3034;
             FStar_Syntax_Syntax.fv_delta = uu____3035;
             FStar_Syntax_Syntax.fv_qual = Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3056 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
               in
            FStar_All.pipe_right uu____3056 FStar_List.rev  in
          let args1 =
            let uu____3065 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3075  ->
                      match uu____3075 with | (p2,b) -> aux p2))
               in
            FStar_All.pipe_right uu____3065 FStar_List.rev  in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3117 = map21 tl1 []  in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3117
            | (hd1::tl1,hd2::tl2) ->
                let uu____3131 = map21 tl1 tl2  in (hd1, hd2) :: uu____3131
             in
          let args2 =
            let uu____3141 = map21 fields1 args1  in
            FStar_All.pipe_right uu____3141 FStar_List.rev  in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3169  -> match uu____3169 with | (p2,b) -> aux p2)
              args
             in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3180 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
             in
          (match uu____3180 with
           | Some op ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | None  ->
               let uu____3183 =
                 let uu____3184 =
                   let uu____3188 = bv_as_unique_ident v1  in
                   (uu____3188, None)  in
                 FStar_Parser_AST.PatVar uu____3184  in
               mk1 uu____3183)
      | FStar_Syntax_Syntax.Pat_wild uu____3190 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3198 =
              let uu____3199 =
                let uu____3203 = bv_as_unique_ident bv  in (uu____3203, None)
                 in
              FStar_Parser_AST.PatVar uu____3199  in
            mk1 uu____3198  in
          let uu____3205 =
            let uu____3206 =
              let uu____3209 = resugar_term term  in (pat, uu____3209)  in
            FStar_Parser_AST.PatAscribed uu____3206  in
          mk1 uu____3205
       in
    aux p
