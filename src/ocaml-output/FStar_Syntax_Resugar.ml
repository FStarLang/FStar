open Prims
let doc_to_string : FStar_Pprint.document -> Prims.string =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let parser_term_to_string : FStar_Parser_AST.term -> Prims.string =
  fun t  ->
    let uu____7 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____7
  
let map_opt f l =
  let uu____32 =
    FStar_Util.choose_map
      (fun uu____36  -> fun x  -> let uu____38 = f x  in ((), uu____38)) () l
     in
  FStar_Pervasives_Native.snd uu____32 
let bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name =
      if
        FStar_Util.starts_with FStar_Ident.reserved_prefix
          (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      then
        let uu____46 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____46
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___183_78  ->
          match uu___183_78 with
          | (uu____82,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____83)) -> false
          | uu____85 -> true))
  
let resugar_arg_qual :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option
  =
  fun q  ->
    match q with
    | FStar_Pervasives_Native.None  ->
        FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b) ->
        if b
        then FStar_Pervasives_Native.None
        else
          FStar_Pervasives_Native.Some
            (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
        FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some FStar_Parser_AST.Equality)
  
let resugar_imp :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Parser_AST.imp
  =
  fun q  ->
    match q with
    | FStar_Pervasives_Native.None  -> FStar_Parser_AST.Nothing
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        FStar_Parser_AST.Hash
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
        failwith "Not an imp"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        failwith "Not an imp"
  
let rec universe_to_int :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____124 -> (n1, u)
  
let universe_to_string : FStar_Ident.ident Prims.list -> Prims.string =
  fun univs1  ->
    let uu____130 = FStar_Options.print_universes ()  in
    if uu____130
    then
      let uu____131 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1
         in
      FStar_All.pipe_right uu____131 (FStar_String.concat ", ")
    else ""
  
let rec resugar_universe :
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un  in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1
            (FStar_Parser_AST.Const
               (FStar_Const.Const_int ("0", FStar_Pervasives_Native.None))) r
      | FStar_Syntax_Syntax.U_succ uu____154 ->
          let uu____155 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____155 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____160 =
                      let uu____161 =
                        let uu____162 =
                          let uu____168 = FStar_Util.string_of_int n1  in
                          (uu____168, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____162  in
                      FStar_Parser_AST.Const uu____161  in
                    mk1 uu____160 r
                | uu____174 ->
                    let e1 =
                      let uu____176 =
                        let uu____177 =
                          let uu____178 =
                            let uu____184 = FStar_Util.string_of_int n1  in
                            (uu____184, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____178  in
                        FStar_Parser_AST.Const uu____177  in
                      mk1 uu____176 r  in
                    let e2 = resugar_universe u1 r  in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____194 ->
               let t =
                 let uu____197 =
                   let uu____198 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____198  in
                 mk1 uu____197 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____201 =
                        let uu____202 =
                          let uu____206 = resugar_universe x r  in
                          (acc, uu____206, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____202  in
                      mk1 uu____201 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____208 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____213 =
              let uu____216 =
                let uu____217 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____217  in
              (uu____216, r)  in
            FStar_Ident.mk_ident uu____213  in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
  
let string_to_op :
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun s  ->
    let name_of_op uu___184_230 =
      match uu___184_230 with
      | "Amp" -> FStar_Pervasives_Native.Some ("&", (Prims.parse_int "0"))
      | "At" -> FStar_Pervasives_Native.Some ("@", (Prims.parse_int "0"))
      | "Plus" -> FStar_Pervasives_Native.Some ("+", (Prims.parse_int "0"))
      | "Minus" -> FStar_Pervasives_Native.Some ("-", (Prims.parse_int "0"))
      | "Subtraction" ->
          FStar_Pervasives_Native.Some ("-", (Prims.parse_int "2"))
      | "Slash" -> FStar_Pervasives_Native.Some ("/", (Prims.parse_int "0"))
      | "Less" -> FStar_Pervasives_Native.Some ("<", (Prims.parse_int "0"))
      | "Equals" -> FStar_Pervasives_Native.Some ("=", (Prims.parse_int "0"))
      | "Greater" ->
          FStar_Pervasives_Native.Some (">", (Prims.parse_int "0"))
      | "Underscore" ->
          FStar_Pervasives_Native.Some ("_", (Prims.parse_int "0"))
      | "Bar" -> FStar_Pervasives_Native.Some ("|", (Prims.parse_int "0"))
      | "Bang" -> FStar_Pervasives_Native.Some ("!", (Prims.parse_int "0"))
      | "Hat" -> FStar_Pervasives_Native.Some ("^", (Prims.parse_int "0"))
      | "Percent" ->
          FStar_Pervasives_Native.Some ("%", (Prims.parse_int "0"))
      | "Star" -> FStar_Pervasives_Native.Some ("*", (Prims.parse_int "0"))
      | "Question" ->
          FStar_Pervasives_Native.Some ("?", (Prims.parse_int "0"))
      | "Colon" -> FStar_Pervasives_Native.Some (":", (Prims.parse_int "0"))
      | uu____268 -> FStar_Pervasives_Native.None  in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", (Prims.parse_int "0"))
    | uu____282 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____288 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____288 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____295 ->
               let op =
                 let uu____298 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____315) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____298
                  in
               FStar_Pervasives_Native.Some (op, (Prims.parse_int "0")))
        else FStar_Pervasives_Native.None
  
let rec resugar_term_as_op :
  FStar_Syntax_Syntax.term ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun t  ->
    let infix_prim_ops =
      [(FStar_Parser_Const.op_Addition, "+");
      (FStar_Parser_Const.op_Subtraction, "-");
      (FStar_Parser_Const.op_Minus, "-");
      (FStar_Parser_Const.op_Multiply, "*");
      (FStar_Parser_Const.op_Division, "/");
      (FStar_Parser_Const.op_Modulus, "%");
      (FStar_Parser_Const.read_lid, "!");
      (FStar_Parser_Const.list_append_lid, "@");
      (FStar_Parser_Const.list_tot_append_lid, "@");
      (FStar_Parser_Const.strcat_lid, "^");
      (FStar_Parser_Const.pipe_right_lid, "|>");
      (FStar_Parser_Const.pipe_left_lid, "<|");
      (FStar_Parser_Const.op_Eq, "=");
      (FStar_Parser_Const.op_ColonEq, ":=");
      (FStar_Parser_Const.op_notEq, "<>");
      (FStar_Parser_Const.not_lid, "~");
      (FStar_Parser_Const.op_And, "&&");
      (FStar_Parser_Const.op_Or, "||");
      (FStar_Parser_Const.op_LTE, "<=");
      (FStar_Parser_Const.op_GTE, ">=");
      (FStar_Parser_Const.op_LT, "<");
      (FStar_Parser_Const.op_GT, ">");
      (FStar_Parser_Const.op_Modulus, "mod");
      (FStar_Parser_Const.and_lid, "/\\");
      (FStar_Parser_Const.or_lid, "\\/");
      (FStar_Parser_Const.imp_lid, "==>");
      (FStar_Parser_Const.iff_lid, "<==>");
      (FStar_Parser_Const.precedes_lid, "<<");
      (FStar_Parser_Const.eq2_lid, "==");
      (FStar_Parser_Const.eq3_lid, "===");
      (FStar_Parser_Const.forall_lid, "forall");
      (FStar_Parser_Const.exists_lid, "exists");
      (FStar_Parser_Const.salloc_lid, "alloc")]  in
    let fallback fv =
      let uu____413 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____413 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), (Prims.parse_int "0"))
      | uu____438 ->
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
          then FStar_Pervasives_Native.Some ("dtuple", (Prims.parse_int "0"))
          else
            if FStar_Util.starts_with str "tuple"
            then
              FStar_Pervasives_Native.Some ("tuple", (Prims.parse_int "0"))
            else
              if FStar_Util.starts_with str "try_with"
              then
                FStar_Pervasives_Native.Some
                  ("try_with", (Prims.parse_int "0"))
              else
                (let uu____481 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____481
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else FStar_Pervasives_Native.None)
       in
    let uu____494 =
      let uu____495 = FStar_Syntax_Subst.compress t  in
      uu____495.FStar_Syntax_Syntax.n  in
    match uu____494 with
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
        let uu____523 = string_to_op s  in
        (match uu____523 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____537 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____547 -> FStar_Pervasives_Native.None
  
let is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____553 -> false
  
let is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____557 -> true
    | uu____558 -> false
  
let rec resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un
       in
    let name a r =
      let uu____587 = FStar_Ident.lid_of_path [a] r  in
      FStar_Parser_AST.Name uu____587  in
    let var a r =
      let uu____595 = FStar_Ident.lid_of_path [a] r  in
      FStar_Parser_AST.Var uu____595  in
    let uu____596 =
      let uu____597 = FStar_Syntax_Subst.compress t  in
      uu____597.FStar_Syntax_Syntax.n  in
    match uu____596 with
    | FStar_Syntax_Syntax.Tm_delayed uu____600 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____623 =
            let uu____625 = bv_as_unique_ident x  in [uu____625]  in
          FStar_Ident.lid_of_ids uu____623  in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____628 =
            let uu____630 = bv_as_unique_ident x  in [uu____630]  in
          FStar_Ident.lid_of_ids uu____628  in
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
          let uu____654 =
            let uu____655 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
            FStar_Parser_AST.Discrim uu____655  in
          mk1 uu____654
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
             | uu____666 -> failwith "wrong projector format")
          else
            (let uu____669 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____670 =
                    let uu____671 = FStar_String.get s (Prims.parse_int "0")
                       in
                    FStar_Char.uppercase uu____671  in
                  let uu____672 = FStar_String.get s (Prims.parse_int "0")
                     in
                  uu____670 <> uu____672)
                in
             if uu____669
             then
               let uu____673 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos  in
               mk1 uu____673
             else
               (let uu____675 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos  in
                mk1 uu____675))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____682 = FStar_Options.print_universes ()  in
        if uu____682
        then
          let e1 = resugar_term e  in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____686 =
                   let uu____687 =
                     let uu____691 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos  in
                     (acc, uu____691, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____687  in
                 mk1 uu____686) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____694 = FStar_Syntax_Syntax.is_teff t  in
        if uu____694
        then
          let uu____695 = name "Effect" t.FStar_Syntax_Syntax.pos  in
          mk1 uu____695
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____698 = name "Type0" t.FStar_Syntax_Syntax.pos  in
             mk1 uu____698
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____699 = name "Type" t.FStar_Syntax_Syntax.pos  in
             mk1 uu____699
         | uu____700 ->
             let uu____701 = FStar_Options.print_universes ()  in
             if uu____701
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos  in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos
                  in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____712 = name "Type" t.FStar_Syntax_Syntax.pos  in
                mk1 uu____712))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____715) ->
        let uu____738 = FStar_Syntax_Subst.open_term xs body  in
        (match uu____738 with
         | (xs1,body1) ->
             let xs2 =
               let uu____744 = FStar_Options.print_implicits ()  in
               if uu____744 then xs1 else filter_imp xs1  in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____751  ->
                       match uu____751 with
                       | (x,qual) -> resugar_bv_as_pat x qual))
                in
             let body2 = resugar_term body1  in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____771 = FStar_Syntax_Subst.open_comp xs body  in
        (match uu____771 with
         | (xs1,body1) ->
             let xs2 =
               let uu____777 = FStar_Options.print_implicits ()  in
               if uu____777 then xs1 else filter_imp xs1  in
             let body2 = resugar_comp body1  in
             let xs3 =
               let uu____782 =
                 FStar_All.pipe_right xs2
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos))
                  in
               FStar_All.pipe_right uu____782 FStar_List.rev  in
             let rec aux body3 uu___185_795 =
               match uu___185_795 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3))
                      in
                   aux body4 tl1
                in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____808 =
          let uu____811 =
            let uu____812 = FStar_Syntax_Syntax.mk_binder x  in [uu____812]
             in
          FStar_Syntax_Subst.open_term uu____811 phi  in
        (match uu____808 with
         | (x1,phi1) ->
             let b =
               let uu____816 =
                 let uu____818 = FStar_List.hd x1  in
                 resugar_binder uu____818 t.FStar_Syntax_Syntax.pos  in
               FStar_Util.must uu____816  in
             let uu____821 =
               let uu____822 =
                 let uu____825 = resugar_term phi1  in (b, uu____825)  in
               FStar_Parser_AST.Refine uu____822  in
             mk1 uu____821)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___186_855 =
          match uu___186_855 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____902 -> failwith "last of an empty list"  in
        let rec last_two uu___187_926 =
          match uu___187_926 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____946::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____998::t1 -> last_two t1  in
        let rec last_three uu___188_1026 =
          match uu___188_1026 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1046::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1064::uu____1065::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1138::t1 -> last_three t1  in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1187  ->
                    match uu____1187 with
                    | (e2,qual) ->
                        let uu____1198 = resugar_term e2  in
                        (uu____1198, qual)))
             in
          let e2 = resugar_term e1  in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1205  ->
                 match uu____1205 with
                 | (x,qual) ->
                     let uu____1213 =
                       let uu____1214 =
                         let uu____1218 = resugar_imp qual  in
                         (acc, x, uu____1218)  in
                       FStar_Parser_AST.App uu____1214  in
                     mk1 uu____1213) e2 args2
           in
        let args1 =
          let uu____1225 = FStar_Options.print_implicits ()  in
          if uu____1225 then args else filter_imp args  in
        let uu____1234 = resugar_term_as_op e  in
        (match uu____1234 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1240) ->
             (match args1 with
              | (fst1,uu____1244)::(snd1,uu____1246)::rest ->
                  let e1 =
                    let uu____1270 =
                      let uu____1271 =
                        let uu____1275 =
                          let uu____1277 = resugar_term fst1  in
                          let uu____1278 =
                            let uu____1280 = resugar_term snd1  in
                            [uu____1280]  in
                          uu____1277 :: uu____1278  in
                        ((FStar_Ident.id_of_text "*"), uu____1275)  in
                      FStar_Parser_AST.Op uu____1271  in
                    mk1 uu____1270  in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1285  ->
                         match uu____1285 with
                         | (x,uu____1289) ->
                             let uu____1290 =
                               let uu____1291 =
                                 let uu____1295 =
                                   let uu____1297 =
                                     let uu____1299 = resugar_term x  in
                                     [uu____1299]  in
                                   e1 :: uu____1297  in
                                 ((FStar_Ident.id_of_text "*"), uu____1295)
                                  in
                               FStar_Parser_AST.Op uu____1291  in
                             mk1 uu____1290) e1 rest
              | uu____1301 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1307) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1  in
             let body =
               match args2 with
               | (b,uu____1329)::[] -> b
               | uu____1342 -> failwith "wrong arguments to dtuple"  in
             let uu____1350 =
               let uu____1351 = FStar_Syntax_Subst.compress body  in
               uu____1351.FStar_Syntax_Syntax.n  in
             (match uu____1350 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1356) ->
                  let uu____1379 = FStar_Syntax_Subst.open_term xs body1  in
                  (match uu____1379 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1385 = FStar_Options.print_implicits ()
                            in
                         if uu____1385 then xs1 else filter_imp xs1  in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (map_opt
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos))
                          in
                       let body3 = resugar_term body2  in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1393 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1404  ->
                            match uu____1404 with
                            | (e1,qual) -> resugar_term e1))
                     in
                  let e1 = resugar_term e  in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1412) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____1416) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____1419 = FStar_List.hd args1  in
             (match uu____1419 with
              | (t1,uu____1429) ->
                  let uu____1434 =
                    let uu____1435 = FStar_Syntax_Subst.compress t1  in
                    uu____1435.FStar_Syntax_Syntax.n  in
                  (match uu____1434 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____1448 =
                         let uu____1449 =
                           let uu____1452 = resugar_term t1  in
                           (uu____1452, f)  in
                         FStar_Parser_AST.Project uu____1449  in
                       mk1 uu____1448
                   | uu____1453 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____1454) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1  in
             let uu____1470 =
               match new_args with
               | (a1,uu____1484)::(a2,uu____1486)::[] -> (a1, a2)
               | uu____1511 -> failwith "wrong arguments to try_with"  in
             (match uu____1470 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1537 =
                      let uu____1538 = FStar_Syntax_Subst.compress term  in
                      uu____1538.FStar_Syntax_Syntax.n  in
                    match uu____1537 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1543) ->
                        let uu____1566 = FStar_Syntax_Subst.open_term x e1
                           in
                        (match uu____1566 with | (x1,e2) -> e2)
                    | uu____1571 ->
                        failwith "wrong argument format to try_with"
                     in
                  let body1 =
                    let uu____1573 = decomp body  in resugar_term uu____1573
                     in
                  let handler1 =
                    let uu____1575 = decomp handler  in
                    resugar_term uu____1575  in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1581,uu____1582,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1599,uu____1600,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1613 =
                          let uu____1614 =
                            let uu____1619 = resugar_body t11  in
                            (uu____1619, t2, t3)  in
                          FStar_Parser_AST.Ascribed uu____1614  in
                        mk1 uu____1613
                    | uu____1621 ->
                        failwith "unexpected body format to try_with"
                     in
                  let e1 = resugar_body body1  in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1654 -> []  in
                  let branches = resugar_branches handler1  in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____1670) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____1674) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1725 -> (xs, pat, t1)  in
             let resugar body =
               let uu____1733 =
                 let uu____1734 = FStar_Syntax_Subst.compress body  in
                 uu____1734.FStar_Syntax_Syntax.n  in
               match uu____1733 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1739) ->
                   let uu____1762 = FStar_Syntax_Subst.open_term xs body1  in
                   (match uu____1762 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1768 = FStar_Options.print_implicits ()
                             in
                          if uu____1768 then xs1 else filter_imp xs1  in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (map_opt
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos))
                           in
                        let uu____1774 =
                          let uu____1779 =
                            let uu____1780 =
                              FStar_Syntax_Subst.compress body2  in
                            uu____1780.FStar_Syntax_Syntax.n  in
                          match uu____1779 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1  in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____1820  ->
                                                 match uu____1820 with
                                                 | (e2,uu____1824) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1827) ->
                                    let uu____1828 =
                                      let uu____1830 =
                                        let uu____1831 = name s r  in
                                        mk1 uu____1831  in
                                      [uu____1830]  in
                                    [uu____1828]
                                | uu____1834 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists"
                                 in
                              (pats, body3)
                          | uu____1839 ->
                              let uu____1840 = resugar_term body2  in
                              ([], uu____1840)
                           in
                        (match uu____1774 with
                         | (pats,body3) ->
                             let uu____1850 = uncurry xs3 pats body3  in
                             (match uu____1850 with
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
               | uu____1877 ->
                   if op = "forall"
                   then
                     let uu____1878 =
                       let uu____1879 =
                         let uu____1886 = resugar_term body  in
                         ([], [[]], uu____1886)  in
                       FStar_Parser_AST.QForall uu____1879  in
                     mk1 uu____1878
                   else
                     (let uu____1893 =
                        let uu____1894 =
                          let uu____1901 = resugar_term body  in
                          ([], [[]], uu____1901)  in
                        FStar_Parser_AST.QExists uu____1894  in
                      mk1 uu____1893)
                in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1  in
               (match args2 with
                | (b,uu____1921)::[] -> resugar b
                | uu____1934 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____1941) ->
             let uu____1944 = FStar_List.hd args1  in
             (match uu____1944 with | (e1,uu____1954) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op  in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1981  ->
                       match uu____1981 with | (e1,qual) -> resugar_term e1))
                in
             (match arity with
              | _0_28 when _0_28 = (Prims.parse_int "0") ->
                  let uu____1986 =
                    FStar_Parser_ToDocument.handleable_args_length op1  in
                  (match uu____1986 with
                   | _0_29 when
                       (_0_29 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1994 =
                         let uu____1995 =
                           let uu____1999 =
                             let uu____2001 = last1 args1  in
                             resugar uu____2001  in
                           (op1, uu____1999)  in
                         FStar_Parser_AST.Op uu____1995  in
                       mk1 uu____1994
                   | _0_30 when
                       (_0_30 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____2013 =
                         let uu____2014 =
                           let uu____2018 =
                             let uu____2020 = last_two args1  in
                             resugar uu____2020  in
                           (op1, uu____2018)  in
                         FStar_Parser_AST.Op uu____2014  in
                       mk1 uu____2013
                   | _0_31 when
                       (_0_31 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____2032 =
                         let uu____2033 =
                           let uu____2037 =
                             let uu____2039 = last_three args1  in
                             resugar uu____2039  in
                           (op1, uu____2037)  in
                         FStar_Parser_AST.Op uu____2033  in
                       mk1 uu____2032
                   | uu____2044 -> resugar_as_app e args1)
              | _0_32 when
                  (_0_32 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____2052 =
                    let uu____2053 =
                      let uu____2057 =
                        let uu____2059 = last_two args1  in
                        resugar uu____2059  in
                      (op1, uu____2057)  in
                    FStar_Parser_AST.Op uu____2053  in
                  mk1 uu____2052
              | uu____2064 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____2067,t1)::[]) ->
        let bnds =
          let uu____2122 =
            let uu____2125 = resugar_pat pat  in
            let uu____2126 = resugar_term e  in (uu____2125, uu____2126)  in
          [uu____2122]  in
        let body = resugar_term t1  in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____2137,t1)::(pat2,uu____2140,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2215 =
          let uu____2216 =
            let uu____2220 = resugar_term e  in
            let uu____2221 = resugar_term t1  in
            let uu____2222 = resugar_term t2  in
            (uu____2220, uu____2221, uu____2222)  in
          FStar_Parser_AST.If uu____2216  in
        mk1 uu____2215
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2262 =
          match uu____2262 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat  in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____2281 = resugar_term e1  in
                    FStar_Pervasives_Native.Some uu____2281
                 in
              let b1 = resugar_term b  in (pat1, wopt1, b1)
           in
        let uu____2284 =
          let uu____2285 =
            let uu____2293 = resugar_term e  in
            let uu____2294 = FStar_List.map resugar_branch branches  in
            (uu____2293, uu____2294)  in
          FStar_Parser_AST.Match uu____2285  in
        mk1 uu____2284
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2316) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1  in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt  in
        let uu____2369 =
          let uu____2370 =
            let uu____2375 = resugar_term e  in (uu____2375, term, tac_opt1)
             in
          FStar_Parser_AST.Ascribed uu____2370  in
        mk1 uu____2369
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
        let uu____2393 = FStar_Syntax_Subst.open_let_rec bnds body  in
        (match uu____2393 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2409 =
                 let uu____2412 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef
                    in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2412
                  in
               match uu____2409 with
               | (univs1,td) ->
                   let uu____2419 =
                     let uu____2426 =
                       let uu____2427 = FStar_Syntax_Subst.compress td  in
                       uu____2427.FStar_Syntax_Syntax.n  in
                     match uu____2426 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2436,(t1,uu____2438)::(d,uu____2440)::[]) ->
                         (t1, d)
                     | uu____2474 -> failwith "wrong let binding format"  in
                   (match uu____2419 with
                    | (typ,def) ->
                        let uu____2495 =
                          let uu____2499 =
                            let uu____2500 = FStar_Syntax_Subst.compress def
                               in
                            uu____2500.FStar_Syntax_Syntax.n  in
                          match uu____2499 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2508) ->
                              let uu____2531 =
                                FStar_Syntax_Subst.open_term b t1  in
                              (match uu____2531 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2540 =
                                       FStar_Options.print_implicits ()  in
                                     if uu____2540 then b1 else filter_imp b1
                                      in
                                   (b2, t2, true))
                          | uu____2542 -> ([], def, false)  in
                        (match uu____2495 with
                         | (binders,term,is_pat_app) ->
                             let uu____2557 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2568 =
                                     let uu____2569 =
                                       let uu____2570 =
                                         let uu____2574 =
                                           bv_as_unique_ident bv  in
                                         (uu____2574,
                                           FStar_Pervasives_Native.None)
                                          in
                                       FStar_Parser_AST.PatVar uu____2570  in
                                     mk_pat uu____2569  in
                                   (uu____2568, term)
                                in
                             (match uu____2557 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (map_opt
                                           (fun uu____2592  ->
                                              match uu____2592 with
                                              | (bv,q) ->
                                                  let uu____2601 =
                                                    resugar_arg_qual q  in
                                                  FStar_Util.map_opt
                                                    uu____2601
                                                    (fun q1  ->
                                                       let uu____2607 =
                                                         let uu____2608 =
                                                           let uu____2612 =
                                                             bv_as_unique_ident
                                                               bv
                                                              in
                                                           (uu____2612, q1)
                                                            in
                                                         FStar_Parser_AST.PatVar
                                                           uu____2608
                                                          in
                                                       mk_pat uu____2607)))
                                       in
                                    let uu____2614 =
                                      let uu____2617 = resugar_term term1  in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2617)
                                       in
                                    let uu____2619 =
                                      universe_to_string univs1  in
                                    (uu____2614, uu____2619)
                                  else
                                    (let uu____2623 =
                                       let uu____2626 = resugar_term term1
                                          in
                                       (pat, uu____2626)  in
                                     let uu____2627 =
                                       universe_to_string univs1  in
                                     (uu____2623, uu____2627)))))
                in
             let r = FStar_List.map resugar_one_binding bnds1  in
             let bnds2 =
               let f =
                 let uu____2653 =
                   let uu____2654 = FStar_Options.print_universes ()  in
                   Prims.op_Negation uu____2654  in
                 Obj.magic
                   (if uu____2653
                    then FStar_Pervasives_Native.fst
                    else
                      (fun uu___189_2666  ->
                         match uu___189_2666 with
                         | ((pat,body2),univs1) ->
                             let uu____2678 =
                               if univs1 = ""
                               then body2
                               else
                                 mk1
                                   (FStar_Parser_AST.Labeled
                                      (body2, univs1, true))
                                in
                             (pat, uu____2678)))
                  in
               FStar_List.map f r  in
             let body2 = resugar_term body1  in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2692) ->
        let s =
          let uu____2706 =
            let uu____2707 = FStar_Unionfind.uvar_id u  in
            FStar_All.pipe_right uu____2707 FStar_Util.string_of_int  in
          Prims.strcat "uu___unification_ " uu____2706  in
        let uu____2711 = var s t.FStar_Syntax_Syntax.pos  in mk1 uu____2711
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___190_2721 =
          match uu___190_2721 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____2735 =
                  let uu____2736 = FStar_Syntax_Subst.compress h  in
                  uu____2736.FStar_Syntax_Syntax.n  in
                match uu____2735 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____2749 = FStar_Syntax_Syntax.lid_of_fv fv  in
                    (uu____2749, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____2766 = head_fv_universes_args h1  in
                    (match uu____2766 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____2822 = head_fv_universes_args head1  in
                    (match uu____2822 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____2866 ->
                    let uu____2867 =
                      let uu____2868 =
                        let uu____2869 =
                          let uu____2870 = resugar_term h  in
                          parser_term_to_string uu____2870  in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____2869
                         in
                      FStar_Errors.Err uu____2868  in
                    raise uu____2867
                 in
              let uu____2880 =
                try
                  let uu____2909 = FStar_Syntax_Util.unmeta e  in
                  head_fv_universes_args uu____2909
                with
                | FStar_Errors.Err uu____2920 ->
                    let uu____2921 =
                      let uu____2922 =
                        let uu____2925 =
                          let uu____2926 =
                            let uu____2927 = resugar_term e  in
                            parser_term_to_string uu____2927  in
                          FStar_Util.format1 "wrong Data_app head format %s"
                            uu____2926
                           in
                        (uu____2925, (e.FStar_Syntax_Syntax.pos))  in
                      FStar_Errors.Error uu____2922  in
                    raise uu____2921
                 in
              (match uu____2880 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____2959 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos  in
                          (uu____2959, FStar_Parser_AST.UnivApp)) universes
                      in
                   let args1 =
                     FStar_List.map
                       (fun uu____2969  ->
                          match uu____2969 with
                          | (t1,q) ->
                              let uu____2979 = resugar_term t1  in
                              let uu____2980 = resugar_imp q  in
                              (uu____2979, uu____2980)) args
                      in
                   let args2 =
                     let uu____2985 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____2986 = FStar_Options.print_universes ()
                             in
                          Prims.op_Negation uu____2986)
                        in
                     if uu____2985
                     then args1
                     else FStar_List.append universes1 args1  in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e  in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____3001,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____3017 =
                      let uu____3018 =
                        let uu____3023 = resugar_seq t11  in
                        (uu____3023, t2, t3)  in
                      FStar_Parser_AST.Ascribed uu____3018  in
                    mk1 uu____3017
                | uu____3025 -> t1  in
              resugar_seq term
          | FStar_Syntax_Syntax.Primop  -> resugar_term e
          | FStar_Syntax_Syntax.Masked_effect  -> resugar_term e
          | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term e
          | FStar_Syntax_Syntax.Mutable_alloc  ->
              let term = resugar_term e  in
              (match term.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier ,l,t1)
                   ->
                   mk1
                     (FStar_Parser_AST.Let (FStar_Parser_AST.Mutable, l, t1))
               | uu____3038 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____3040 =
                let uu____3041 = FStar_Syntax_Subst.compress e  in
                uu____3041.FStar_Syntax_Syntax.n  in
              (match uu____3040 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____3045;
                      FStar_Syntax_Syntax.pos = uu____3046;
                      FStar_Syntax_Syntax.vars = uu____3047;_},(term,uu____3049)::[])
                   -> resugar_term term
               | uu____3071 -> failwith "mutable_rval should have app term")
           in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____3093  ->
                       match uu____3093 with
                       | (x,uu____3097) -> resugar_term x))
                in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____3099,p) ->
             let uu____3101 =
               let uu____3102 =
                 let uu____3106 = resugar_term e  in (uu____3106, l, p)  in
               FStar_Parser_AST.Labeled uu____3102  in
             mk1 uu____3101
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____3115 =
               let uu____3116 =
                 let uu____3121 = resugar_term e  in
                 let uu____3122 =
                   let uu____3123 =
                     let uu____3124 =
                       let uu____3130 =
                         let uu____3134 =
                           let uu____3137 = resugar_term t1  in
                           (uu____3137, FStar_Parser_AST.Nothing)  in
                         [uu____3134]  in
                       (name1, uu____3130)  in
                     FStar_Parser_AST.Construct uu____3124  in
                   mk1 uu____3123  in
                 (uu____3121, uu____3122, FStar_Pervasives_Native.None)  in
               FStar_Parser_AST.Ascribed uu____3116  in
             mk1 uu____3115
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____3147,t1) ->
             let uu____3153 =
               let uu____3154 =
                 let uu____3159 = resugar_term e  in
                 let uu____3160 =
                   let uu____3161 =
                     let uu____3162 =
                       let uu____3168 =
                         let uu____3172 =
                           let uu____3175 = resugar_term t1  in
                           (uu____3175, FStar_Parser_AST.Nothing)  in
                         [uu____3172]  in
                       (name1, uu____3168)  in
                     FStar_Parser_AST.Construct uu____3162  in
                   mk1 uu____3161  in
                 (uu____3159, uu____3160, FStar_Pervasives_Native.None)  in
               FStar_Parser_AST.Ascribed uu____3154  in
             mk1 uu____3153)
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
         | FStar_Pervasives_Native.None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Parser_Const.effect_Tot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | FStar_Pervasives_Native.Some u1 ->
             let uu____3206 = FStar_Options.print_universes ()  in
             if uu____3206
             then
               let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_Tot_lid,
                      [(u2, FStar_Parser_AST.UnivApp);
                      (t, FStar_Parser_AST.Nothing)]))
             else
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_Tot_lid,
                      [(t, FStar_Parser_AST.Nothing)])))
    | FStar_Syntax_Syntax.GTotal (typ,u) ->
        let t = resugar_term typ  in
        (match u with
         | FStar_Pervasives_Native.None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Parser_Const.effect_GTot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | FStar_Pervasives_Native.Some u1 ->
             let uu____3242 = FStar_Options.print_universes ()  in
             if uu____3242
             then
               let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_GTot_lid,
                      [(u2, FStar_Parser_AST.UnivApp);
                      (t, FStar_Parser_AST.Nothing)]))
             else
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_GTot_lid,
                      [(t, FStar_Parser_AST.Nothing)])))
    | FStar_Syntax_Syntax.Comp c1 ->
        let result =
          let uu____3265 = resugar_term c1.FStar_Syntax_Syntax.result_typ  in
          (uu____3265, FStar_Parser_AST.Nothing)  in
        let uu____3266 = FStar_Options.print_effect_args ()  in
        if uu____3266
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs
             in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Parser_Const.effect_Lemma_lid
            then
              let rec aux l uu___191_3306 =
                match uu___191_3306 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3348 -> aux l tl1
                     | uu____3353 -> aux ((t, aq) :: l) tl1)
                 in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args  in
          let args1 =
            FStar_List.map
              (fun uu____3373  ->
                 match uu____3373 with
                 | (e,uu____3379) ->
                     let uu____3380 = resugar_term e  in
                     (uu____3380, FStar_Parser_AST.Nothing)) args
             in
          let rec aux l uu___192_3394 =
            match uu___192_3394 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3414 = resugar_term e  in
                       (uu____3414, FStar_Parser_AST.Nothing)  in
                     aux (e1 :: l) tl1
                 | uu____3417 -> aux l tl1)
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

and resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option
  =
  fun b  ->
    fun r  ->
      let uu____3442 = b  in
      match uu____3442 with
      | (x,aq) ->
          let uu____3446 = resugar_arg_qual aq  in
          FStar_Util.map_opt uu____3446
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort  in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____3453 =
                     let uu____3454 = bv_as_unique_ident x  in
                     FStar_Parser_AST.Variable uu____3454  in
                   FStar_Parser_AST.mk_binder uu____3453 r
                     FStar_Parser_AST.Type_level imp
               | uu____3455 ->
                   let uu____3456 = FStar_Syntax_Syntax.is_null_bv x  in
                   if uu____3456
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____3458 =
                        let uu____3459 =
                          let uu____3462 = bv_as_unique_ident x  in
                          (uu____3462, e)  in
                        FStar_Parser_AST.Annotated uu____3459  in
                      FStar_Parser_AST.mk_binder uu____3458 r
                        FStar_Parser_AST.Type_level imp))

and resugar_bv_as_pat :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3470 = FStar_Syntax_Syntax.range_of_bv x  in
        FStar_Parser_AST.mk_pattern a uu____3470  in
      let uu____3471 =
        let uu____3472 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
        uu____3472.FStar_Syntax_Syntax.n  in
      match uu____3471 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix
             in
          if i = (Prims.parse_int "0")
          then
            let uu____3478 = mk1 FStar_Parser_AST.PatWild  in
            FStar_Pervasives_Native.Some uu____3478
          else
            (let uu____3480 = resugar_arg_qual qual  in
             FStar_Util.bind_opt uu____3480
               (fun aq  ->
                  let uu____3486 =
                    let uu____3487 =
                      let uu____3488 =
                        let uu____3492 = bv_as_unique_ident x  in
                        (uu____3492, aq)  in
                      FStar_Parser_AST.PatVar uu____3488  in
                    mk1 uu____3487  in
                  FStar_Pervasives_Native.Some uu____3486))
      | uu____3494 ->
          let uu____3495 = resugar_arg_qual qual  in
          FStar_Util.bind_opt uu____3495
            (fun aq  ->
               let pat =
                 let uu____3502 =
                   let uu____3503 =
                     let uu____3507 = bv_as_unique_ident x  in
                     (uu____3507, aq)  in
                   FStar_Parser_AST.PatVar uu____3503  in
                 mk1 uu____3502  in
               let uu____3509 = FStar_Options.print_bound_var_types ()  in
               if uu____3509
               then
                 let uu____3511 =
                   let uu____3512 =
                     let uu____3513 =
                       let uu____3516 =
                         resugar_term x.FStar_Syntax_Syntax.sort  in
                       (pat, uu____3516)  in
                     FStar_Parser_AST.PatAscribed uu____3513  in
                   mk1 uu____3512  in
                 FStar_Pervasives_Native.Some uu____3511
               else FStar_Pervasives_Native.Some pat)

and resugar_pat : FStar_Syntax_Syntax.pat -> FStar_Parser_AST.pattern =
  fun p  ->
    let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p  in
    let to_arg_qual bopt =
      FStar_Util.bind_opt bopt
        (fun b  ->
           if true
           then FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit
           else FStar_Pervasives_Native.None)
       in
    let rec aux p1 imp_opt =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant c ->
          mk1 (FStar_Parser_AST.PatConst c)
      | FStar_Syntax_Syntax.Pat_cons (fv,[]) ->
          mk1
            (FStar_Parser_AST.PatName
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
      | FStar_Syntax_Syntax.Pat_cons (fv,args) when
          FStar_Ident.lid_equals
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.cons_lid
          ->
          let args1 =
            FStar_List.map
              (fun uu____3577  ->
                 match uu____3577 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args
             in
          mk1 (FStar_Parser_AST.PatList args1)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) when
          (FStar_Parser_Const.is_tuple_data_lid'
             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
            ||
            (FStar_Parser_Const.is_dtuple_data_lid'
               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
          ->
          let args1 =
            FStar_List.map
              (fun uu____3606  ->
                 match uu____3606 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args
             in
          let uu____3611 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          if uu____3611
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3619;
             FStar_Syntax_Syntax.fv_delta = uu____3620;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3641 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
               in
            FStar_All.pipe_right uu____3641 FStar_List.rev  in
          let args1 =
            let uu____3650 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3660  ->
                      match uu____3660 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
               in
            FStar_All.pipe_right uu____3650 FStar_List.rev  in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3702 = map21 tl1 []  in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3702
            | (hd1::tl1,hd2::tl2) ->
                let uu____3716 = map21 tl1 tl2  in (hd1, hd2) :: uu____3716
             in
          let args2 =
            let uu____3726 = map21 fields1 args1  in
            FStar_All.pipe_right uu____3726 FStar_List.rev  in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3754  ->
                 match uu____3754 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args
             in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3765 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
             in
          (match uu____3765 with
           | FStar_Pervasives_Native.Some (op,uu____3770) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____3775 =
                 let uu____3776 =
                   let uu____3780 = bv_as_unique_ident v1  in
                   let uu____3781 = to_arg_qual imp_opt  in
                   (uu____3780, uu____3781)  in
                 FStar_Parser_AST.PatVar uu____3776  in
               mk1 uu____3775)
      | FStar_Syntax_Syntax.Pat_wild uu____3784 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3792 =
              let uu____3793 =
                let uu____3797 = bv_as_unique_ident bv  in
                (uu____3797,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))
                 in
              FStar_Parser_AST.PatVar uu____3793  in
            mk1 uu____3792  in
          let uu____3799 = FStar_Options.print_bound_var_types ()  in
          if uu____3799
          then
            let uu____3800 =
              let uu____3801 =
                let uu____3804 = resugar_term term  in (pat, uu____3804)  in
              FStar_Parser_AST.PatAscribed uu____3801  in
            mk1 uu____3800
          else pat
       in
    aux p FStar_Pervasives_Native.None

let resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___193_3809  ->
    match uu___193_3809 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Assumption
    | FStar_Syntax_Syntax.New  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.New
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
        FStar_Pervasives_Native.Some
          FStar_Parser_AST.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default  ->
        if true
        then FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.Some FStar_Parser_AST.Visible
    | FStar_Syntax_Syntax.Irreducible  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Irreducible
    | FStar_Syntax_Syntax.Abstract  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Abstract
    | FStar_Syntax_Syntax.Inline_for_extraction  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.NoExtract
    | FStar_Syntax_Syntax.Noeq  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Noeq
    | FStar_Syntax_Syntax.Unopteq  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Unopteq
    | FStar_Syntax_Syntax.TotalEffect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.TotalEffect
    | FStar_Syntax_Syntax.Logic  ->
        if true
        then FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.Some FStar_Parser_AST.Logic
    | FStar_Syntax_Syntax.Reifiable  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reifiable
    | FStar_Syntax_Syntax.Reflectable uu____3815 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3816 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____3817 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____3820 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____3825 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____3830 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___194_3833  ->
    match uu___194_3833 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.LightOff  -> FStar_Parser_AST.LightOff
  
let resugar_typ :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelts,FStar_Parser_AST.tycon)
        FStar_Pervasives_Native.tuple2
  =
  fun datacon_ses  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (tylid,uvs,bs,t,uu____3855,datacons) ->
          let uu____3861 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3872,uu____3873,uu____3874,inductive_lid,uu____3876,uu____3877)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3880 -> failwith "unexpected"))
             in
          (match uu____3861 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3891 = FStar_Options.print_implicits ()  in
                 if uu____3891 then bs else filter_imp bs  in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos))
                  in
               let tyc =
                 let uu____3898 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___195_3900  ->
                           match uu___195_3900 with
                           | FStar_Syntax_Syntax.RecordType uu____3901 ->
                               true
                           | uu____3906 -> false))
                    in
                 if uu____3898
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____3934,univs1,term,uu____3937,num,uu____3939)
                         ->
                         let uu____3942 =
                           let uu____3943 = FStar_Syntax_Subst.compress term
                              in
                           uu____3943.FStar_Syntax_Syntax.n  in
                         (match uu____3942 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3952) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3983  ->
                                        match uu____3983 with
                                        | (b,qual) ->
                                            let uu____3992 =
                                              let uu____3993 =
                                                bv_as_unique_ident b  in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3993
                                               in
                                            let uu____3994 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort
                                               in
                                            (uu____3992, uu____3994,
                                              FStar_Pervasives_Native.None)))
                                 in
                              FStar_List.append mfields fields
                          | uu____4000 -> failwith "unexpected")
                     | uu____4006 -> failwith "unexpected"  in
                   let fields =
                     FStar_List.fold_left resugar_datacon_as_fields []
                       current_datacons
                      in
                   FStar_Parser_AST.TyconRecord
                     ((tylid.FStar_Ident.ident), bs2,
                       FStar_Pervasives_Native.None, fields)
                 else
                   (let resugar_datacon constructors se1 =
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (l,univs1,term,uu____4073,num,uu____4075) ->
                          let c =
                            let uu____4085 =
                              let uu____4087 = resugar_term term  in
                              FStar_Pervasives_Native.Some uu____4087  in
                            ((l.FStar_Ident.ident), uu____4085,
                              FStar_Pervasives_Native.None, false)
                             in
                          c :: constructors
                      | uu____4096 -> failwith "unexpected"  in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons
                       in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors))
                  in
               (other_datacons, tyc))
      | uu____4135 ->
          failwith
            "Impossible : only Sig_inductive_typ can be resugared as types"
  
let mk_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Parser_AST.decl' -> FStar_Parser_AST.decl
  =
  fun r  ->
    fun q  ->
      fun d'  ->
        let uu____4149 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____4149;
          FStar_Parser_AST.attrs = []
        }
  
let decl'_to_decl :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl' -> FStar_Parser_AST.decl
  =
  fun se  ->
    fun d'  ->
      mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals
        d'
  
let resugar_tscheme' :
  Prims.string -> FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl =
  fun name  ->
    fun ts  ->
      let uu____4162 = ts  in
      match uu____4162 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
          let uu____4168 =
            let uu____4169 =
              let uu____4176 =
                let uu____4181 =
                  let uu____4185 =
                    let uu____4186 =
                      let uu____4193 = resugar_term typ  in
                      (name1, [], FStar_Pervasives_Native.None, uu____4193)
                       in
                    FStar_Parser_AST.TyconAbbrev uu____4186  in
                  (uu____4185, FStar_Pervasives_Native.None)  in
                [uu____4181]  in
              (false, uu____4176)  in
            FStar_Parser_AST.Tycon uu____4169  in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____4168
  
let resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl =
  fun ts  -> resugar_tscheme' "tsheme" ts 
let resugar_eff_decl :
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
                d.FStar_Syntax_Syntax.action_params
               in
            let uu____4232 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn
               in
            match uu____4232 with
            | (bs,action_defn) ->
                let uu____4237 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ
                   in
                (match uu____4237 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____4243 = FStar_Options.print_implicits ()  in
                       if uu____4243
                       then action_params
                       else filter_imp action_params  in
                     let action_params2 =
                       let uu____4247 =
                         FStar_All.pipe_right action_params1
                           (map_opt (fun b  -> resugar_binder b r))
                          in
                       FStar_All.pipe_right uu____4247 FStar_List.rev  in
                     let action_defn1 = resugar_term action_defn  in
                     let action_typ1 = resugar_term action_typ  in
                     if for_free1
                     then
                       let a =
                         let uu____4256 =
                           let uu____4262 =
                             FStar_Ident.lid_of_str "construct"  in
                           (uu____4262,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)])
                            in
                         FStar_Parser_AST.Construct uu____4256  in
                       let t =
                         FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un  in
                       mk_decl r q
                         (FStar_Parser_AST.Tycon
                            (false,
                              [((FStar_Parser_AST.TyconAbbrev
                                   (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                     action_params2,
                                     FStar_Pervasives_Native.None, t)),
                                 FStar_Pervasives_Native.None)]))
                     else
                       mk_decl r q
                         (FStar_Parser_AST.Tycon
                            (false,
                              [((FStar_Parser_AST.TyconAbbrev
                                   (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                     action_params2,
                                     FStar_Pervasives_Native.None,
                                     action_defn1)),
                                 FStar_Pervasives_Native.None)])))
             in
          let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident  in
          let uu____4301 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature
             in
          match uu____4301 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____4307 = FStar_Options.print_implicits ()  in
                if uu____4307 then eff_binders else filter_imp eff_binders
                 in
              let eff_binders2 =
                let uu____4311 =
                  FStar_All.pipe_right eff_binders1
                    (map_opt (fun b  -> resugar_binder b r))
                   in
                FStar_All.pipe_right uu____4311 FStar_List.rev  in
              let eff_typ1 = resugar_term eff_typ  in
              let ret_wp =
                resugar_tscheme' "ret_wp" ed.FStar_Syntax_Syntax.ret_wp  in
              let bind_wp =
                resugar_tscheme' "bind_wp" ed.FStar_Syntax_Syntax.ret_wp  in
              let if_then_else1 =
                resugar_tscheme' "if_then_else"
                  ed.FStar_Syntax_Syntax.if_then_else
                 in
              let ite_wp =
                resugar_tscheme' "ite_wp" ed.FStar_Syntax_Syntax.ite_wp  in
              let stronger =
                resugar_tscheme' "stronger" ed.FStar_Syntax_Syntax.stronger
                 in
              let close_wp =
                resugar_tscheme' "close_wp" ed.FStar_Syntax_Syntax.close_wp
                 in
              let assert_p =
                resugar_tscheme' "assert_p" ed.FStar_Syntax_Syntax.assert_p
                 in
              let assume_p =
                resugar_tscheme' "assume_p" ed.FStar_Syntax_Syntax.assume_p
                 in
              let null_wp =
                resugar_tscheme' "null_wp" ed.FStar_Syntax_Syntax.null_wp  in
              let trivial =
                resugar_tscheme' "trivial" ed.FStar_Syntax_Syntax.trivial  in
              let repr =
                resugar_tscheme' "repr" ([], (ed.FStar_Syntax_Syntax.repr))
                 in
              let return_repr =
                resugar_tscheme' "return_repr"
                  ed.FStar_Syntax_Syntax.return_repr
                 in
              let bind_repr =
                resugar_tscheme' "bind_repr" ed.FStar_Syntax_Syntax.bind_repr
                 in
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
                  trivial]
                 in
              let actions =
                FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions
                  (FStar_List.map (fun a  -> resugar_action a false))
                 in
              let decls = FStar_List.append mandatory_members_decls actions
                 in
              mk_decl r q
                (FStar_Parser_AST.NewEffect
                   (FStar_Parser_AST.DefineEffect
                      (eff_name, eff_binders2, eff_typ1, decls)))
  
let resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4352) ->
        let uu____4357 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____4368 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____4377 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4381 -> false
                  | uu____4389 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
           in
        (match uu____4357 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4409 se1 =
               match uu____4409 with
               | (datacon_ses1,tycons) ->
                   let uu____4424 = resugar_typ datacon_ses1 se1  in
                   (match uu____4424 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                in
             let uu____4433 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses
                in
             (match uu____4433 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4452 =
                         let uu____4453 =
                           let uu____4454 =
                             let uu____4461 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons
                                in
                             (false, uu____4461)  in
                           FStar_Parser_AST.Tycon uu____4454  in
                         decl'_to_decl se uu____4453  in
                       FStar_Pervasives_Native.Some uu____4452
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4478,uu____4479,uu____4480,uu____4481,uu____4482)
                            ->
                            let uu____4485 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None))
                               in
                            FStar_Pervasives_Native.Some uu____4485
                        | uu____4487 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4489 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4493,attrs) ->
        let uu____4499 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___196_4501  ->
                  match uu___196_4501 with
                  | FStar_Syntax_Syntax.Projector (uu____4502,uu____4503) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4504 -> true
                  | uu____4505 -> false))
           in
        if uu____4499
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng
              in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown  in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy))
              in
           let t = resugar_term desugared_let  in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____4530) ->
               let uu____4537 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets))
                  in
               FStar_Pervasives_Native.Some uu____4537
           | uu____4541 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,fml) ->
        let uu____4545 =
          let uu____4546 =
            let uu____4547 =
              let uu____4550 = resugar_term fml  in
              ((lid.FStar_Ident.ident), uu____4550)  in
            FStar_Parser_AST.Assume uu____4547  in
          decl'_to_decl se uu____4546  in
        FStar_Pervasives_Native.Some uu____4545
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4552 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed
           in
        FStar_Pervasives_Native.Some uu____4552
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4554 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed
           in
        FStar_Pervasives_Native.Some uu____4554
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source  in
        let dst = e.FStar_Syntax_Syntax.target  in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____4561,t) ->
              let uu____4568 = resugar_term t  in
              FStar_Pervasives_Native.Some uu____4568
          | uu____4569 -> FStar_Pervasives_Native.None  in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____4574,t) ->
              let uu____4581 = resugar_term t  in
              FStar_Pervasives_Native.Some uu____4581
          | uu____4582 -> FStar_Pervasives_Native.None  in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____4597 -> failwith "Should not happen hopefully"  in
        let uu____4602 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               })
           in
        FStar_Pervasives_Native.Some uu____4602
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4610 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____4610 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4617 = FStar_Options.print_implicits ()  in
               if uu____4617 then bs1 else filter_imp bs1  in
             let bs3 =
               FStar_All.pipe_right bs2
                 (map_opt
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng))
                in
             let uu____4623 =
               let uu____4624 =
                 let uu____4625 =
                   let uu____4632 =
                     let uu____4637 =
                       let uu____4641 =
                         let uu____4642 =
                           let uu____4649 = resugar_comp c1  in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____4649)
                            in
                         FStar_Parser_AST.TyconAbbrev uu____4642  in
                       (uu____4641, FStar_Pervasives_Native.None)  in
                     [uu____4637]  in
                   (false, uu____4632)  in
                 FStar_Parser_AST.Tycon uu____4625  in
               decl'_to_decl se uu____4624  in
             FStar_Pervasives_Native.Some uu____4623)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4664 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
        FStar_Pervasives_Native.Some uu____4664
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4668 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___197_4670  ->
                  match uu___197_4670 with
                  | FStar_Syntax_Syntax.Projector (uu____4671,uu____4672) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4673 -> true
                  | uu____4674 -> false))
           in
        if uu____4668
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____4678 =
               (let uu____4679 = FStar_Options.print_universes ()  in
                Prims.op_Negation uu____4679) || (FStar_List.isEmpty uvs)
                in
             if uu____4678
             then resugar_term t
             else
               (let uu____4681 = FStar_Syntax_Subst.open_univ_vars uvs t  in
                match uu____4681 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1  in
                    let uu____4687 =
                      let uu____4688 =
                        let uu____4692 = resugar_term t1  in
                        (uu____4692, universes, true)  in
                      FStar_Parser_AST.Labeled uu____4688  in
                    FStar_Parser_AST.mk_term uu____4687
                      t1.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un)
              in
           let uu____4693 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
              in
           FStar_Pervasives_Native.Some uu____4693)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4694 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____4703 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____4711 -> FStar_Pervasives_Native.None
  