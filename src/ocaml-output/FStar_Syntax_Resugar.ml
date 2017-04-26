open Prims
let bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name = (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
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
      | uu____25 -> (n1, u)
  
let rec resugar_universe :
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un  in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1 (FStar_Parser_AST.Const (FStar_Const.Const_int ("0", None))) r
      | FStar_Syntax_Syntax.U_succ uu____44 ->
          let uu____45 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____45 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____50 =
                      let uu____51 =
                        let uu____52 =
                          let uu____58 = FStar_Util.string_of_int n1  in
                          (uu____58, None)  in
                        FStar_Const.Const_int uu____52  in
                      FStar_Parser_AST.Const uu____51  in
                    mk1 uu____50 r
                | uu____64 ->
                    let e1 =
                      let uu____66 =
                        let uu____67 =
                          let uu____68 =
                            let uu____74 = FStar_Util.string_of_int n1  in
                            (uu____74, None)  in
                          FStar_Const.Const_int uu____68  in
                        FStar_Parser_AST.Const uu____67  in
                      mk1 uu____66 r  in
                    let e2 = resugar_universe u1 r  in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____84 ->
               let t =
                 let uu____87 =
                   let uu____88 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____88  in
                 mk1 uu____87 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____91 =
                        let uu____92 =
                          let uu____96 = resugar_universe x r  in
                          (acc, uu____96, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____92  in
                      mk1 uu____91 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____98 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____103 =
              let uu____106 =
                let uu____107 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____107  in
              (uu____106, r)  in
            FStar_Ident.mk_ident uu____103  in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
  
let string_to_op : Prims.string -> Prims.string Prims.option =
  fun s  ->
    let name_of_op uu___197_116 =
      match uu___197_116 with
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
      | uu____118 -> None  in
    match s with
    | "op_String_Assignment" -> Some ".[]<-"
    | "op_Array_Assignment" -> Some ".()<-"
    | "op_String_Access" -> Some ".[]"
    | "op_Array_Access" -> Some ".()"
    | uu____120 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____124 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____124 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____129 ->
               let op =
                 let uu____132 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | Some op -> Prims.strcat acc op
                        | None  -> failwith "wrong composed operator format")
                   "" uu____132
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
      let uu____224 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  -> FStar_Syntax_Syntax.fv_eq_lid fv (Prims.fst d)))
         in
      match uu____224 with
      | Some op -> Some (Prims.snd op)
      | uu____245 ->
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
                (let uu____276 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.sread_lid
                    in
                 if uu____276
                 then
                   Some
                     (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str)
                 else None)
       in
    let uu____283 =
      let uu____284 = FStar_Syntax_Subst.compress t  in
      uu____284.FStar_Syntax_Syntax.n  in
    match uu____283 with
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
        let uu____310 = string_to_op s  in
        (match uu____310 with | Some t1 -> Some t1 | uu____314 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____322 -> None
  
let is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____326 -> false
  
let is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____330 -> true
    | uu____331 -> false
  
let rec resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un
       in
    let name a r =
      let uu____358 = FStar_Ident.lid_of_path [a] r  in
      FStar_Parser_AST.Name uu____358  in
    let var a r =
      let uu____366 = FStar_Ident.lid_of_path [a] r  in
      FStar_Parser_AST.Var uu____366  in
    let uu____367 =
      let uu____368 = FStar_Syntax_Subst.compress t  in
      uu____368.FStar_Syntax_Syntax.n  in
    match uu____367 with
    | FStar_Syntax_Syntax.Tm_delayed uu____371 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____394 =
            let uu____396 = bv_as_unique_ident x  in [uu____396]  in
          FStar_Ident.lid_of_ids uu____394  in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____399 =
            let uu____401 = bv_as_unique_ident x  in [uu____401]  in
          FStar_Ident.lid_of_ids uu____399  in
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
          let uu____425 =
            let uu____426 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
            FStar_Parser_AST.Discrim uu____426  in
          mk1 uu____425
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
             | uu____437 -> failwith "wrong projector format")
          else
            (let uu____440 =
               ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid))
                 ||
                 (let uu____441 =
                    let uu____442 = FStar_String.get s (Prims.parse_int "0")
                       in
                    FStar_Char.uppercase uu____442  in
                  let uu____443 = FStar_String.get s (Prims.parse_int "0")
                     in
                  uu____441 <> uu____443)
                in
             if uu____440
             then
               let uu____444 = var s t.FStar_Syntax_Syntax.pos  in
               mk1 uu____444
             else
               (let uu____446 = name s t.FStar_Syntax_Syntax.pos  in
                mk1 uu____446))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let e1 = resugar_term e  in
        FStar_List.fold_left
          (fun acc  ->
             fun x  ->
               let uu____456 =
                 let uu____457 =
                   let uu____461 =
                     resugar_universe x t.FStar_Syntax_Syntax.pos  in
                   (acc, uu____461, FStar_Parser_AST.UnivApp)  in
                 FStar_Parser_AST.App uu____457  in
               mk1 uu____456) e1 universes
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____463 = FStar_Syntax_Syntax.is_teff t  in
        if uu____463
        then
          let uu____464 = name "Effect" t.FStar_Syntax_Syntax.pos  in
          mk1 uu____464
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____467 = name "Type0" t.FStar_Syntax_Syntax.pos  in
             mk1 uu____467
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____468 = name "Type" t.FStar_Syntax_Syntax.pos  in
             mk1 uu____468
         | uu____469 ->
             let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos  in
             let l =
               FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos  in
             mk1
               (FStar_Parser_AST.Construct
                  (l, [(u1, FStar_Parser_AST.UnivApp)])))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____481) ->
        let uu____504 = FStar_Syntax_Subst.open_term xs body  in
        (match uu____504 with
         | (xs1,body1) ->
             let patterns =
               FStar_All.pipe_right xs1
                 (FStar_List.map
                    (fun uu____514  ->
                       match uu____514 with
                       | (x,qual) -> resugar_bv_as_pat x qual))
                in
             let body2 = resugar_term body1  in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____533 = FStar_Syntax_Subst.open_comp xs body  in
        (match uu____533 with
         | (xs1,body1) ->
             let body2 = resugar_comp body1  in
             let xs2 =
               let uu____541 =
                 FStar_All.pipe_right xs1
                   (FStar_List.map
                      (fun uu____546  ->
                         match uu____546 with
                         | (b,qual) ->
                             resugar_bv_as_binder b t.FStar_Syntax_Syntax.pos))
                  in
               FStar_All.pipe_right uu____541 FStar_List.rev  in
             let rec aux body3 uu___198_560 =
               match uu___198_560 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3))
                      in
                   aux body4 tl1
                in
             aux body2 xs2)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____573 =
          let uu____576 =
            let uu____577 = FStar_Syntax_Syntax.mk_binder x  in [uu____577]
             in
          FStar_Syntax_Subst.open_term uu____576 phi  in
        (match uu____573 with
         | (x1,phi1) ->
             let uu____580 = FStar_List.hd x1  in
             (match uu____580 with
              | (b,uu____586) ->
                  let b1 = resugar_bv_as_binder b t.FStar_Syntax_Syntax.pos
                     in
                  let uu____588 =
                    let uu____589 =
                      let uu____592 = resugar_term phi1  in (b1, uu____592)
                       in
                    FStar_Parser_AST.Refine uu____589  in
                  mk1 uu____588))
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___199_622 =
          match uu___199_622 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____669 -> failwith "last of an empty list"  in
        let rec last_two uu___200_693 =
          match uu___200_693 with
          | []|_::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____756::t1 -> last_two t1  in
        let rec last_three uu___201_784 =
          match uu___201_784 with
          | []|_::[]|_::_::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____874::t1 -> last_three t1  in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____910  ->
                    match uu____910 with | (e2,qual) -> resugar_term e2))
             in
          let e2 = resugar_term e1  in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 mk1
                   (FStar_Parser_AST.App (acc, x, FStar_Parser_AST.Nothing)))
            e2 args2
           in
        let uu____918 = resugar_term_as_op e  in
        (match uu____918 with
         | None  -> resugar_as_app e args
         | Some "tuple" ->
             let args1 =
               FStar_All.pipe_right args
                 (FStar_List.map
                    (fun uu____930  ->
                       match uu____930 with | (e1,qual) -> resugar_term e1))
                in
             (match args1 with
              | fst1::snd1::rest ->
                  let e1 =
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "*"), [fst1; snd1]))
                     in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.Op
                              ((FStar_Ident.id_of_text "*"), [e1; x]))) e1
                    rest
              | uu____944 -> failwith "tuple needs at least two arguments.")
         | Some "dtuple" ->
             let args1 = last1 args  in
             let body =
               match args1 with
               | (b,uu____958)::[] -> b
               | uu____971 -> failwith "wrong arguments to dtuple"  in
             let uu____979 =
               let uu____980 = FStar_Syntax_Subst.compress body  in
               uu____980.FStar_Syntax_Syntax.n  in
             (match uu____979 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____985) ->
                  let uu____1008 = FStar_Syntax_Subst.open_term xs body1  in
                  (match uu____1008 with
                   | (xs1,body2) ->
                       let xs2 =
                         FStar_All.pipe_right xs1
                           (FStar_List.map
                              (fun uu____1018  ->
                                 match uu____1018 with
                                 | (b,qual) ->
                                     resugar_bv_as_binder b
                                       t.FStar_Syntax_Syntax.pos))
                          in
                       let body3 = resugar_term body2  in
                       mk1 (FStar_Parser_AST.Sum (xs2, body3)))
              | uu____1025 ->
                  let args2 =
                    FStar_All.pipe_right args1
                      (FStar_List.map
                         (fun uu____1036  ->
                            match uu____1036 with
                            | (e1,qual) -> resugar_term e1))
                     in
                  let e1 = resugar_term e  in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args2)
         | Some ref_read when
             ref_read = FStar_Syntax_Const.sread_lid.FStar_Ident.str ->
             let uu____1045 = FStar_List.hd args  in
             (match uu____1045 with
              | (t1,uu____1055) ->
                  let uu____1060 =
                    let uu____1061 = FStar_Syntax_Subst.compress t1  in
                    uu____1061.FStar_Syntax_Syntax.n  in
                  (match uu____1060 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____1074 =
                         let uu____1075 =
                           let uu____1078 = resugar_term t1  in
                           (uu____1078, f)  in
                         FStar_Parser_AST.Project uu____1075  in
                       mk1 uu____1074
                   | uu____1079 -> resugar_term t1))
         | Some "try_with" ->
             let new_args = last_two args  in
             let uu____1086 =
               match new_args with
               | (a1,uu____1100)::(a2,uu____1102)::[] -> (a1, a2)
               | uu____1127 -> failwith "wrong arguments to try_with"  in
             (match uu____1086 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1153 =
                      let uu____1154 = FStar_Syntax_Subst.compress term  in
                      uu____1154.FStar_Syntax_Syntax.n  in
                    match uu____1153 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1159) ->
                        let uu____1182 = FStar_Syntax_Subst.open_term x e1
                           in
                        (match uu____1182 with | (x1,e2) -> e2)
                    | uu____1187 ->
                        failwith "wrong argument format to try_with"
                     in
                  let body1 =
                    let uu____1189 = decomp body  in resugar_term uu____1189
                     in
                  let handler1 =
                    let uu____1191 = decomp handler  in
                    resugar_term uu____1191  in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1197,uu____1198,b)::[]) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1220 =
                          let uu____1221 =
                            let uu____1226 = resugar_body t11  in
                            (uu____1226, t2, t3)  in
                          FStar_Parser_AST.Ascribed uu____1221  in
                        mk1 uu____1220
                    | uu____1228 ->
                        failwith "unexpected body format to try_with"
                     in
                  let e1 = resugar_body body1  in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1261 -> []  in
                  let branches = resugar_branches handler1  in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | Some op when (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body)|FStar_Parser_AST.QForall
                 (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1322 -> (xs, pat, t1)  in
             let resugar body =
               let uu____1330 =
                 let uu____1331 = FStar_Syntax_Subst.compress body  in
                 uu____1331.FStar_Syntax_Syntax.n  in
               match uu____1330 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1336) ->
                   let uu____1359 = FStar_Syntax_Subst.open_term xs body1  in
                   (match uu____1359 with
                    | (xs1,body2) ->
                        let xs2 =
                          FStar_All.pipe_right xs1
                            (FStar_List.map
                               (fun uu____1369  ->
                                  match uu____1369 with
                                  | (b,qual) ->
                                      resugar_bv_as_binder b
                                        t.FStar_Syntax_Syntax.pos))
                           in
                        let uu____1374 =
                          let uu____1379 =
                            let uu____1380 =
                              FStar_Syntax_Subst.compress body2  in
                            uu____1380.FStar_Syntax_Syntax.n  in
                          match uu____1379 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1  in
                              let resugar_pats pats =
                                FStar_List.map
                                  (fun es  ->
                                     FStar_All.pipe_right es
                                       (FStar_List.map
                                          (fun uu____1422  ->
                                             match uu____1422 with
                                             | (e2,uu____1426) ->
                                                 resugar_term e2))) pats
                                 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    resugar_pats pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1441) ->
                                    let uu____1442 =
                                      let uu____1444 =
                                        let uu____1445 = name s r  in
                                        mk1 uu____1445  in
                                      [uu____1444]  in
                                    [uu____1442]
                                | uu____1448 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists"
                                 in
                              (pats, body3)
                          | uu____1453 ->
                              let uu____1454 = resugar_term body2  in
                              ([], uu____1454)
                           in
                        (match uu____1374 with
                         | (pats,body3) ->
                             let uu____1464 = uncurry xs2 pats body3  in
                             (match uu____1464 with
                              | (xs3,pats1,body4) ->
                                  let xs4 =
                                    FStar_All.pipe_right xs3 FStar_List.rev
                                     in
                                  if op = "forall"
                                  then
                                    mk1
                                      (FStar_Parser_AST.QForall
                                         (xs4, pats1, body4))
                                  else
                                    mk1
                                      (FStar_Parser_AST.QExists
                                         (xs4, pats1, body4)))))
               | uu____1491 ->
                   if op = "forall"
                   then
                     let uu____1492 =
                       let uu____1493 =
                         let uu____1500 = resugar_term body  in
                         ([], [[]], uu____1500)  in
                       FStar_Parser_AST.QForall uu____1493  in
                     mk1 uu____1492
                   else
                     (let uu____1507 =
                        let uu____1508 =
                          let uu____1515 = resugar_term body  in
                          ([], [[]], uu____1515)  in
                        FStar_Parser_AST.QExists uu____1508  in
                      mk1 uu____1507)
                in
             let args1 = last1 args  in
             (match args1 with
              | (b,uu____1528)::[] -> resugar b
              | uu____1541 -> failwith "wrong args format to QForall")
         | Some "alloc" ->
             let uu____1547 = FStar_List.hd args  in
             (match uu____1547 with | (e1,uu____1557) -> resugar_term e1)
         | Some op ->
             let op1 = FStar_Ident.id_of_text op  in
             let resugar args1 =
               FStar_All.pipe_right args1
                 (FStar_List.map
                    (fun uu____1581  ->
                       match uu____1581 with | (e1,qual) -> resugar_term e1))
                in
             let uu____1586 =
               FStar_Parser_ToDocument.handleable_args_length op1  in
             (match uu____1586 with
              | _0_27 when _0_27 = (Prims.parse_int "1") ->
                  let uu____1587 =
                    let uu____1588 =
                      let uu____1592 =
                        let uu____1594 = last1 args  in resugar uu____1594
                         in
                      (op1, uu____1592)  in
                    FStar_Parser_AST.Op uu____1588  in
                  mk1 uu____1587
              | _0_28 when _0_28 = (Prims.parse_int "2") ->
                  let uu____1599 =
                    let uu____1600 =
                      let uu____1604 =
                        let uu____1606 = last_two args  in resugar uu____1606
                         in
                      (op1, uu____1604)  in
                    FStar_Parser_AST.Op uu____1600  in
                  mk1 uu____1599
              | _0_29 when _0_29 = (Prims.parse_int "3") ->
                  let uu____1611 =
                    let uu____1612 =
                      let uu____1616 =
                        let uu____1618 = last_three args  in
                        resugar uu____1618  in
                      (op1, uu____1616)  in
                    FStar_Parser_AST.Op uu____1612  in
                  mk1 uu____1611
              | uu____1623 -> resugar_as_app e args))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____1626,t1)::(pat2,uu____1629,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____1704 =
          let uu____1705 =
            let uu____1709 = resugar_term e  in
            let uu____1710 = resugar_term t1  in
            let uu____1711 = resugar_term t2  in
            (uu____1709, uu____1710, uu____1711)  in
          FStar_Parser_AST.If uu____1705  in
        mk1 uu____1704
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____1751 =
          match uu____1751 with
          | (pat,wopt,b) ->
              let pat1 = resugar_match_pat pat  in
              let wopt1 =
                match wopt with
                | None  -> None
                | Some e1 ->
                    let uu____1770 = resugar_term e1  in Some uu____1770
                 in
              let b1 = resugar_term b  in (pat1, wopt1, b1)
           in
        let uu____1773 =
          let uu____1774 =
            let uu____1782 = resugar_term e  in
            let uu____1783 = FStar_List.map resugar_branch branches  in
            (uu____1782, uu____1783)  in
          FStar_Parser_AST.Match uu____1774  in
        mk1 uu____1773
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____1805) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1  in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt  in
        let uu____1858 =
          let uu____1859 =
            let uu____1864 = resugar_term e  in (uu____1864, term, tac_opt1)
             in
          FStar_Parser_AST.Ascribed uu____1859  in
        mk1 uu____1858
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
        let uu____1882 = FStar_Syntax_Subst.open_let_rec bnds body  in
        (match uu____1882 with
         | (bnd,body1) ->
             let resugar_one_binding bnd1 =
               let uu____1898 =
                 let uu____1901 =
                   FStar_Syntax_Util.mk_conj bnd1.FStar_Syntax_Syntax.lbtyp
                     bnd1.FStar_Syntax_Syntax.lbdef
                    in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd1.FStar_Syntax_Syntax.lbunivs uu____1901
                  in
               match uu____1898 with
               | (univs1,td) ->
                   let uu____1908 =
                     let uu____1915 =
                       let uu____1916 = FStar_Syntax_Subst.compress td  in
                       uu____1916.FStar_Syntax_Syntax.n  in
                     match uu____1915 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____1925,(t1,uu____1927)::(d,uu____1929)::[]) ->
                         (t1, d)
                     | uu____1963 -> failwith "wrong let binding format"  in
                   (match uu____1908 with
                    | (typ,def) ->
                        let uu____1984 =
                          let uu____1988 =
                            let uu____1989 = FStar_Syntax_Subst.compress def
                               in
                            uu____1989.FStar_Syntax_Syntax.n  in
                          match uu____1988 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____1997) ->
                              let uu____2020 =
                                FStar_Syntax_Subst.open_term b t1  in
                              (match uu____2020 with
                               | (b1,t2) -> (b1, t2, true))
                          | uu____2028 -> ([], def, false)  in
                        (match uu____1984 with
                         | (binders,term,is_pat_app) ->
                             let uu____2043 =
                               match bnd1.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2054 =
                                     let uu____2057 =
                                       let uu____2058 =
                                         FStar_Syntax_Syntax.mk_binder bv  in
                                       [uu____2058]  in
                                     FStar_Syntax_Subst.open_term uu____2057
                                       term
                                      in
                                   (match uu____2054 with
                                    | (x,term1) ->
                                        let uu____2063 = FStar_List.hd x  in
                                        (match uu____2063 with
                                         | (bv1,uu____2071) ->
                                             let uu____2072 =
                                               let uu____2073 =
                                                 let uu____2074 =
                                                   let uu____2078 =
                                                     bv_as_unique_ident bv1
                                                      in
                                                   (uu____2078, None)  in
                                                 FStar_Parser_AST.PatVar
                                                   uu____2074
                                                  in
                                               mk_pat uu____2073  in
                                             (uu____2072, term1)))
                                in
                             (match uu____2043 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (FStar_List.map
                                           (fun uu____2095  ->
                                              match uu____2095 with
                                              | (bv,uu____2099) ->
                                                  let uu____2100 =
                                                    let uu____2101 =
                                                      let uu____2105 =
                                                        bv_as_unique_ident bv
                                                         in
                                                      (uu____2105, None)  in
                                                    FStar_Parser_AST.PatVar
                                                      uu____2101
                                                     in
                                                  mk_pat uu____2100))
                                       in
                                    let uu____2107 =
                                      let uu____2110 = resugar_term term1  in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2110)
                                       in
                                    let uu____2112 =
                                      let uu____2113 =
                                        FStar_List.map
                                          (fun x  -> x.FStar_Ident.idText)
                                          univs1
                                         in
                                      FStar_All.pipe_right uu____2113
                                        (FStar_String.concat ", ")
                                       in
                                    (uu____2107, uu____2112)
                                  else
                                    (let uu____2120 =
                                       let uu____2123 = resugar_term term1
                                          in
                                       (pat, uu____2123)  in
                                     let uu____2124 =
                                       let uu____2125 =
                                         FStar_List.map
                                           (fun x  -> x.FStar_Ident.idText)
                                           univs1
                                          in
                                       FStar_All.pipe_right uu____2125
                                         (FStar_String.concat ", ")
                                        in
                                     (uu____2120, uu____2124)))))
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
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2167) ->
        let s =
          let uu____2181 =
            let uu____2182 = FStar_Unionfind.uvar_id u  in
            FStar_All.pipe_right uu____2182 FStar_Util.string_of_int  in
          Prims.strcat "uu___unification_ " uu____2181  in
        let uu____2186 = var s t.FStar_Syntax_Syntax.pos  in mk1 uu____2186
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___202_2196 =
          match uu___202_2196 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2197 =
                let uu____2198 = FStar_Syntax_Subst.compress e  in
                uu____2198.FStar_Syntax_Syntax.n  in
              (match uu____2197 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2224 =
                       let uu____2225 = FStar_Syntax_Subst.compress h  in
                       uu____2225.FStar_Syntax_Syntax.n  in
                     match uu____2224 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2232 = FStar_Syntax_Syntax.lid_of_fv fv
                            in
                         (uu____2232, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2240 = aux h1  in
                         (match uu____2240 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2252 -> failwith "wrong Data_app head format"
                      in
                   let uu____2256 = aux head1  in
                   (match uu____2256 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____2271 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos
                                  in
                               (uu____2271, FStar_Parser_AST.UnivApp))
                            universes
                           in
                        let args1 =
                          FStar_List.map
                            (fun uu____2280  ->
                               match uu____2280 with
                               | (t1,uu____2286) ->
                                   let uu____2287 = resugar_term t1  in
                                   (uu____2287, FStar_Parser_AST.Nothing))
                            args
                           in
                        if FStar_Syntax_Util.is_tuple_data_lid' head2
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          mk1
                            (FStar_Parser_AST.Construct
                               (head2, (FStar_List.append args1 universes1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____2297,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2303,uu____2304) -> resugar_term e
                    | uu____2309 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2310 -> failwith "wrong Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e  in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2316,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2332 =
                      let uu____2333 =
                        let uu____2338 = resugar_seq t11  in
                        (uu____2338, t2, t3)  in
                      FStar_Parser_AST.Ascribed uu____2333  in
                    mk1 uu____2332
                | uu____2340 -> t1  in
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
               | uu____2353 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant None
                 in
              let uu____2355 =
                let uu____2356 = FStar_Syntax_Subst.compress e  in
                uu____2356.FStar_Syntax_Syntax.n  in
              (match uu____2355 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2360;
                      FStar_Syntax_Syntax.pos = uu____2361;
                      FStar_Syntax_Syntax.vars = uu____2362;_},(term,uu____2364)::[])
                   -> resugar_term term
               | uu____2386 -> failwith "mutable_rval should have app term")
           in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2408  ->
                       match uu____2408 with
                       | (x,uu____2412) -> resugar_term x))
                in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2414,p) ->
             let uu____2416 =
               let uu____2417 =
                 let uu____2421 = resugar_term e  in (uu____2421, l, p)  in
               FStar_Parser_AST.Labeled uu____2417  in
             mk1 uu____2416
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1)
           |FStar_Syntax_Syntax.Meta_monadic_lift (name1,_,t1) ->
             let uu____2435 =
               let uu____2436 =
                 let uu____2441 = resugar_term e  in
                 let uu____2442 =
                   let uu____2443 =
                     let uu____2444 =
                       let uu____2450 =
                         let uu____2454 =
                           let uu____2457 = resugar_term t1  in
                           (uu____2457, FStar_Parser_AST.Nothing)  in
                         [uu____2454]  in
                       (name1, uu____2450)  in
                     FStar_Parser_AST.Construct uu____2444  in
                   mk1 uu____2443  in
                 (uu____2441, uu____2442, None)  in
               FStar_Parser_AST.Ascribed uu____2436  in
             mk1 uu____2435)
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
             let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Syntax_Const.effect_Tot_lid,
                    [(u2, FStar_Parser_AST.UnivApp);
                    (t, FStar_Parser_AST.Nothing)])))
    | FStar_Syntax_Syntax.GTotal (typ,u) ->
        let t = resugar_term typ  in
        (match u with
         | None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Syntax_Const.effect_GTot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | Some u1 ->
             let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Syntax_Const.effect_GTot_lid,
                    [(u2, FStar_Parser_AST.UnivApp);
                    (t, FStar_Parser_AST.Nothing)])))
    | FStar_Syntax_Syntax.Comp c1 ->
        let universe =
          FStar_List.map (fun u  -> resugar_universe u)
            c1.FStar_Syntax_Syntax.comp_univs
           in
        let result =
          let uu____2536 = resugar_term c1.FStar_Syntax_Syntax.result_typ  in
          (uu____2536, FStar_Parser_AST.Nothing)  in
        let args =
          if
            FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Const.effect_Lemma_lid
          then
            let rec aux l uu___203_2569 =
              match uu___203_2569 with
              | [] -> l
              | (t,aq)::tl1 ->
                  (match t.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.true_lid
                       -> aux l tl1
                   | FStar_Syntax_Syntax.Tm_meta uu____2611 -> aux l tl1
                   | uu____2616 -> aux ((t, aq) :: l) tl1)
               in
            aux [] c1.FStar_Syntax_Syntax.effect_args
          else c1.FStar_Syntax_Syntax.effect_args  in
        let args1 =
          FStar_List.map
            (fun uu____2636  ->
               match uu____2636 with
               | (e,uu____2642) ->
                   let uu____2643 = resugar_term e  in
                   (uu____2643, FStar_Parser_AST.Nothing)) args
           in
        let rec aux l uu___204_2657 =
          match uu___204_2657 with
          | [] -> l
          | hd1::tl1 ->
              (match hd1 with
               | FStar_Syntax_Syntax.DECREASES e ->
                   let e1 =
                     let uu____2677 = resugar_term e  in
                     (uu____2677, FStar_Parser_AST.Nothing)  in
                   aux (e1 :: l) tl1
               | uu____2680 -> aux l tl1)
           in
        let decrease = aux [] c1.FStar_Syntax_Syntax.flags  in
        mk1
          (FStar_Parser_AST.Construct
             ((c1.FStar_Syntax_Syntax.effect_name),
               (FStar_List.append (result :: decrease) args1)))

and resugar_bv_as_binder :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Parser_AST.binder =
  fun x  ->
    fun r  ->
      let e = resugar_term x.FStar_Syntax_Syntax.sort  in
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Wild  ->
          let uu____2697 =
            let uu____2698 = bv_as_unique_ident x  in
            FStar_Parser_AST.Variable uu____2698  in
          FStar_Parser_AST.mk_binder uu____2697 r FStar_Parser_AST.Type_level
            None
      | uu____2699 ->
          let uu____2700 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____2700
          then
            FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
              FStar_Parser_AST.Type_level None
          else
            (let uu____2702 =
               let uu____2703 =
                 let uu____2706 = bv_as_unique_ident x  in (uu____2706, e)
                  in
               FStar_Parser_AST.Annotated uu____2703  in
             FStar_Parser_AST.mk_binder uu____2702 r
               FStar_Parser_AST.Type_level None)

and resugar_bv_as_pat :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual -> FStar_Parser_AST.pattern
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____2713 = FStar_Syntax_Syntax.range_of_bv x  in
        FStar_Parser_AST.mk_pattern a uu____2713  in
      let uu____2714 =
        let uu____2715 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
        uu____2715.FStar_Syntax_Syntax.n  in
      match uu____2714 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix
             in
          if i = (Prims.parse_int "0")
          then mk1 FStar_Parser_AST.PatWild
          else
            (let uu____2720 =
               let uu____2721 =
                 let uu____2725 = bv_as_unique_ident x  in
                 let uu____2726 = resugar_arg_qual qual  in
                 (uu____2725, uu____2726)  in
               FStar_Parser_AST.PatVar uu____2721  in
             mk1 uu____2720)
      | uu____2729 ->
          let pat =
            let uu____2731 =
              let uu____2732 =
                let uu____2736 = bv_as_unique_ident x  in
                let uu____2737 = resugar_arg_qual qual  in
                (uu____2736, uu____2737)  in
              FStar_Parser_AST.PatVar uu____2732  in
            mk1 uu____2731  in
          let uu____2740 =
            let uu____2741 =
              let uu____2744 = resugar_term x.FStar_Syntax_Syntax.sort  in
              (pat, uu____2744)  in
            FStar_Parser_AST.PatAscribed uu____2741  in
          mk1 uu____2740

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
              (fun uu____2796  -> match uu____2796 with | (p2,b) -> aux p2)
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
              (fun uu____2825  -> match uu____2825 with | (p2,b) -> aux p2)
              args
             in
          if
            FStar_Syntax_Util.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____2837;
             FStar_Syntax_Syntax.fv_delta = uu____2838;
             FStar_Syntax_Syntax.fv_qual = Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____2859 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
               in
            FStar_All.pipe_right uu____2859 FStar_List.rev  in
          let args1 =
            let uu____2868 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____2878  ->
                      match uu____2878 with | (p2,b) -> aux p2))
               in
            FStar_All.pipe_right uu____2868 FStar_List.rev  in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____2920 = map21 tl1 []  in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____2920
            | (hd1::tl1,hd2::tl2) ->
                let uu____2934 = map21 tl1 tl2  in (hd1, hd2) :: uu____2934
             in
          let args2 =
            let uu____2944 = map21 fields1 args1  in
            FStar_All.pipe_right uu____2944 FStar_List.rev  in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____2972  -> match uu____2972 with | (p2,b) -> aux p2)
              args
             in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____2983 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
             in
          (match uu____2983 with
           | Some op ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | None  ->
               let uu____2986 =
                 let uu____2987 =
                   let uu____2991 = bv_as_unique_ident v1  in
                   (uu____2991, None)  in
                 FStar_Parser_AST.PatVar uu____2987  in
               mk1 uu____2986)
      | FStar_Syntax_Syntax.Pat_wild uu____2993 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3001 =
              let uu____3002 =
                let uu____3006 = bv_as_unique_ident bv  in (uu____3006, None)
                 in
              FStar_Parser_AST.PatVar uu____3002  in
            mk1 uu____3001  in
          let uu____3008 =
            let uu____3009 =
              let uu____3012 = resugar_term term  in (pat, uu____3012)  in
            FStar_Parser_AST.PatAscribed uu____3009  in
          mk1 uu____3008
       in
    aux p
