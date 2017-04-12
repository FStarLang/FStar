open Prims
let bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name =
      let uu____5 =
        let uu____6 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.strcat "__" uu____6  in
      Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____5
       in
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
      | uu____27 -> (n1, u)
  
let rec resugar_universe :
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un  in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1 (FStar_Parser_AST.Const (FStar_Const.Const_int ("0", None))) r
      | FStar_Syntax_Syntax.U_succ uu____46 ->
          let uu____47 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____47 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____52 =
                      let uu____53 =
                        let uu____54 =
                          let uu____60 = FStar_Util.string_of_int n1  in
                          (uu____60, None)  in
                        FStar_Const.Const_int uu____54  in
                      FStar_Parser_AST.Const uu____53  in
                    mk1 uu____52 r
                | uu____66 ->
                    let e1 =
                      let uu____68 =
                        let uu____69 =
                          let uu____70 =
                            let uu____76 = FStar_Util.string_of_int n1  in
                            (uu____76, None)  in
                          FStar_Const.Const_int uu____70  in
                        FStar_Parser_AST.Const uu____69  in
                      mk1 uu____68 r  in
                    let e2 = resugar_universe u1 r  in
                    mk1 (FStar_Parser_AST.Op ("+", [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____86 ->
               let t =
                 let uu____89 =
                   let uu____90 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____90  in
                 mk1 uu____89 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____93 =
                        let uu____94 =
                          let uu____98 = resugar_universe x r  in
                          (acc, uu____98, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____94  in
                      mk1 uu____93 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____100 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____105 =
              let uu____108 =
                let uu____109 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____109  in
              (uu____108, r)  in
            FStar_Ident.mk_ident uu____105  in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
  
let string_to_op : Prims.string -> Prims.string Prims.option =
  fun s  ->
    let name_of_op uu___192_118 =
      match uu___192_118 with
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
      | uu____120 -> None  in
    match s with
    | "op_String_Assignment" -> Some ".[]<-"
    | "op_Array_Assignment" -> Some ".()<-"
    | "op_String_Access" -> Some ".[]"
    | "op_Array_Access" -> Some ".()"
    | uu____122 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____126 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____126 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____131 ->
               let op =
                 let uu____134 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | Some op -> Prims.strcat acc op
                        | None  -> failwith "wrong composed operator format")
                   "" uu____134
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
      (FStar_Syntax_Const.precedes_lid, "<<");
      (FStar_Syntax_Const.eq3_lid, "===");
      (FStar_Syntax_Const.forall_lid, "forall");
      (FStar_Syntax_Const.exists_lid, "exists");
      (FStar_Syntax_Const.salloc_lid, "alloc")]  in
    let fallback fv =
      let uu____228 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  -> FStar_Syntax_Syntax.fv_eq_lid fv (Prims.fst d)))
         in
      match uu____228 with
      | Some op -> Some (Prims.snd op)
      | uu____249 ->
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
                (let uu____280 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.sread_lid
                    in
                 if uu____280
                 then
                   Some
                     (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str)
                 else None)
       in
    let uu____287 =
      let uu____288 = FStar_Syntax_Subst.compress t  in
      uu____288.FStar_Syntax_Syntax.n  in
    match uu____287 with
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
        let uu____314 = string_to_op s  in
        (match uu____314 with | Some t1 -> Some t1 | uu____318 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____326 -> None
  
let is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____330 -> false
  
let is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____334 -> true
    | uu____335 -> false
  
let rec resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un
       in
    let name a r =
      let uu____362 = FStar_Ident.lid_of_path [a] r  in
      FStar_Parser_AST.Name uu____362  in
    let var a r =
      let uu____370 = FStar_Ident.lid_of_path [a] r  in
      FStar_Parser_AST.Var uu____370  in
    let uu____371 =
      let uu____372 = FStar_Syntax_Subst.compress t  in
      uu____372.FStar_Syntax_Syntax.n  in
    match uu____371 with
    | FStar_Syntax_Syntax.Tm_delayed uu____375 ->
        failwith "This case is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____398 =
            let uu____400 = bv_as_unique_ident x  in [uu____400]  in
          FStar_Ident.lid_of_ids uu____398  in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____403 =
            let uu____405 = bv_as_unique_ident x  in [uu____405]  in
          FStar_Ident.lid_of_ids uu____403  in
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
          let uu____429 =
            let uu____430 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
            FStar_Parser_AST.Discrim uu____430  in
          mk1 uu____429
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
             | uu____441 -> failwith "not implemented yet")
          else
            (let uu____444 =
               ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid))
                 ||
                 (let uu____445 =
                    let uu____446 = FStar_String.get s (Prims.parse_int "0")
                       in
                    FStar_Char.uppercase uu____446  in
                  let uu____447 = FStar_String.get s (Prims.parse_int "0")
                     in
                  uu____445 <> uu____447)
                in
             if uu____444
             then
               let uu____448 = var s t.FStar_Syntax_Syntax.pos  in
               mk1 uu____448
             else
               (let uu____450 = name s t.FStar_Syntax_Syntax.pos  in
                mk1 uu____450))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let e1 = resugar_term e  in
        FStar_List.fold_left
          (fun acc  ->
             fun x  ->
               let uu____460 =
                 let uu____461 =
                   let uu____465 =
                     resugar_universe x t.FStar_Syntax_Syntax.pos  in
                   (acc, uu____465, FStar_Parser_AST.UnivApp)  in
                 FStar_Parser_AST.App uu____461  in
               mk1 uu____460) e1 universes
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____467 = FStar_Syntax_Syntax.is_teff t  in
        if uu____467
        then
          let uu____468 = name "Effect" t.FStar_Syntax_Syntax.pos  in
          mk1 uu____468
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____471 = name "Type0" t.FStar_Syntax_Syntax.pos  in
             mk1 uu____471
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____472 = name "Type" t.FStar_Syntax_Syntax.pos  in
             mk1 uu____472
         | uu____473 ->
             let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos  in
             let l =
               FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos  in
             mk1
               (FStar_Parser_AST.Construct
                  (l, [(u1, FStar_Parser_AST.Nothing)])))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____485) ->
        let uu____508 = FStar_Syntax_Subst.open_term xs body  in
        (match uu____508 with
         | (xs1,body1) ->
             let patterns =
               FStar_All.pipe_right xs1
                 (FStar_List.map
                    (fun uu____518  ->
                       match uu____518 with
                       | (x,qual) -> resugar_bv_as_pat x qual))
                in
             let body2 = resugar_term body1  in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____537 = FStar_Syntax_Subst.open_comp xs body  in
        (match uu____537 with
         | (xs1,body1) ->
             let body2 = resugar_comp body1  in
             let xs2 =
               let uu____545 =
                 FStar_All.pipe_right xs1
                   (FStar_List.map
                      (fun uu____550  ->
                         match uu____550 with
                         | (b,qual) ->
                             resugar_bv_as_binder b t.FStar_Syntax_Syntax.pos))
                  in
               FStar_All.pipe_right uu____545 FStar_List.rev  in
             let rec aux body3 uu___193_564 =
               match uu___193_564 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3))
                      in
                   aux body4 tl1
                in
             aux body2 xs2)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____577 =
          let uu____580 =
            let uu____581 = FStar_Syntax_Syntax.mk_binder x  in [uu____581]
             in
          FStar_Syntax_Subst.open_term uu____580 phi  in
        (match uu____577 with
         | (x1,phi1) ->
             let uu____584 = FStar_List.hd x1  in
             (match uu____584 with
              | (b,uu____590) ->
                  let b1 = resugar_bv_as_binder b t.FStar_Syntax_Syntax.pos
                     in
                  let uu____592 =
                    let uu____593 =
                      let uu____596 = resugar_term phi1  in (b1, uu____596)
                       in
                    FStar_Parser_AST.Refine uu____593  in
                  mk1 uu____592))
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let uu____613 = resugar_term_as_op e  in
        (match uu____613 with
         | None  ->
             let args1 =
               FStar_All.pipe_right args
                 (FStar_List.map
                    (fun uu____625  ->
                       match uu____625 with | (e1,qual) -> resugar_term e1))
                in
             let e1 = resugar_term e  in
             FStar_List.fold_left
               (fun acc  ->
                  fun x  ->
                    mk1
                      (FStar_Parser_AST.App
                         (acc, x, FStar_Parser_AST.Nothing))) e1 args1
         | Some "tuple" ->
             let args1 =
               FStar_All.pipe_right args
                 (FStar_List.map
                    (fun uu____643  ->
                       match uu____643 with | (e1,qual) -> resugar_term e1))
                in
             (match args1 with
              | fst1::snd1::rest ->
                  let e1 = mk1 (FStar_Parser_AST.Op ("*", [fst1; snd1]))  in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  -> mk1 (FStar_Parser_AST.Op ("*", [e1; x]))) e1
                    rest
              | uu____657 -> failwith "tuple needs at least two arguments.")
         | Some "dtuple" ->
             let rec last1 uu___194_671 =
               match uu___194_671 with
               | hd1::[] -> hd1
               | hd1::tl1 -> last1 tl1
               | uu____709 -> failwith "Empty list."  in
             let uu____719 = last1 args  in
             (match uu____719 with
              | (body,uu____725) ->
                  let uu____730 =
                    let uu____731 = FStar_Syntax_Subst.compress body  in
                    uu____731.FStar_Syntax_Syntax.n  in
                  (match uu____730 with
                   | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____736) ->
                       let uu____759 = FStar_Syntax_Subst.open_term xs body1
                          in
                       (match uu____759 with
                        | (xs1,body2) ->
                            let xs2 =
                              FStar_All.pipe_right xs1
                                (FStar_List.map
                                   (fun uu____769  ->
                                      match uu____769 with
                                      | (b,qual) ->
                                          resugar_bv_as_binder b
                                            t.FStar_Syntax_Syntax.pos))
                               in
                            let body3 = resugar_term body2  in
                            mk1 (FStar_Parser_AST.Sum (xs2, body3)))
                   | uu____776 ->
                       let args1 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____787  ->
                                 match uu____787 with
                                 | (e1,qual) -> resugar_term e1))
                          in
                       let e1 = resugar_term e  in
                       FStar_List.fold_left
                         (fun acc  ->
                            fun x  ->
                              mk1
                                (FStar_Parser_AST.App
                                   (acc, x, FStar_Parser_AST.Nothing))) e1
                         args1))
         | Some ref_read when
             ref_read = FStar_Syntax_Const.sread_lid.FStar_Ident.str ->
             let uu____796 = FStar_List.hd args  in
             (match uu____796 with
              | (t1,uu____806) ->
                  let uu____811 =
                    let uu____812 = FStar_Syntax_Subst.compress t1  in
                    uu____812.FStar_Syntax_Syntax.n  in
                  (match uu____811 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____825 =
                         let uu____826 =
                           let uu____829 = resugar_term t1  in (uu____829, f)
                            in
                         FStar_Parser_AST.Project uu____826  in
                       mk1 uu____825
                   | uu____830 -> resugar_term t1))
         | Some "try_with" ->
             let uu____831 =
               match args with
               | (a1,uu____845)::(a2,uu____847)::[] -> (a1, a2)
               | uu____872 -> failwith "wrong arguments to try_with"  in
             (match uu____831 with
              | (body,handler) ->
                  let decomp term =
                    match term.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____904) ->
                        let uu____927 = FStar_Syntax_Subst.open_term x e1  in
                        (match uu____927 with | (x1,e2) -> e2)
                    | uu____932 -> failwith "unexpected"  in
                  let body1 =
                    let uu____934 = decomp body  in resugar_term uu____934
                     in
                  let handler1 =
                    let uu____936 = decomp handler  in resugar_term uu____936
                     in
                  let e1 =
                    match body1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e1,(uu____939,uu____940,b)::[])
                        -> b
                    | uu____957 -> failwith "unexpected body format"  in
                  let branches =
                    match handler1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | uu____981 -> failwith "unexpected handler format"  in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | Some op when (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body)|FStar_Parser_AST.QForall
                 (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1037 -> (xs, pat, t1)  in
             let resugar body =
               let uu____1045 =
                 let uu____1046 = FStar_Syntax_Subst.compress body  in
                 uu____1046.FStar_Syntax_Syntax.n  in
               match uu____1045 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1051) ->
                   let uu____1074 = FStar_Syntax_Subst.open_term xs body1  in
                   (match uu____1074 with
                    | (xs1,body2) ->
                        let xs2 =
                          FStar_All.pipe_right xs1
                            (FStar_List.map
                               (fun uu____1084  ->
                                  match uu____1084 with
                                  | (b,qual) ->
                                      resugar_bv_as_binder b
                                        t.FStar_Syntax_Syntax.pos))
                           in
                        let uu____1089 =
                          let uu____1094 =
                            let uu____1095 =
                              FStar_Syntax_Subst.compress body2  in
                            uu____1095.FStar_Syntax_Syntax.n  in
                          match uu____1094 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1  in
                              let resugar_pats pats =
                                FStar_List.map
                                  (fun es  ->
                                     FStar_All.pipe_right es
                                       (FStar_List.map
                                          (fun uu____1137  ->
                                             match uu____1137 with
                                             | (e2,uu____1141) ->
                                                 resugar_term e2))) pats
                                 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    resugar_pats pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1156) ->
                                    let uu____1157 =
                                      let uu____1159 =
                                        let uu____1160 = name s r  in
                                        mk1 uu____1160  in
                                      [uu____1159]  in
                                    [uu____1157]
                                | uu____1163 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists"
                                 in
                              (pats, body3)
                          | uu____1168 ->
                              let uu____1169 = resugar_term body2  in
                              ([], uu____1169)
                           in
                        (match uu____1089 with
                         | (pats,body3) ->
                             let uu____1179 = uncurry xs2 pats body3  in
                             (match uu____1179 with
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
               | uu____1206 -> failwith "expect Tm_abs for QForall/QExists"
                in
             (match args with
              | (b,_)::[]|_::(b,_)::[] -> resugar b
              | uu____1239 -> failwith "wrong args format to QForall")
         | Some "alloc" ->
             let uu____1245 = FStar_List.hd args  in
             (match uu____1245 with | (e1,uu____1255) -> resugar_term e1)
         | Some op ->
             let args1 =
               FStar_All.pipe_right args
                 (FStar_List.map
                    (fun uu____1271  ->
                       match uu____1271 with | (e1,qual) -> resugar_term e1))
                in
             mk1 (FStar_Parser_AST.Op (op, args1)))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____1279,t1)::(pat2,uu____1282,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____1357 =
          let uu____1358 =
            let uu____1362 = resugar_term e  in
            let uu____1363 = resugar_term t1  in
            let uu____1364 = resugar_term t2  in
            (uu____1362, uu____1363, uu____1364)  in
          FStar_Parser_AST.If uu____1358  in
        mk1 uu____1357
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____1404 =
          match uu____1404 with
          | (pat,wopt,b) ->
              let pat1 = resugar_match_pat pat  in
              let wopt1 =
                match wopt with
                | None  -> None
                | Some e1 ->
                    let uu____1423 = resugar_term e1  in Some uu____1423
                 in
              let b1 = resugar_term b  in (pat1, wopt1, b1)
           in
        let uu____1426 =
          let uu____1427 =
            let uu____1435 = resugar_term e  in
            let uu____1436 = FStar_List.map resugar_branch branches  in
            (uu____1435, uu____1436)  in
          FStar_Parser_AST.Match uu____1427  in
        mk1 uu____1426
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____1458) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1  in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt  in
        let uu____1511 =
          let uu____1512 =
            let uu____1517 = resugar_term e  in (uu____1517, term, tac_opt1)
             in
          FStar_Parser_AST.Ascribed uu____1512  in
        mk1 uu____1511
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
        let uu____1535 = FStar_Syntax_Subst.open_let_rec bnds body  in
        (match uu____1535 with
         | (bnd,body1) ->
             let resugar_one_binding bnd1 =
               let uu____1551 =
                 let uu____1554 =
                   FStar_Syntax_Util.mk_conj bnd1.FStar_Syntax_Syntax.lbtyp
                     bnd1.FStar_Syntax_Syntax.lbdef
                    in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd1.FStar_Syntax_Syntax.lbunivs uu____1554
                  in
               match uu____1551 with
               | (univs1,td) ->
                   let uu____1561 =
                     let uu____1568 =
                       let uu____1569 = FStar_Syntax_Subst.compress td  in
                       uu____1569.FStar_Syntax_Syntax.n  in
                     match uu____1568 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____1578,(t1,uu____1580)::(d,uu____1582)::[]) ->
                         (t1, d)
                     | uu____1616 -> failwith "Impossibe"  in
                   (match uu____1561 with
                    | (typ,def) ->
                        let uu____1637 =
                          let uu____1641 =
                            let uu____1642 = FStar_Syntax_Subst.compress def
                               in
                            uu____1642.FStar_Syntax_Syntax.n  in
                          match uu____1641 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____1650) ->
                              let uu____1673 =
                                FStar_Syntax_Subst.open_term b t1  in
                              (match uu____1673 with
                               | (b1,t2) -> (b1, t2, true))
                          | uu____1681 -> ([], def, false)  in
                        (match uu____1637 with
                         | (binders,term,is_pat_app) ->
                             let uu____1696 =
                               match bnd1.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____1707 =
                                     let uu____1710 =
                                       let uu____1711 =
                                         FStar_Syntax_Syntax.mk_binder bv  in
                                       [uu____1711]  in
                                     FStar_Syntax_Subst.open_term uu____1710
                                       term
                                      in
                                   (match uu____1707 with
                                    | (x,term1) ->
                                        let uu____1716 = FStar_List.hd x  in
                                        (match uu____1716 with
                                         | (bv1,uu____1724) ->
                                             let uu____1725 =
                                               let uu____1726 =
                                                 let uu____1727 =
                                                   let uu____1731 =
                                                     bv_as_unique_ident bv1
                                                      in
                                                   (uu____1731, None)  in
                                                 FStar_Parser_AST.PatVar
                                                   uu____1727
                                                  in
                                               mk_pat uu____1726  in
                                             (uu____1725, term1)))
                                in
                             (match uu____1696 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (FStar_List.map
                                           (fun uu____1748  ->
                                              match uu____1748 with
                                              | (bv,uu____1752) ->
                                                  let uu____1753 =
                                                    let uu____1754 =
                                                      let uu____1758 =
                                                        bv_as_unique_ident bv
                                                         in
                                                      (uu____1758, None)  in
                                                    FStar_Parser_AST.PatVar
                                                      uu____1754
                                                     in
                                                  mk_pat uu____1753))
                                       in
                                    let uu____1760 =
                                      let uu____1763 = resugar_term term1  in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____1763)
                                       in
                                    let uu____1765 =
                                      let uu____1766 =
                                        FStar_List.map
                                          (fun x  -> x.FStar_Ident.idText)
                                          univs1
                                         in
                                      FStar_All.pipe_right uu____1766
                                        (FStar_String.concat ", ")
                                       in
                                    (uu____1760, uu____1765)
                                  else
                                    (let uu____1773 =
                                       let uu____1776 = resugar_term term1
                                          in
                                       (pat, uu____1776)  in
                                     let uu____1777 =
                                       let uu____1778 =
                                         FStar_List.map
                                           (fun x  -> x.FStar_Ident.idText)
                                           univs1
                                          in
                                       FStar_All.pipe_right uu____1778
                                         (FStar_String.concat ", ")
                                        in
                                     (uu____1773, uu____1777)))))
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
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____1820) ->
        let s =
          let uu____1834 =
            let uu____1835 = FStar_Unionfind.uvar_id u  in
            FStar_All.pipe_right uu____1835 FStar_Util.string_of_int  in
          Prims.strcat "uu___unification_ " uu____1834  in
        let uu____1839 = var s t.FStar_Syntax_Syntax.pos  in mk1 uu____1839
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___195_1849 =
          match uu___195_1849 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____1850 =
                let uu____1851 = FStar_Syntax_Subst.compress e  in
                uu____1851.FStar_Syntax_Syntax.n  in
              (match uu____1850 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____1877 =
                       let uu____1878 = FStar_Syntax_Subst.compress h  in
                       uu____1878.FStar_Syntax_Syntax.n  in
                     match uu____1877 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____1885 = FStar_Syntax_Syntax.lid_of_fv fv
                            in
                         (uu____1885, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____1893 = aux h1  in
                         (match uu____1893 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____1905 -> failwith "wrong Data_app head format"
                      in
                   let uu____1909 = aux head1  in
                   (match uu____1909 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____1924 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos
                                  in
                               (uu____1924, FStar_Parser_AST.UnivApp))
                            universes
                           in
                        let args1 =
                          FStar_List.map
                            (fun uu____1933  ->
                               match uu____1933 with
                               | (t1,uu____1939) ->
                                   let uu____1940 = resugar_term t1  in
                                   (uu____1940, FStar_Parser_AST.Nothing))
                            args
                           in
                        mk1
                          (FStar_Parser_AST.Construct
                             (head2, (FStar_List.append args1 universes1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____1946,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____1952,uu____1953) -> resugar_term e
                    | uu____1958 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____1959 -> failwith "Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e  in
              (match term.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Let (uu____1961,(p,t1)::[],t2) ->
                   mk1 (FStar_Parser_AST.Seq (t1, t2))
               | uu____1972 ->
                   failwith "This case is impossible for sequence")
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
               | uu____1985 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant None
                 in
              let uu____1987 =
                let uu____1988 = FStar_Syntax_Subst.compress e  in
                uu____1988.FStar_Syntax_Syntax.n  in
              (match uu____1987 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____1992;
                      FStar_Syntax_Syntax.pos = uu____1993;
                      FStar_Syntax_Syntax.vars = uu____1994;_},(term,uu____1996)::[])
                   -> resugar_term term
               | uu____2018 -> failwith "mutable_rval should have app term")
           in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2040  ->
                       match uu____2040 with
                       | (x,uu____2044) -> resugar_term x))
                in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2046,p) ->
             let uu____2048 =
               let uu____2049 =
                 let uu____2053 = resugar_term e  in (uu____2053, l, p)  in
               FStar_Parser_AST.Labeled uu____2049  in
             mk1 uu____2048
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1)
           |FStar_Syntax_Syntax.Meta_monadic_lift (name1,_,t1) ->
             let uu____2067 =
               let uu____2068 =
                 let uu____2073 = resugar_term e  in
                 let uu____2074 =
                   let uu____2075 =
                     let uu____2076 =
                       let uu____2082 =
                         let uu____2086 =
                           let uu____2089 = resugar_term t1  in
                           (uu____2089, FStar_Parser_AST.Nothing)  in
                         [uu____2086]  in
                       (name1, uu____2082)  in
                     FStar_Parser_AST.Construct uu____2076  in
                   mk1 uu____2075  in
                 (uu____2073, uu____2074, None)  in
               FStar_Parser_AST.Ascribed uu____2068  in
             mk1 uu____2067)
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
          let uu____2168 = resugar_term c1.FStar_Syntax_Syntax.result_typ  in
          (uu____2168, FStar_Parser_AST.Nothing)  in
        let args =
          if
            FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Const.effect_Lemma_lid
          then
            let rec aux l uu___196_2201 =
              match uu___196_2201 with
              | [] -> l
              | (t,aq)::tl1 ->
                  (match t.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.true_lid
                       -> aux l tl1
                   | FStar_Syntax_Syntax.Tm_meta uu____2243 -> aux l tl1
                   | uu____2248 -> aux ((t, aq) :: l) tl1)
               in
            aux [] c1.FStar_Syntax_Syntax.effect_args
          else c1.FStar_Syntax_Syntax.effect_args  in
        let args1 =
          FStar_List.map
            (fun uu____2268  ->
               match uu____2268 with
               | (e,uu____2274) ->
                   let uu____2275 = resugar_term e  in
                   (uu____2275, FStar_Parser_AST.Nothing)) args
           in
        let rec aux l uu___197_2289 =
          match uu___197_2289 with
          | [] -> l
          | hd1::tl1 ->
              (match hd1 with
               | FStar_Syntax_Syntax.DECREASES e ->
                   let e1 =
                     let uu____2309 = resugar_term e  in
                     (uu____2309, FStar_Parser_AST.Nothing)  in
                   aux (e1 :: l) tl1
               | uu____2312 -> aux l tl1)
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
          let uu____2329 =
            let uu____2330 = bv_as_unique_ident x  in
            FStar_Parser_AST.Variable uu____2330  in
          FStar_Parser_AST.mk_binder uu____2329 r FStar_Parser_AST.Type_level
            None
      | uu____2331 ->
          let uu____2332 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____2332
          then
            FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
              FStar_Parser_AST.Type_level None
          else
            (let uu____2334 =
               let uu____2335 =
                 let uu____2338 = bv_as_unique_ident x  in (uu____2338, e)
                  in
               FStar_Parser_AST.Annotated uu____2335  in
             FStar_Parser_AST.mk_binder uu____2334 r
               FStar_Parser_AST.Type_level None)

and resugar_bv_as_pat :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual -> FStar_Parser_AST.pattern
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____2345 = FStar_Syntax_Syntax.range_of_bv x  in
        FStar_Parser_AST.mk_pattern a uu____2345  in
      let uu____2346 =
        let uu____2347 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
        uu____2347.FStar_Syntax_Syntax.n  in
      match uu____2346 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix
             in
          if i = (Prims.parse_int "0")
          then mk1 FStar_Parser_AST.PatWild
          else
            (let uu____2352 =
               let uu____2353 =
                 let uu____2357 = bv_as_unique_ident x  in
                 let uu____2358 = resugar_arg_qual qual  in
                 (uu____2357, uu____2358)  in
               FStar_Parser_AST.PatVar uu____2353  in
             mk1 uu____2352)
      | uu____2361 ->
          let pat =
            let uu____2363 =
              let uu____2364 =
                let uu____2368 = bv_as_unique_ident x  in
                let uu____2369 = resugar_arg_qual qual  in
                (uu____2368, uu____2369)  in
              FStar_Parser_AST.PatVar uu____2364  in
            mk1 uu____2363  in
          let uu____2372 =
            let uu____2373 =
              let uu____2376 = resugar_term x.FStar_Syntax_Syntax.sort  in
              (pat, uu____2376)  in
            FStar_Parser_AST.PatAscribed uu____2373  in
          mk1 uu____2372

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
              (fun uu____2428  -> match uu____2428 with | (p2,b) -> aux p2)
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
              (fun uu____2457  -> match uu____2457 with | (p2,b) -> aux p2)
              args
             in
          if
            FStar_Syntax_Util.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____2469;
             FStar_Syntax_Syntax.fv_delta = uu____2470;
             FStar_Syntax_Syntax.fv_qual = Some
               (FStar_Syntax_Syntax.Record_ctor uu____2471);_},args)
          -> failwith "PatRecord not resugared yet"
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____2505  -> match uu____2505 with | (p2,b) -> aux p2)
              args
             in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____2516 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
             in
          (match uu____2516 with
           | Some op -> mk1 (FStar_Parser_AST.PatOp op)
           | None  ->
               let uu____2519 =
                 let uu____2520 =
                   let uu____2524 = bv_as_unique_ident v1  in
                   (uu____2524, None)  in
                 FStar_Parser_AST.PatVar uu____2520  in
               mk1 uu____2519)
      | FStar_Syntax_Syntax.Pat_wild uu____2526 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____2534 =
              let uu____2535 =
                let uu____2539 = bv_as_unique_ident bv  in (uu____2539, None)
                 in
              FStar_Parser_AST.PatVar uu____2535  in
            mk1 uu____2534  in
          let uu____2541 =
            let uu____2542 =
              let uu____2545 = resugar_term term  in (pat, uu____2545)  in
            FStar_Parser_AST.PatAscribed uu____2542  in
          mk1 uu____2541
       in
    aux p
