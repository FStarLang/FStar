open Prims
let semi: FStar_Format.doc = FStar_Format.text ";"
let comma: FStar_Format.doc = FStar_Format.text ","
let dot: FStar_Format.doc = FStar_Format.text "."
let colon: FStar_Format.doc = FStar_Format.text ":"
let ws: FStar_Format.doc = FStar_Format.break1
let escape_or:
  (FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string =
  fun fallback  ->
    fun uu___96_9  ->
      match uu___96_9 with
      | c when c = '\\' -> "\\\\"
      | c when c = ' ' -> " "
      | c when c = '\b' -> "\\b"
      | c when c = '\t' -> "\\t"
      | c when c = '\r' -> "\\r"
      | c when c = '\n' -> "\\n"
      | c when c = '\'' -> "\\'"
      | c when c = '"' -> "\\\""
      | c when FStar_Util.is_letter_or_digit c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_punctuation c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_symbol c -> FStar_Util.string_of_char c
      | c -> fallback c
let jstr_escape: Prims.string -> Prims.string =
  fun s  -> FStar_String.collect (escape_or FStar_Util.string_of_char) s
let escape_char:
  (FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string =
  fun fallback  ->
    fun uu___97_35  ->
      match uu___97_35 with
      | c when c = '\'' -> "_"
      | c when FStar_Util.is_letter_or_digit c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_punctuation c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_symbol c -> FStar_Util.string_of_char c
      | c -> fallback c
let remove_chars_t: Prims.string -> Prims.string =
  fun s  -> FStar_String.collect (escape_char FStar_Util.string_of_char) s
let print_op_un: FStar_Extraction_JavaScript_Ast.op_un -> FStar_Format.doc =
  fun uu___98_48  ->
    match uu___98_48 with
    | FStar_Extraction_JavaScript_Ast.JSU_Minus  -> FStar_Format.text "-"
    | FStar_Extraction_JavaScript_Ast.JSU_Not  -> FStar_Format.text "!"
let print_op_bin: FStar_Extraction_JavaScript_Ast.op_bin -> FStar_Format.doc
  =
  fun uu___99_51  ->
    match uu___99_51 with
    | FStar_Extraction_JavaScript_Ast.JSB_Equal  -> FStar_Format.text "=="
    | FStar_Extraction_JavaScript_Ast.JSB_NotEqual  -> FStar_Format.text "!="
    | FStar_Extraction_JavaScript_Ast.JSB_LessThan  -> FStar_Format.text "<"
    | FStar_Extraction_JavaScript_Ast.JSB_LessThanEqual  ->
        FStar_Format.text "<="
    | FStar_Extraction_JavaScript_Ast.JSB_GreaterThan  ->
        FStar_Format.text ">"
    | FStar_Extraction_JavaScript_Ast.JSB_GreaterThanEqual  ->
        FStar_Format.text ">="
    | FStar_Extraction_JavaScript_Ast.JSB_Plus  -> FStar_Format.text "+"
    | FStar_Extraction_JavaScript_Ast.JSB_Minus  -> FStar_Format.text "-"
    | FStar_Extraction_JavaScript_Ast.JSB_Mult  -> FStar_Format.text "*"
    | FStar_Extraction_JavaScript_Ast.JSB_Div  -> FStar_Format.text "/"
    | FStar_Extraction_JavaScript_Ast.JSB_Mod  -> FStar_Format.text "%"
    | FStar_Extraction_JavaScript_Ast.JSB_StrictEqual  ->
        FStar_Format.text "==="
let print_op_log: FStar_Extraction_JavaScript_Ast.op_log -> FStar_Format.doc
  =
  fun uu___100_54  ->
    match uu___100_54 with
    | FStar_Extraction_JavaScript_Ast.JSL_Or  -> FStar_Format.text "||"
    | FStar_Extraction_JavaScript_Ast.JSL_And  -> FStar_Format.text "&&"
let keywords_js: Prims.string Prims.list =
  ["abstract";
  "arguments";
  "boolean";
  "break";
  "byte";
  "case";
  "catch";
  "char";
  "class";
  "const";
  "continue";
  "debugger";
  "default";
  "delete";
  "do";
  "double";
  "else";
  "enum";
  "eval";
  "export";
  "extends";
  "false";
  "final";
  "finally";
  "float";
  "for";
  "function";
  "goto";
  "if";
  "implements";
  "import";
  "in";
  "instanceof";
  "int";
  "interface";
  "let";
  "long";
  "native";
  "new";
  "null";
  "package";
  "private";
  "protected";
  "public";
  "return";
  "short";
  "static";
  "super";
  "switch";
  "synchronized";
  "this";
  "throw";
  "throws";
  "transient";
  "true";
  "try";
  "typeof";
  "var";
  "void";
  "volatile";
  "while";
  "with";
  "yield"]
let remove_chars: Prims.string -> FStar_Format.doc =
  fun s  ->
    if FStar_List.existsb (fun x  -> s = x) keywords_js
    then
      let v1 = FStar_List.tryFind (fun x  -> s = x) keywords_js in
      ((let uu____64 = FStar_Util.must v1 in
        FStar_Util.print1
          "Warning: this name is a keyword in JavaScript: %s \n" uu____64);
       (let uu____65 =
          let uu____67 =
            let uu____69 =
              let uu____70 = remove_chars_t s in FStar_Format.text uu____70 in
            [uu____69] in
          (FStar_Format.text "_") :: uu____67 in
        FStar_Format.reduce uu____65))
    else (let uu____72 = remove_chars_t s in FStar_Format.text uu____72)
let rec pretty_print: FStar_Extraction_JavaScript_Ast.t -> FStar_Format.doc =
  fun program  ->
    let uu____136 =
      let uu____138 =
        FStar_List.map
          (fun uu___101_140  ->
             match uu___101_140 with
             | FStar_Extraction_JavaScript_Ast.JS_Statement s ->
                 (match s with
                  | FStar_Extraction_JavaScript_Ast.JSS_Block l ->
                      pretty_print_statements l
                  | uu____144 -> pretty_print_statement s)) program in
      FStar_List.append
        [FStar_Format.text "/* @flow */"; FStar_Format.hardline] uu____138 in
    FStar_Format.reduce uu____136
and pretty_print_statement:
  FStar_Extraction_JavaScript_Ast.statement_t -> FStar_Format.doc =
  fun p  ->
    let optws s =
      match s with
      | FStar_Extraction_JavaScript_Ast.JSS_Block b ->
          pretty_print_statements b
      | uu____152 -> pretty_print_statement s in
    match p with
    | FStar_Extraction_JavaScript_Ast.JSS_Empty  -> semi
    | FStar_Extraction_JavaScript_Ast.JSS_Block l ->
        let uu____155 =
          let uu____157 =
            let uu____159 =
              let uu____161 = pretty_print_statements l in
              [uu____161; FStar_Format.text "}"; FStar_Format.hardline] in
            (FStar_Format.text "{") :: uu____159 in
          ws :: uu____157 in
        FStar_Format.reduce uu____155
    | FStar_Extraction_JavaScript_Ast.JSS_Expression e ->
        let uu____163 =
          let uu____165 =
            let uu____167 = pretty_print_exp e in
            [uu____167; semi; FStar_Format.hardline] in
          ws :: uu____165 in
        FStar_Format.reduce uu____163
    | FStar_Extraction_JavaScript_Ast.JSS_If (c,t,f) ->
        let uu____173 =
          let uu____175 =
            let uu____177 =
              let uu____179 =
                let uu____180 = pretty_print_exp c in
                FStar_Format.parens uu____180 in
              let uu____181 =
                let uu____183 =
                  let uu____185 =
                    let uu____187 = optws t in
                    let uu____188 =
                      let uu____190 =
                        let uu____192 =
                          match f with
                          | None  -> FStar_Format.empty
                          | Some s ->
                              let uu____194 =
                                let uu____196 =
                                  let uu____198 =
                                    let uu____200 =
                                      let uu____202 = optws s in
                                      [uu____202; FStar_Format.text "}"] in
                                    (FStar_Format.text "{") :: uu____200 in
                                  (FStar_Format.text "else") :: uu____198 in
                                ws :: uu____196 in
                              FStar_Format.reduce uu____194 in
                        [uu____192; FStar_Format.hardline] in
                      (FStar_Format.text "}") :: uu____190 in
                    uu____187 :: uu____188 in
                  FStar_Format.hardline :: uu____185 in
                (FStar_Format.text "{") :: uu____183 in
              uu____179 :: uu____181 in
            (FStar_Format.text "if") :: uu____177 in
          ws :: uu____175 in
        FStar_Format.reduce uu____173
    | FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id,uu____204),lt1,t) ->
        let uu____216 =
          let uu____218 =
            let uu____220 =
              let uu____222 = remove_chars id in
              let uu____223 =
                let uu____225 = print_decl_t lt1 in
                let uu____226 =
                  let uu____228 =
                    let uu____230 = print_typ t in
                    [uu____230; semi; FStar_Format.hardline] in
                  (FStar_Format.text "=") :: uu____228 in
                uu____225 :: uu____226 in
              uu____222 :: uu____223 in
            (FStar_Format.text "type ") :: uu____220 in
          ws :: uu____218 in
        FStar_Format.reduce uu____216
    | FStar_Extraction_JavaScript_Ast.JSS_Return e ->
        let uu____233 =
          let uu____235 =
            let uu____237 =
              let uu____239 =
                match e with
                | None  -> FStar_Format.empty
                | Some v1 ->
                    let uu____241 =
                      let uu____243 =
                        let uu____245 = pretty_print_exp v1 in [uu____245] in
                      ws :: uu____243 in
                    FStar_Format.reduce uu____241 in
              [uu____239; semi; FStar_Format.hardline] in
            (FStar_Format.text "return") :: uu____237 in
          ws :: uu____235 in
        FStar_Format.reduce uu____233
    | FStar_Extraction_JavaScript_Ast.JSS_Throw e ->
        let uu____247 =
          let uu____249 =
            let uu____251 =
              let uu____253 = pretty_print_exp e in [uu____253; semi] in
            (FStar_Format.text "throw ") :: uu____251 in
          ws :: uu____249 in
        FStar_Format.reduce uu____247
    | FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((p1,e),k) ->
        (match p1 with
         | FStar_Extraction_JavaScript_Ast.JGP_Identifier (n1,uu____263) when
             n1 = "_" ->
             (match e with
              | Some v1 when
                  v1 =
                    (FStar_Extraction_JavaScript_Ast.JSE_Literal
                       (FStar_Extraction_JavaScript_Ast.JSV_Null, ""))
                  -> FStar_Format.empty
              | Some v1 ->
                  let uu____268 =
                    let uu____270 = pretty_print_exp v1 in
                    [uu____270; semi; FStar_Format.hardline] in
                  FStar_Format.reduce uu____268
              | None  -> FStar_Format.empty)
         | uu____271 ->
             let uu____272 =
               let uu____274 = print_kind_var k in
               let uu____275 =
                 let uu____277 = print_pattern p1 true in
                 let uu____278 =
                   let uu____280 =
                     match e with
                     | None  -> FStar_Format.empty
                     | Some v1 ->
                         let uu____282 =
                           let uu____284 =
                             let uu____286 = pretty_print_exp v1 in
                             [uu____286] in
                           (FStar_Format.text "=") :: uu____284 in
                         FStar_Format.reduce uu____282 in
                   [uu____280; semi; FStar_Format.hardline] in
                 uu____277 :: uu____278 in
               uu____274 :: uu____275 in
             FStar_Format.reduce uu____272)
    | FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (d,k) ->
        (match d with
         | FStar_Extraction_JavaScript_Ast.JSE_Declaration s ->
             (match s with
              | FStar_Extraction_JavaScript_Ast.JSS_Block l ->
                  let uu____292 =
                    FStar_List.map (fun x  -> print_export_stmt x) l in
                  FStar_Format.reduce uu____292
              | uu____295 ->
                  let uu____296 =
                    let uu____298 =
                      let uu____300 = optws s in
                      [uu____300; FStar_Format.hardline] in
                    (FStar_Format.text "export ") :: uu____298 in
                  FStar_Format.reduce uu____296)
         | FStar_Extraction_JavaScript_Ast.JSE_Expression e ->
             let uu____302 =
               let uu____304 =
                 let uu____306 = pretty_print_exp e in
                 [uu____306; FStar_Format.hardline] in
               (FStar_Format.text "export ") :: uu____304 in
             FStar_Format.reduce uu____302)
    | FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration d ->
        let uu____311 =
          let uu____313 =
            let uu____315 =
              let uu____316 = jstr_escape (fst d) in
              FStar_Format.text uu____316 in
            let uu____318 =
              let uu____320 =
                let uu____322 =
                  let uu____324 =
                    let uu____325 = jstr_escape (fst d) in
                    FStar_Format.text uu____325 in
                  [uu____324;
                  FStar_Format.text "\"";
                  semi;
                  FStar_Format.hardline] in
                (FStar_Format.text "\"./") :: uu____322 in
              (FStar_Format.text " from ") :: uu____320 in
            uu____315 :: uu____318 in
          (FStar_Format.text "import * as ") :: uu____313 in
        FStar_Format.reduce uu____311
    | FStar_Extraction_JavaScript_Ast.JSS_Seq l -> pretty_print_statements l
and pretty_print_statements:
  FStar_Extraction_JavaScript_Ast.statement_t Prims.list -> FStar_Format.doc
  =
  fun l  ->
    let uu____331 = FStar_List.map pretty_print_statement l in
    FStar_Format.reduce uu____331
and print_export_stmt:
  FStar_Extraction_JavaScript_Ast.statement_t -> FStar_Format.doc =
  fun s  ->
    match s with
    | FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((p,e),k) ->
        (match p with
         | FStar_Extraction_JavaScript_Ast.JGP_Identifier (n1,uu____343) when
             n1 = "_" ->
             (match e with
              | Some v1 when
                  v1 =
                    (FStar_Extraction_JavaScript_Ast.JSE_Literal
                       (FStar_Extraction_JavaScript_Ast.JSV_Null, ""))
                  -> FStar_Format.empty
              | Some v1 ->
                  let uu____348 =
                    let uu____350 = pretty_print_exp v1 in
                    [uu____350; semi; FStar_Format.hardline] in
                  FStar_Format.reduce uu____348
              | None  -> FStar_Format.empty)
         | uu____351 ->
             let uu____352 =
               let uu____354 =
                 let uu____356 = pretty_print_statement s in
                 [uu____356; FStar_Format.hardline] in
               (FStar_Format.text "export ") :: uu____354 in
             FStar_Format.reduce uu____352)
    | uu____357 ->
        let uu____358 =
          let uu____360 =
            let uu____362 = pretty_print_statement s in
            [uu____362; FStar_Format.hardline] in
          (FStar_Format.text "export ") :: uu____360 in
        FStar_Format.reduce uu____358
and pretty_print_exp:
  FStar_Extraction_JavaScript_Ast.expression_t -> FStar_Format.doc =
  fun uu___102_363  ->
    match uu___102_363 with
    | FStar_Extraction_JavaScript_Ast.JSE_Array l ->
        (match l with
         | Some v1 ->
             let uu____370 =
               let uu____372 =
                 let uu____374 =
                   let uu____375 = FStar_List.map pretty_print_exp v1 in
                   FStar_All.pipe_right uu____375
                     (FStar_Format.combine comma) in
                 [uu____374; FStar_Format.text "]"] in
               (FStar_Format.text "[") :: uu____372 in
             FStar_Format.reduce uu____370
         | None  ->
             FStar_Format.reduce
               [FStar_Format.text "["; FStar_Format.text "]"])
    | FStar_Extraction_JavaScript_Ast.JSE_Object l ->
        let uu____381 =
          let uu____383 =
            let uu____385 =
              let uu____386 = FStar_List.map pretty_print_obj l in
              FStar_All.pipe_right uu____386 (FStar_Format.combine comma) in
            [uu____385; FStar_Format.text "}"] in
          (FStar_Format.text "{") :: uu____383 in
        FStar_Format.reduce uu____381
    | FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction
        (uu____389,args,body,ret_t,decl_vars) ->
        let uu____410 =
          let uu____412 = print_decl_t decl_vars in
          let uu____413 =
            let uu____415 =
              let uu____416 = print_body body in
              print_arrow_fun args uu____416 ret_t in
            [uu____415] in
          uu____412 :: uu____413 in
        FStar_Format.reduce uu____410
    | FStar_Extraction_JavaScript_Ast.JSE_Unary (o,e) ->
        let uu____419 =
          let uu____421 = let uu____423 = pretty_print_exp e in [uu____423] in
          (print_op_un o) :: uu____421 in
        FStar_Format.reduce uu____419
    | FStar_Extraction_JavaScript_Ast.JSE_Binary (o,e1,e2) ->
        let uu____427 =
          let uu____429 =
            let uu____431 = pretty_print_exp e1 in
            let uu____432 =
              let uu____434 =
                let uu____436 = pretty_print_exp e2 in
                [uu____436; FStar_Format.text ")"] in
              (print_op_bin o) :: uu____434 in
            uu____431 :: uu____432 in
          (FStar_Format.text "(") :: uu____429 in
        FStar_Format.reduce uu____427
    | FStar_Extraction_JavaScript_Ast.JSE_Assignment (p,e) ->
        (match p with
         | FStar_Extraction_JavaScript_Ast.JGP_Identifier (n1,uu____440) when
             n1 = "_" -> pretty_print_exp e
         | uu____443 ->
             let uu____444 =
               let uu____446 = print_pattern p false in
               let uu____447 =
                 let uu____449 =
                   let uu____451 = pretty_print_exp e in [uu____451] in
                 (FStar_Format.text "=") :: uu____449 in
               uu____446 :: uu____447 in
             FStar_Format.reduce uu____444)
    | FStar_Extraction_JavaScript_Ast.JSE_Logical (o,e1,e2) ->
        let uu____455 =
          let uu____457 = pretty_print_exp e1 in
          let uu____458 =
            let uu____460 =
              let uu____462 = pretty_print_exp e2 in [uu____462] in
            (print_op_log o) :: uu____460 in
          uu____457 :: uu____458 in
        FStar_Format.reduce uu____455
    | FStar_Extraction_JavaScript_Ast.JSE_Call (e,l) ->
        let le =
          let uu____468 =
            FStar_List.map
              (fun x  ->
                 let uu____471 = pretty_print_exp x in
                 FStar_Format.parens uu____471) l in
          FStar_All.pipe_right uu____468
            (FStar_Format.combine FStar_Format.empty) in
        let uu____473 =
          let uu____475 = pretty_print_exp e in
          [uu____475;
          (match l with | [] -> FStar_Format.text "()" | uu____476 -> le)] in
        FStar_Format.reduce uu____473
    | FStar_Extraction_JavaScript_Ast.JSE_Member (o,p) ->
        let uu____480 =
          let uu____482 = pretty_print_exp o in
          let uu____483 =
            let uu____485 = pretty_print_propmem p in [uu____485] in
          uu____482 :: uu____483 in
        FStar_Format.reduce uu____480
    | FStar_Extraction_JavaScript_Ast.JSE_Identifier (id,t) ->
        remove_chars id
    | FStar_Extraction_JavaScript_Ast.JSE_Literal l -> print_literal l
    | FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e,t) ->
        let uu____495 =
          let uu____497 =
            let uu____499 = pretty_print_exp e in
            let uu____500 =
              let uu____502 =
                let uu____504 = print_typ t in
                [uu____504; FStar_Format.text ")"] in
              colon :: uu____502 in
            uu____499 :: uu____500 in
          (FStar_Format.text "(") :: uu____497 in
        FStar_Format.reduce uu____495
and print_decl_t: Prims.string Prims.list option -> FStar_Format.doc =
  fun lt1  ->
    match lt1 with
    | Some l ->
        let uu____511 =
          let uu____513 =
            let uu____515 =
              let uu____516 = FStar_List.map (fun s  -> remove_chars s) l in
              FStar_All.pipe_right uu____516 (FStar_Format.combine comma) in
            [uu____515; FStar_Format.text ">"] in
          (FStar_Format.text "<") :: uu____513 in
        FStar_Format.reduce uu____511
    | None  -> FStar_Format.empty
and print_arrow_fun:
  FStar_Extraction_JavaScript_Ast.pattern_t Prims.list ->
    FStar_Format.doc ->
      FStar_Extraction_JavaScript_Ast.typ option -> FStar_Format.doc
  =
  fun args  ->
    fun body  ->
      fun ret_t  ->
        let ret_t1 =
          match ret_t with
          | None  -> FStar_Format.empty
          | Some v1 ->
              let uu____528 =
                let uu____530 =
                  let uu____532 =
                    let uu____533 = print_typ v1 in
                    FStar_Format.parens uu____533 in
                  [uu____532] in
                colon :: uu____530 in
              FStar_Format.reduce uu____528 in
        print_arrow_fun_p args body ret_t1 true
and print_arrow_fun_p:
  FStar_Extraction_JavaScript_Ast.pattern_t Prims.list ->
    FStar_Format.doc -> FStar_Format.doc -> Prims.bool -> FStar_Format.doc
  =
  fun args  ->
    fun body  ->
      fun ret_t  ->
        fun print_ret_t  ->
          let ret_t1 = if print_ret_t then ret_t else FStar_Format.empty in
          match args with
          | [] ->
              FStar_Format.reduce
                [FStar_Format.text "()"; FStar_Format.text "=>"; body]
          | x::[] ->
              let uu____542 =
                let uu____544 =
                  let uu____545 = print_pattern x true in
                  FStar_Format.parens uu____545 in
                [uu____544; ret_t1; FStar_Format.text "=>"; body] in
              FStar_Format.reduce uu____542
          | hd1::tl1 ->
              let uu____549 =
                let uu____551 =
                  let uu____552 = print_pattern hd1 true in
                  FStar_Format.parens uu____552 in
                let uu____553 =
                  let uu____555 =
                    let uu____557 =
                      let uu____559 =
                        let uu____560 =
                          print_arrow_fun_p tl1 body ret_t1 false in
                        FStar_Format.parens uu____560 in
                      [uu____559] in
                    (FStar_Format.text "=>") :: uu____557 in
                  ret_t1 :: uu____555 in
                uu____551 :: uu____553 in
              FStar_Format.reduce uu____549
and pretty_print_obj:
  FStar_Extraction_JavaScript_Ast.property_obj_t -> FStar_Format.doc =
  fun el  ->
    match el with
    | FStar_Extraction_JavaScript_Ast.JSPO_Property (k,e,uu____564) ->
        let uu____565 =
          let uu____567 = pretty_print_prop_key k in
          let uu____568 =
            let uu____570 = let uu____572 = pretty_print_exp e in [uu____572] in
            (FStar_Format.text ":") :: uu____570 in
          uu____567 :: uu____568 in
        FStar_Format.reduce uu____565
    | FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty e ->
        pretty_print_exp e
and pretty_print_prop_key:
  FStar_Extraction_JavaScript_Ast.object_prop_key_t -> FStar_Format.doc =
  fun k  ->
    match k with
    | FStar_Extraction_JavaScript_Ast.JSO_Literal l -> print_literal l
    | FStar_Extraction_JavaScript_Ast.JSO_Identifier (id,t) ->
        let uu____582 = jstr_escape id in FStar_Format.text uu____582
    | FStar_Extraction_JavaScript_Ast.JSO_Computed e -> pretty_print_exp e
and pretty_print_propmem:
  FStar_Extraction_JavaScript_Ast.propmem_t -> FStar_Format.doc =
  fun p  ->
    match p with
    | FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i,t) ->
        let uu____589 =
          let uu____591 =
            let uu____593 =
              let uu____594 = jstr_escape i in FStar_Format.text uu____594 in
            [uu____593] in
          (FStar_Format.text ".") :: uu____591 in
        FStar_Format.reduce uu____589
    | FStar_Extraction_JavaScript_Ast.JSPM_Expression e ->
        let uu____596 =
          let uu____598 =
            let uu____600 = pretty_print_exp e in
            [uu____600; FStar_Format.text "]"] in
          (FStar_Format.text "[") :: uu____598 in
        FStar_Format.reduce uu____596
and print_typ: FStar_Extraction_JavaScript_Ast.typ -> FStar_Format.doc =
  fun uu___103_601  ->
    match uu___103_601 with
    | FStar_Extraction_JavaScript_Ast.JST_Any  -> FStar_Format.text "any"
    | FStar_Extraction_JavaScript_Ast.JST_Void  -> FStar_Format.text "void"
    | FStar_Extraction_JavaScript_Ast.JST_Null  -> FStar_Format.text "null"
    | FStar_Extraction_JavaScript_Ast.JST_Number  ->
        FStar_Format.text "number"
    | FStar_Extraction_JavaScript_Ast.JST_String  ->
        FStar_Format.text "string"
    | FStar_Extraction_JavaScript_Ast.JST_Boolean  ->
        FStar_Format.text "boolean"
    | FStar_Extraction_JavaScript_Ast.JST_Function (args,ret_t,decl_vars) ->
        let uu____621 =
          let uu____623 = print_decl_t decl_vars in
          let uu____624 =
            let uu____626 = print_fun_typ args ret_t in [uu____626] in
          uu____623 :: uu____624 in
        FStar_Format.reduce uu____621
    | FStar_Extraction_JavaScript_Ast.JST_Object lp ->
        let uu____631 =
          let uu____633 =
            let uu____635 =
              let uu____636 =
                FStar_List.map
                  (fun uu____640  ->
                     match uu____640 with
                     | (k,t) ->
                         let uu____645 =
                           let uu____647 = pretty_print_prop_key k in
                           let uu____648 =
                             let uu____650 =
                               let uu____652 = print_typ t in [uu____652] in
                             (FStar_Format.text ":") :: uu____650 in
                           uu____647 :: uu____648 in
                         FStar_Format.reduce uu____645) lp in
              FStar_All.pipe_right uu____636 (FStar_Format.combine comma) in
            [uu____635; FStar_Format.text "}"] in
          (FStar_Format.text "{") :: uu____633 in
        FStar_Format.reduce uu____631
    | FStar_Extraction_JavaScript_Ast.JST_Array t ->
        let uu____655 =
          let uu____657 =
            let uu____659 =
              let uu____661 = print_typ t in
              [uu____661; FStar_Format.text ">"] in
            (FStar_Format.text "<") :: uu____659 in
          (FStar_Format.text "Array") :: uu____657 in
        FStar_Format.reduce uu____655
    | FStar_Extraction_JavaScript_Ast.JST_Union l ->
        let uu____664 =
          let uu____666 =
            let uu____667 = FStar_List.map print_typ l in
            FStar_All.pipe_right uu____667
              (FStar_Format.combine (FStar_Format.text "|")) in
          [uu____666] in
        FStar_Format.reduce uu____664
    | FStar_Extraction_JavaScript_Ast.JST_Intersection l ->
        let uu____672 =
          let uu____674 =
            let uu____675 = FStar_List.map print_typ l in
            FStar_All.pipe_right uu____675
              (FStar_Format.combine (FStar_Format.text "&")) in
          [uu____674] in
        FStar_Format.reduce uu____672
    | FStar_Extraction_JavaScript_Ast.JST_Tuple lt1 ->
        let uu____680 =
          let uu____682 =
            let uu____684 =
              let uu____685 = FStar_List.map print_typ lt1 in
              FStar_All.pipe_right uu____685 (FStar_Format.combine comma) in
            [uu____684; FStar_Format.text "]"] in
          (FStar_Format.text "[") :: uu____682 in
        FStar_Format.reduce uu____680
    | FStar_Extraction_JavaScript_Ast.JST_StringLiteral (s,uu____689) ->
        let uu____690 =
          let uu____691 =
            let uu____692 = jstr_escape s in Prims.strcat uu____692 "\"" in
          Prims.strcat "\"" uu____691 in
        FStar_Format.text uu____690
    | FStar_Extraction_JavaScript_Ast.JST_Generic (n1,lt1) ->
        let print_lt =
          match lt1 with
          | None  -> FStar_Format.empty
          | Some v1 ->
              let uu____704 =
                let uu____706 =
                  let uu____708 =
                    let uu____709 = FStar_List.map print_typ v1 in
                    FStar_All.pipe_right uu____709
                      (FStar_Format.combine comma) in
                  [uu____708; FStar_Format.text ">"] in
                (FStar_Format.text "<") :: uu____706 in
              FStar_Format.reduce uu____704 in
        let uu____712 =
          let uu____714 = remove_chars n1 in [uu____714; print_lt] in
        FStar_Format.reduce uu____712
and print_fun_typ:
  ((Prims.string* FStar_Extraction_JavaScript_Ast.typ option)*
    FStar_Extraction_JavaScript_Ast.typ) Prims.list ->
    FStar_Extraction_JavaScript_Ast.typ -> FStar_Format.doc
  =
  fun args  ->
    fun ret_t  ->
      let print_arg uu____731 =
        match uu____731 with
        | ((id,uu____738),t) ->
            let uu____745 =
              let uu____747 =
                let uu____748 = jstr_escape id in FStar_Format.text uu____748 in
              let uu____749 =
                let uu____751 = let uu____753 = print_typ t in [uu____753] in
                colon :: uu____751 in
              uu____747 :: uu____749 in
            FStar_Format.reduce uu____745 in
      match args with
      | [] ->
          let uu____759 =
            let uu____761 =
              let uu____763 = let uu____765 = print_typ ret_t in [uu____765] in
              (FStar_Format.text "=>") :: uu____763 in
            (FStar_Format.text "()") :: uu____761 in
          FStar_Format.reduce uu____759
      | x::[] ->
          let uu____782 =
            let uu____784 =
              let uu____785 = print_arg x in FStar_Format.parens uu____785 in
            let uu____786 =
              let uu____788 =
                let uu____790 =
                  let uu____791 = print_typ ret_t in
                  FStar_Format.parens uu____791 in
                [uu____790] in
              (FStar_Format.text "=>") :: uu____788 in
            uu____784 :: uu____786 in
          FStar_Format.reduce uu____782
      | hd1::tl1 ->
          let uu____810 =
            let uu____812 =
              let uu____813 = print_arg hd1 in FStar_Format.parens uu____813 in
            let uu____814 =
              let uu____816 =
                let uu____818 =
                  let uu____819 = print_fun_typ tl1 ret_t in
                  FStar_Format.parens uu____819 in
                [uu____818] in
              (FStar_Format.text "=>") :: uu____816 in
            uu____812 :: uu____814 in
          FStar_Format.reduce uu____810
and print_literal:
  (FStar_Extraction_JavaScript_Ast.value_t* Prims.string) -> FStar_Format.doc
  =
  fun uu____820  ->
    match uu____820 with
    | (v1,s) ->
        (match (v1, s) with
         | (FStar_Extraction_JavaScript_Ast.JSV_String s1,uu____826) ->
             let uu____827 =
               let uu____828 =
                 let uu____829 = jstr_escape s1 in
                 Prims.strcat uu____829 "\"" in
               Prims.strcat "\"" uu____828 in
             FStar_Format.text uu____827
         | (FStar_Extraction_JavaScript_Ast.JSV_Boolean b,uu____831) ->
             let uu____832 = FStar_Util.string_of_bool b in
             FStar_Format.text uu____832
         | (FStar_Extraction_JavaScript_Ast.JSV_Null ,uu____833) ->
             FStar_Format.text "null"
         | (FStar_Extraction_JavaScript_Ast.JSV_Number f,s1) ->
             FStar_Format.text s1)
and print_kind_var:
  FStar_Extraction_JavaScript_Ast.kind_var_t -> FStar_Format.doc =
  fun uu___104_836  ->
    match uu___104_836 with
    | FStar_Extraction_JavaScript_Ast.JSV_Var  -> FStar_Format.text "var "
    | FStar_Extraction_JavaScript_Ast.JSV_Let  -> FStar_Format.text "let "
    | FStar_Extraction_JavaScript_Ast.JSV_Const  ->
        FStar_Format.text "const "
and print_pattern:
  FStar_Extraction_JavaScript_Ast.pattern_t -> Prims.bool -> FStar_Format.doc
  =
  fun p  ->
    fun print_t  ->
      match p with
      | FStar_Extraction_JavaScript_Ast.JGP_Expression e ->
          pretty_print_exp e
      | FStar_Extraction_JavaScript_Ast.JGP_Identifier (id,t) ->
          let r =
            match t with
            | Some v1 ->
                let uu____846 =
                  let uu____848 = let uu____850 = print_typ v1 in [uu____850] in
                  colon :: uu____848 in
                FStar_Format.reduce uu____846
            | None  -> FStar_Format.empty in
          let uu____851 =
            let uu____853 = remove_chars id in
            [uu____853; if print_t then r else FStar_Format.empty] in
          FStar_Format.reduce uu____851
and print_body: FStar_Extraction_JavaScript_Ast.body_t -> FStar_Format.doc =
  fun uu___105_855  ->
    match uu___105_855 with
    | FStar_Extraction_JavaScript_Ast.JS_BodyBlock l ->
        let uu____858 =
          let uu____860 =
            let uu____862 =
              let uu____864 = pretty_print_statements l in
              [uu____864; FStar_Format.text "}"] in
            FStar_Format.hardline :: uu____862 in
          (FStar_Format.text "{") :: uu____860 in
        FStar_Format.reduce uu____858
    | FStar_Extraction_JavaScript_Ast.JS_BodyExpression e ->
        let uu____866 = pretty_print_exp e in FStar_Format.parens uu____866