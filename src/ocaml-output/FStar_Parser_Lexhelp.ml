open Prims
let intern_string: Prims.string -> Prims.string =
  let strings = FStar_Util.smap_create (Prims.parse_int "100") in
  fun s  ->
    let uu____6 = FStar_Util.smap_try_find strings s in
    match uu____6 with
    | Some res -> res
    | None  -> (FStar_Util.smap_add strings s s; s)
let default_string_finish endm b s = FStar_Parser_Parse.STRING s
let call_string_finish fin buf endm b =
  let _0_26 = FStar_Bytes.close buf in fin endm b _0_26
let add_string: FStar_Bytes.bytebuf -> Prims.string -> Prims.unit =
  fun buf  ->
    fun x  ->
      let uu____76 = FStar_Bytes.string_as_unicode_bytes x in
      FStar_Bytes.emit_bytes buf uu____76
let add_int_char: FStar_Bytes.bytebuf -> Prims.int -> Prims.unit =
  fun buf  ->
    fun c  ->
      FStar_Bytes.emit_int_as_byte buf (c mod (Prims.parse_int "256"));
      FStar_Bytes.emit_int_as_byte buf (c / (Prims.parse_int "256"))
let add_unichar: FStar_Bytes.bytebuf -> Prims.int -> Prims.unit =
  fun buf  -> fun c  -> add_int_char buf c
let add_byte_char: FStar_Bytes.bytebuf -> FStar_BaseTypes.char -> Prims.unit
  =
  fun buf  ->
    fun c  ->
      add_int_char buf
        ((FStar_Util.int_of_char c) mod (Prims.parse_int "256"))
let stringbuf_as_bytes: FStar_Bytes.bytebuf -> FStar_Bytes.bytes =
  fun buf  ->
    let bytes = FStar_Bytes.close buf in
    let uu____100 =
      let uu____101 = FStar_Bytes.length bytes in
      uu____101 / (Prims.parse_int "2") in
    FStar_Bytes.make
      (fun i  ->
         FStar_Bytes.get bytes (FStar_Mul.op_Star i (Prims.parse_int "2")))
      uu____100
let stringbuf_is_bytes: FStar_Bytes.bytebuf -> Prims.bool =
  fun buf  ->
    let bytes = FStar_Bytes.close buf in
    let ok = FStar_Util.mk_ref true in
    (let uu____116 =
       let uu____117 =
         let uu____118 = FStar_Bytes.length bytes in
         uu____118 / (Prims.parse_int "2") in
       uu____117 - (Prims.parse_int "1") in
     FStar_Util.for_range (Prims.parse_int "0") uu____116
       (fun i  ->
          let uu____125 =
            let uu____126 =
              FStar_Bytes.get bytes
                ((FStar_Mul.op_Star i (Prims.parse_int "2")) +
                   (Prims.parse_int "1")) in
            uu____126 <> (Prims.parse_int "0") in
          if uu____125 then FStar_ST.write ok false else ()));
    FStar_ST.read ok
let trigraph:
  FStar_BaseTypes.char ->
    FStar_BaseTypes.char -> FStar_BaseTypes.char -> FStar_BaseTypes.char
  =
  fun c1  ->
    fun c2  ->
      fun c3  ->
        let digit c =
          (FStar_Util.int_of_char c) - (FStar_Util.int_of_char '0') in
        FStar_Util.char_of_int
          (((FStar_Mul.op_Star (digit c1) (Prims.parse_int "100")) +
              (FStar_Mul.op_Star (digit c2) (Prims.parse_int "10")))
             + (digit c3))
let digit: FStar_BaseTypes.char -> Prims.int =
  fun d  ->
    let dd = FStar_Util.int_of_char d in
    if
      (dd >= (FStar_Util.int_of_char '0')) &&
        (dd <= (FStar_Util.int_of_char '9'))
    then (FStar_Util.int_of_char d) - (FStar_Util.int_of_char '0')
    else failwith "digit"
let hexdigit: FStar_BaseTypes.char -> Prims.int =
  fun d  ->
    let dd = FStar_Util.int_of_char d in
    if
      (dd >= (FStar_Util.int_of_char '0')) &&
        (dd <= (FStar_Util.int_of_char '9'))
    then digit d
    else
      if
        (dd >= (FStar_Util.int_of_char 'a')) &&
          (dd <= (FStar_Util.int_of_char 'f'))
      then (dd - (FStar_Util.int_of_char 'a')) + (Prims.parse_int "10")
      else
        if
          (dd >= (FStar_Util.int_of_char 'A')) &&
            (dd <= (FStar_Util.int_of_char 'F'))
        then (dd - (FStar_Util.int_of_char 'A')) + (Prims.parse_int "10")
        else failwith "hexdigit"
let unicodegraph_short: Prims.string -> FStar_BaseTypes.uint16 =
  fun s  ->
    if (FStar_String.length s) <> (Prims.parse_int "4")
    then failwith "unicodegraph"
    else
      (let uu____163 =
         let uu____164 =
           let uu____165 =
             let uu____166 =
               let uu____167 =
                 let uu____168 = FStar_Util.char_at s (Prims.parse_int "0") in
                 hexdigit uu____168 in
               FStar_Mul.op_Star uu____167 (Prims.parse_int "4096") in
             let uu____169 =
               let uu____170 =
                 let uu____171 = FStar_Util.char_at s (Prims.parse_int "1") in
                 hexdigit uu____171 in
               FStar_Mul.op_Star uu____170 (Prims.parse_int "256") in
             uu____166 + uu____169 in
           let uu____172 =
             let uu____173 =
               let uu____174 = FStar_Util.char_at s (Prims.parse_int "2") in
               hexdigit uu____174 in
             FStar_Mul.op_Star uu____173 (Prims.parse_int "16") in
           uu____165 + uu____172 in
         let uu____175 =
           let uu____176 = FStar_Util.char_at s (Prims.parse_int "3") in
           hexdigit uu____176 in
         uu____164 + uu____175 in
       FStar_Util.uint16_of_int uu____163)
let hexgraph_short: Prims.string -> FStar_BaseTypes.uint16 =
  fun s  ->
    if (FStar_String.length s) <> (Prims.parse_int "2")
    then failwith "hexgraph"
    else
      (let uu____183 =
         let uu____184 =
           let uu____185 =
             let uu____186 = FStar_Util.char_at s (Prims.parse_int "0") in
             hexdigit uu____186 in
           FStar_Mul.op_Star uu____185 (Prims.parse_int "16") in
         let uu____187 =
           let uu____188 = FStar_Util.char_at s (Prims.parse_int "1") in
           hexdigit uu____188 in
         uu____184 + uu____187 in
       FStar_Util.uint16_of_int uu____183)
let unicodegraph_long:
  Prims.string -> (FStar_BaseTypes.uint16 option* FStar_BaseTypes.uint16) =
  fun s  ->
    if (FStar_String.length s) <> (Prims.parse_int "8")
    then failwith "unicodegraph_long"
    else
      (let high =
         let uu____205 =
           let uu____206 =
             let uu____207 =
               let uu____208 =
                 let uu____209 = FStar_Util.char_at s (Prims.parse_int "0") in
                 hexdigit uu____209 in
               FStar_Mul.op_Star uu____208 (Prims.parse_int "4096") in
             let uu____210 =
               let uu____211 =
                 let uu____212 = FStar_Util.char_at s (Prims.parse_int "1") in
                 hexdigit uu____212 in
               FStar_Mul.op_Star uu____211 (Prims.parse_int "256") in
             uu____207 + uu____210 in
           let uu____213 =
             let uu____214 =
               let uu____215 = FStar_Util.char_at s (Prims.parse_int "2") in
               hexdigit uu____215 in
             FStar_Mul.op_Star uu____214 (Prims.parse_int "16") in
           uu____206 + uu____213 in
         let uu____216 =
           let uu____217 = FStar_Util.char_at s (Prims.parse_int "3") in
           hexdigit uu____217 in
         uu____205 + uu____216 in
       let low =
         let uu____219 =
           let uu____220 =
             let uu____221 =
               let uu____222 =
                 let uu____223 = FStar_Util.char_at s (Prims.parse_int "4") in
                 hexdigit uu____223 in
               FStar_Mul.op_Star uu____222 (Prims.parse_int "4096") in
             let uu____224 =
               let uu____225 =
                 let uu____226 = FStar_Util.char_at s (Prims.parse_int "5") in
                 hexdigit uu____226 in
               FStar_Mul.op_Star uu____225 (Prims.parse_int "256") in
             uu____221 + uu____224 in
           let uu____227 =
             let uu____228 =
               let uu____229 = FStar_Util.char_at s (Prims.parse_int "6") in
               hexdigit uu____229 in
             FStar_Mul.op_Star uu____228 (Prims.parse_int "16") in
           uu____220 + uu____227 in
         let uu____230 =
           let uu____231 = FStar_Util.char_at s (Prims.parse_int "7") in
           hexdigit uu____231 in
         uu____219 + uu____230 in
       if high = (Prims.parse_int "0")
       then (None, (FStar_Util.uint16_of_int low))
       else
         ((Some
             (FStar_Util.uint16_of_int
                ((Prims.parse_int "0xD800") +
                   ((((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) +
                        low)
                       - (Prims.parse_int "0x10000"))
                      / (Prims.parse_int "0x400"))))),
           (FStar_Util.uint16_of_int
              ((Prims.parse_int "0xDF30") +
                 ((((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) +
                      low)
                     - (Prims.parse_int "0x10000"))
                    mod (Prims.parse_int "0x400"))))))
let escape: FStar_Char.char -> FStar_Char.char =
  fun c  ->
    match c with
    | '\\' -> '\\'
    | '\'' -> '\''
    | 'n' -> '\n'
    | 't' -> '\t'
    | 'b' -> '\b'
    | 'r' -> '\r'
    | c1 -> c1
type compatibilityMode =
  | ALWAYS
  | FSHARP
let uu___is_ALWAYS: compatibilityMode -> Prims.bool =
  fun projectee  ->
    match projectee with | ALWAYS  -> true | uu____245 -> false
let uu___is_FSHARP: compatibilityMode -> Prims.bool =
  fun projectee  ->
    match projectee with | FSHARP  -> true | uu____249 -> false
let keywords:
  (compatibilityMode* Prims.string* FStar_Parser_Parse.token) Prims.list =
  [(ALWAYS, "abstract", FStar_Parser_Parse.ABSTRACT);
  (ALWAYS, "attributes", FStar_Parser_Parse.ATTRIBUTES);
  (ALWAYS, "noeq", FStar_Parser_Parse.NOEQUALITY);
  (ALWAYS, "unopteq", FStar_Parser_Parse.UNOPTEQUALITY);
  (ALWAYS, "and", FStar_Parser_Parse.AND);
  (ALWAYS, "assert", FStar_Parser_Parse.ASSERT);
  (ALWAYS, "assume", FStar_Parser_Parse.ASSUME);
  (ALWAYS, "begin", FStar_Parser_Parse.BEGIN);
  (ALWAYS, "by", FStar_Parser_Parse.BY);
  (FSHARP, "default", FStar_Parser_Parse.DEFAULT);
  (ALWAYS, "effect", FStar_Parser_Parse.EFFECT);
  (ALWAYS, "else", FStar_Parser_Parse.ELSE);
  (ALWAYS, "end", FStar_Parser_Parse.END);
  (ALWAYS, "ensures", FStar_Parser_Parse.ENSURES);
  (ALWAYS, "exception", FStar_Parser_Parse.EXCEPTION);
  (ALWAYS, "exists", FStar_Parser_Parse.EXISTS);
  (ALWAYS, "false", FStar_Parser_Parse.FALSE);
  (ALWAYS, "False", FStar_Parser_Parse.L_FALSE);
  (ALWAYS, "forall", FStar_Parser_Parse.FORALL);
  (ALWAYS, "fun", FStar_Parser_Parse.FUN);
  (ALWAYS, "function", FStar_Parser_Parse.FUNCTION);
  (ALWAYS, "if", FStar_Parser_Parse.IF);
  (ALWAYS, "in", FStar_Parser_Parse.IN);
  (ALWAYS, "include", FStar_Parser_Parse.INCLUDE);
  (ALWAYS, "inline", FStar_Parser_Parse.INLINE);
  (ALWAYS, "inline_for_extraction", FStar_Parser_Parse.INLINE_FOR_EXTRACTION);
  (ALWAYS, "irreducible", FStar_Parser_Parse.IRREDUCIBLE);
  (ALWAYS, "let", (FStar_Parser_Parse.LET false));
  (ALWAYS, "logic", FStar_Parser_Parse.LOGIC);
  (ALWAYS, "match", FStar_Parser_Parse.MATCH);
  (ALWAYS, "module", FStar_Parser_Parse.MODULE);
  (ALWAYS, "mutable", FStar_Parser_Parse.MUTABLE);
  (ALWAYS, "new", FStar_Parser_Parse.NEW);
  (ALWAYS, "new_effect", FStar_Parser_Parse.NEW_EFFECT);
  (ALWAYS, "noextract", FStar_Parser_Parse.NOEXTRACT);
  (ALWAYS, "of", FStar_Parser_Parse.OF);
  (ALWAYS, "open", FStar_Parser_Parse.OPEN);
  (ALWAYS, "opaque", FStar_Parser_Parse.OPAQUE);
  (ALWAYS, "private", FStar_Parser_Parse.PRIVATE);
  (ALWAYS, "rec", FStar_Parser_Parse.REC);
  (ALWAYS, "reifiable", FStar_Parser_Parse.REIFIABLE);
  (ALWAYS, "reify", FStar_Parser_Parse.REIFY);
  (ALWAYS, "reflectable", FStar_Parser_Parse.REFLECTABLE);
  (ALWAYS, "requires", FStar_Parser_Parse.REQUIRES);
  (ALWAYS, "sub_effect", FStar_Parser_Parse.SUB_EFFECT);
  (ALWAYS, "then", FStar_Parser_Parse.THEN);
  (ALWAYS, "total", FStar_Parser_Parse.TOTAL);
  (ALWAYS, "true", FStar_Parser_Parse.TRUE);
  (ALWAYS, "True", FStar_Parser_Parse.L_TRUE);
  (ALWAYS, "try", FStar_Parser_Parse.TRY);
  (ALWAYS, "type", FStar_Parser_Parse.TYPE);
  (ALWAYS, "unfold", FStar_Parser_Parse.UNFOLD);
  (ALWAYS, "unfoldable", FStar_Parser_Parse.UNFOLDABLE);
  (ALWAYS, "val", FStar_Parser_Parse.VAL);
  (ALWAYS, "when", FStar_Parser_Parse.WHEN);
  (ALWAYS, "with", FStar_Parser_Parse.WITH);
  (ALWAYS, "_", FStar_Parser_Parse.UNDERSCORE)]
let stringKeywords: Prims.string Prims.list =
  FStar_List.map
    (fun uu____436  -> match uu____436 with | (uu____440,w,uu____442) -> w)
    keywords
let unreserve_words: Prims.string Prims.list =
  FStar_List.choose
    (fun uu____451  ->
       match uu____451 with
       | (mode,keyword,uu____458) ->
           if mode = FSHARP then Some keyword else None) keywords
let kwd_table: FStar_Parser_Parse.token FStar_Util.smap =
  let tab = FStar_Util.smap_create (Prims.parse_int "1000") in
  FStar_List.iter
    (fun uu____472  ->
       match uu____472 with
       | (mode,keyword,token) -> FStar_Util.smap_add tab keyword token)
    keywords;
  tab
let kwd: Prims.string -> FStar_Parser_Parse.token option =
  fun s  -> FStar_Util.smap_try_find kwd_table s
type lexargs =
  {
  getSourceDirectory: Prims.unit -> Prims.string;
  filename: Prims.string;
  contents: Prims.string;}
let mkLexargs:
  ((Prims.unit -> Prims.string)* Prims.string* Prims.string) -> lexargs =
  fun uu____523  ->
    match uu____523 with
    | (srcdir,filename,contents) ->
        { getSourceDirectory = srcdir; filename; contents }
let kwd_or_id:
  lexargs -> FStar_Range.range -> Prims.string -> FStar_Parser_Parse.token =
  fun args  ->
    fun r  ->
      fun s  ->
        let uu____545 = kwd s in
        match uu____545 with
        | Some v1 -> v1
        | None  ->
            (match s with
             | "__SOURCE_DIRECTORY__" ->
                 let uu____548 =
                   let uu____549 = args.getSourceDirectory () in
                   FStar_Bytes.string_as_unicode_bytes uu____549 in
                 FStar_Parser_Parse.STRING uu____548
             | "__SOURCE_FILE__" ->
                 let uu____550 =
                   let uu____551 = FStar_Range.file_of_range r in
                   FStar_Bytes.string_as_unicode_bytes uu____551 in
                 FStar_Parser_Parse.STRING uu____550
             | "__LINE__" ->
                 let uu____552 =
                   let uu____555 =
                     let uu____556 =
                       let uu____557 = FStar_Range.start_of_range r in
                       FStar_Range.line_of_pos uu____557 in
                     FStar_All.pipe_left FStar_Util.string_of_int uu____556 in
                   (uu____555, false) in
                 FStar_Parser_Parse.INT uu____552
             | uu____558 ->
                 if FStar_Util.starts_with s FStar_Ident.reserved_prefix
                 then
                   raise
                     (FStar_Errors.Error
                        ((Prims.strcat FStar_Ident.reserved_prefix
                            " is a reserved prefix for an identifier"), r))
                 else
                   (let uu____560 = intern_string s in
                    FStar_Parser_Parse.IDENT uu____560))