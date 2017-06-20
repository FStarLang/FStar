open Prims
let intern_string : Prims.string -> Prims.string =
  let strings = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun s  ->
    let uu____7 = FStar_Util.smap_try_find strings s  in
    match uu____7 with
    | Some res -> res
    | None  -> (FStar_Util.smap_add strings s s; s)
  
let default_string_finish endm b s = FStar_Parser_Parse.STRING s 
let call_string_finish fin buf endm b =
  let _0_26 = FStar_Bytes.close buf  in fin endm b _0_26 
let add_string : FStar_Bytes.bytebuf -> Prims.string -> Prims.unit =
  fun buf  ->
    fun x  ->
      let uu____91 = FStar_Bytes.string_as_unicode_bytes x  in
      FStar_Bytes.emit_bytes buf uu____91
  
let add_int_char : FStar_Bytes.bytebuf -> Prims.int -> Prims.unit =
  fun buf  ->
    fun c  ->
      FStar_Bytes.emit_int_as_byte buf (c mod (Prims.parse_int "256"));
      FStar_Bytes.emit_int_as_byte buf (c / (Prims.parse_int "256"))
  
let add_unichar : FStar_Bytes.bytebuf -> Prims.int -> Prims.unit =
  fun buf  -> fun c  -> add_int_char buf c 
let add_byte_char : FStar_Bytes.bytebuf -> FStar_BaseTypes.char -> Prims.unit
  =
  fun buf  ->
    fun c  ->
      add_int_char buf
        ((FStar_Util.int_of_char c) mod (Prims.parse_int "256"))
  
let stringbuf_as_bytes : FStar_Bytes.bytebuf -> FStar_Bytes.bytes =
  fun buf  ->
    let bytes = FStar_Bytes.close buf  in
    let uu____122 =
      let uu____123 = FStar_Bytes.length bytes  in
      uu____123 / (Prims.parse_int "2")  in
    FStar_Bytes.make
      (fun i  ->
         FStar_Bytes.get bytes (FStar_Mul.op_Star i (Prims.parse_int "2")))
      uu____122
  
let stringbuf_is_bytes : FStar_Bytes.bytebuf -> Prims.bool =
  fun buf  ->
    let bytes = FStar_Bytes.close buf  in
    let ok = FStar_Util.mk_ref true  in
    (let uu____140 =
       let uu____141 =
         let uu____142 = FStar_Bytes.length bytes  in
         uu____142 / (Prims.parse_int "2")  in
       uu____141 - (Prims.parse_int "1")  in
     FStar_Util.for_range (Prims.parse_int "0") uu____140
       (fun i  ->
          let uu____150 =
            let uu____151 =
              FStar_Bytes.get bytes
                ((FStar_Mul.op_Star i (Prims.parse_int "2")) +
                   (Prims.parse_int "1"))
               in
            uu____151 <> (Prims.parse_int "0")  in
          if uu____150 then FStar_ST.write ok false else ()));
    FStar_ST.read ok
  
let trigraph :
  FStar_BaseTypes.char ->
    FStar_BaseTypes.char -> FStar_BaseTypes.char -> FStar_BaseTypes.char
  =
  fun c1  ->
    fun c2  ->
      fun c3  ->
        let digit c =
          (FStar_Util.int_of_char c) - (FStar_Util.int_of_char '0')  in
        FStar_Util.char_of_int
          (((FStar_Mul.op_Star (digit c1) (Prims.parse_int "100")) +
              (FStar_Mul.op_Star (digit c2) (Prims.parse_int "10")))
             + (digit c3))
  
let digit : FStar_BaseTypes.char -> Prims.int =
  fun d  ->
    let dd = FStar_Util.int_of_char d  in
    if
      (dd >= (FStar_Util.int_of_char '0')) &&
        (dd <= (FStar_Util.int_of_char '9'))
    then (FStar_Util.int_of_char d) - (FStar_Util.int_of_char '0')
    else failwith "digit"
  
let hexdigit : FStar_BaseTypes.char -> Prims.int =
  fun d  ->
    let dd = FStar_Util.int_of_char d  in
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
  
let unicodegraph_short : Prims.string -> FStar_BaseTypes.uint16 =
  fun s  ->
    if (FStar_String.length s) <> (Prims.parse_int "4")
    then failwith "unicodegraph"
    else
      (let uu____196 =
         let uu____197 =
           let uu____198 =
             let uu____199 =
               let uu____200 =
                 let uu____201 = FStar_Util.char_at s (Prims.parse_int "0")
                    in
                 hexdigit uu____201  in
               FStar_Mul.op_Star uu____200 (Prims.parse_int "4096")  in
             let uu____202 =
               let uu____203 =
                 let uu____204 = FStar_Util.char_at s (Prims.parse_int "1")
                    in
                 hexdigit uu____204  in
               FStar_Mul.op_Star uu____203 (Prims.parse_int "256")  in
             uu____199 + uu____202  in
           let uu____205 =
             let uu____206 =
               let uu____207 = FStar_Util.char_at s (Prims.parse_int "2")  in
               hexdigit uu____207  in
             FStar_Mul.op_Star uu____206 (Prims.parse_int "16")  in
           uu____198 + uu____205  in
         let uu____208 =
           let uu____209 = FStar_Util.char_at s (Prims.parse_int "3")  in
           hexdigit uu____209  in
         uu____197 + uu____208  in
       FStar_Util.uint16_of_int uu____196)
  
let hexgraph_short : Prims.string -> FStar_BaseTypes.uint16 =
  fun s  ->
    if (FStar_String.length s) <> (Prims.parse_int "2")
    then failwith "hexgraph"
    else
      (let uu____219 =
         let uu____220 =
           let uu____221 =
             let uu____222 = FStar_Util.char_at s (Prims.parse_int "0")  in
             hexdigit uu____222  in
           FStar_Mul.op_Star uu____221 (Prims.parse_int "16")  in
         let uu____223 =
           let uu____224 = FStar_Util.char_at s (Prims.parse_int "1")  in
           hexdigit uu____224  in
         uu____220 + uu____223  in
       FStar_Util.uint16_of_int uu____219)
  
let unicodegraph_long :
  Prims.string -> (FStar_BaseTypes.uint16 option * FStar_BaseTypes.uint16) =
  fun s  ->
    if (FStar_String.length s) <> (Prims.parse_int "8")
    then failwith "unicodegraph_long"
    else
      (let high =
         let uu____244 =
           let uu____245 =
             let uu____246 =
               let uu____247 =
                 let uu____248 = FStar_Util.char_at s (Prims.parse_int "0")
                    in
                 hexdigit uu____248  in
               FStar_Mul.op_Star uu____247 (Prims.parse_int "4096")  in
             let uu____249 =
               let uu____250 =
                 let uu____251 = FStar_Util.char_at s (Prims.parse_int "1")
                    in
                 hexdigit uu____251  in
               FStar_Mul.op_Star uu____250 (Prims.parse_int "256")  in
             uu____246 + uu____249  in
           let uu____252 =
             let uu____253 =
               let uu____254 = FStar_Util.char_at s (Prims.parse_int "2")  in
               hexdigit uu____254  in
             FStar_Mul.op_Star uu____253 (Prims.parse_int "16")  in
           uu____245 + uu____252  in
         let uu____255 =
           let uu____256 = FStar_Util.char_at s (Prims.parse_int "3")  in
           hexdigit uu____256  in
         uu____244 + uu____255  in
       let low =
         let uu____258 =
           let uu____259 =
             let uu____260 =
               let uu____261 =
                 let uu____262 = FStar_Util.char_at s (Prims.parse_int "4")
                    in
                 hexdigit uu____262  in
               FStar_Mul.op_Star uu____261 (Prims.parse_int "4096")  in
             let uu____263 =
               let uu____264 =
                 let uu____265 = FStar_Util.char_at s (Prims.parse_int "5")
                    in
                 hexdigit uu____265  in
               FStar_Mul.op_Star uu____264 (Prims.parse_int "256")  in
             uu____260 + uu____263  in
           let uu____266 =
             let uu____267 =
               let uu____268 = FStar_Util.char_at s (Prims.parse_int "6")  in
               hexdigit uu____268  in
             FStar_Mul.op_Star uu____267 (Prims.parse_int "16")  in
           uu____259 + uu____266  in
         let uu____269 =
           let uu____270 = FStar_Util.char_at s (Prims.parse_int "7")  in
           hexdigit uu____270  in
         uu____258 + uu____269  in
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
  
let escape : FStar_Char.char -> FStar_Char.char =
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
let uu___is_ALWAYS : compatibilityMode -> Prims.bool =
  fun projectee  ->
    match projectee with | ALWAYS  -> true | uu____286 -> false
  
let uu___is_FSHARP : compatibilityMode -> Prims.bool =
  fun projectee  ->
    match projectee with | FSHARP  -> true | uu____291 -> false
  
let keywords :
  (compatibilityMode * Prims.string * FStar_Parser_Parse.token) Prims.list =
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
let stringKeywords : Prims.string Prims.list =
  FStar_List.map
    (fun uu____474  -> match uu____474 with | (uu____478,w,uu____480) -> w)
    keywords
  
let unreserve_words : Prims.string Prims.list =
  FStar_List.choose
    (fun uu____485  ->
       match uu____485 with
       | (mode,keyword,uu____492) ->
           if mode = FSHARP then Some keyword else None) keywords
  
let kwd_table : FStar_Parser_Parse.token FStar_Util.smap =
  let tab = FStar_Util.smap_create (Prims.parse_int "1000")  in
  FStar_List.iter
    (fun uu____502  ->
       match uu____502 with
       | (mode,keyword,token) -> FStar_Util.smap_add tab keyword token)
    keywords;
  tab 
let kwd : Prims.string -> FStar_Parser_Parse.token option =
  fun s  -> FStar_Util.smap_try_find kwd_table s 
type lexargs =
  {
  getSourceDirectory: Prims.unit -> Prims.string ;
  filename: Prims.string ;
  contents: Prims.string }
let __proj__Mklexargs__item__getSourceDirectory :
  lexargs -> Prims.unit -> Prims.string =
  fun projectee  ->
    match projectee with
    | { getSourceDirectory = __fname__getSourceDirectory;
        filename = __fname__filename; contents = __fname__contents;_} ->
        __fname__getSourceDirectory
  
let __proj__Mklexargs__item__filename : lexargs -> Prims.string =
  fun projectee  ->
    match projectee with
    | { getSourceDirectory = __fname__getSourceDirectory;
        filename = __fname__filename; contents = __fname__contents;_} ->
        __fname__filename
  
let __proj__Mklexargs__item__contents : lexargs -> Prims.string =
  fun projectee  ->
    match projectee with
    | { getSourceDirectory = __fname__getSourceDirectory;
        filename = __fname__filename; contents = __fname__contents;_} ->
        __fname__contents
  
let mkLexargs :
  ((Prims.unit -> Prims.string) * Prims.string * Prims.string) -> lexargs =
  fun uu____571  ->
    match uu____571 with
    | (srcdir,filename,contents) ->
        { getSourceDirectory = srcdir; filename; contents }
  
let kwd_or_id :
  lexargs -> FStar_Range.range -> Prims.string -> FStar_Parser_Parse.token =
  fun args  ->
    fun r  ->
      fun s  ->
        let uu____596 = kwd s  in
        match uu____596 with
        | Some v1 -> v1
        | None  ->
            (match s with
             | "__SOURCE_DIRECTORY__" ->
                 let uu____599 =
                   let uu____600 = args.getSourceDirectory ()  in
                   FStar_Bytes.string_as_unicode_bytes uu____600  in
                 FStar_Parser_Parse.STRING uu____599
             | "__SOURCE_FILE__" ->
                 let uu____601 =
                   let uu____602 = FStar_Range.file_of_range r  in
                   FStar_Bytes.string_as_unicode_bytes uu____602  in
                 FStar_Parser_Parse.STRING uu____601
             | "__LINE__" ->
                 let uu____603 =
                   let uu____606 =
                     let uu____607 =
                       let uu____608 = FStar_Range.start_of_range r  in
                       FStar_Range.line_of_pos uu____608  in
                     FStar_All.pipe_left FStar_Util.string_of_int uu____607
                      in
                   (uu____606, false)  in
                 FStar_Parser_Parse.INT uu____603
             | uu____609 ->
                 if FStar_Util.starts_with s FStar_Ident.reserved_prefix
                 then
                   raise
                     (FStar_Errors.Error
                        ((Prims.strcat FStar_Ident.reserved_prefix
                            " is a reserved prefix for an identifier"), r))
                 else
                   (let uu____611 = intern_string s  in
                    FStar_Parser_Parse.IDENT uu____611))
  