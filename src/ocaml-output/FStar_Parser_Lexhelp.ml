
open Prims

let intern_string : Prims.string  ->  Prims.string = (

let strings = (FStar_Util.smap_create (Prims.parse_int "100"))
in (fun s -> (

let uu____6 = (FStar_Util.smap_try_find strings s)
in (match (uu____6) with
| Some (res) -> begin
res
end
| None -> begin
((FStar_Util.smap_add strings s s);
s;
)
end))))


let default_string_finish = (fun endm b s -> FStar_Parser_Parse.STRING (s))


let call_string_finish = (fun fin buf endm b -> (let _0_27 = (FStar_Bytes.close buf)
in (fin endm b _0_27)))


let add_string : FStar_Bytes.bytebuf  ->  Prims.string  ->  Prims.unit = (fun buf x -> (

let uu____76 = (FStar_Bytes.string_as_unicode_bytes x)
in (FStar_Bytes.emit_bytes buf uu____76)))


let add_int_char : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> ((FStar_Bytes.emit_int_as_byte buf (c mod (Prims.parse_int "256")));
(FStar_Bytes.emit_int_as_byte buf (c / (Prims.parse_int "256")));
))


let add_unichar : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> (add_int_char buf c))


let add_byte_char : FStar_Bytes.bytebuf  ->  FStar_BaseTypes.char  ->  Prims.unit = (fun buf c -> (add_int_char buf ((FStar_Util.int_of_char c) mod (Prims.parse_int "256"))))


let stringbuf_as_bytes : FStar_Bytes.bytebuf  ->  FStar_Bytes.bytes = (fun buf -> (

let bytes = (FStar_Bytes.close buf)
in (

let uu____100 = (

let uu____101 = (FStar_Bytes.length bytes)
in (uu____101 / (Prims.parse_int "2")))
in (FStar_Bytes.make (fun i -> (FStar_Bytes.get bytes (FStar_Mul.op_Star i (Prims.parse_int "2")))) uu____100))))


let stringbuf_is_bytes : FStar_Bytes.bytebuf  ->  Prims.bool = (fun buf -> (

let bytes = (FStar_Bytes.close buf)
in (

let ok = (FStar_Util.mk_ref true)
in ((

let uu____114 = (

let uu____115 = (

let uu____116 = (FStar_Bytes.length bytes)
in (uu____116 / (Prims.parse_int "2")))
in (uu____115 - (Prims.parse_int "1")))
in (FStar_Util.for_range (Prims.parse_int "0") uu____114 (fun i -> (

let uu____121 = (

let uu____122 = (FStar_Bytes.get bytes ((FStar_Mul.op_Star i (Prims.parse_int "2")) + (Prims.parse_int "1")))
in (uu____122 <> (Prims.parse_int "0")))
in (match (uu____121) with
| true -> begin
(FStar_ST.write ok false)
end
| uu____125 -> begin
()
end)))));
(FStar_ST.read ok);
))))


let trigraph : FStar_BaseTypes.char  ->  FStar_BaseTypes.char  ->  FStar_BaseTypes.char  ->  FStar_BaseTypes.char = (fun c1 c2 c3 -> (

let digit = (fun c -> ((FStar_Util.int_of_char c) - (FStar_Util.int_of_char '0')))
in (FStar_Util.char_of_int (((FStar_Mul.op_Star (digit c1) (Prims.parse_int "100")) + (FStar_Mul.op_Star (digit c2) (Prims.parse_int "10"))) + (digit c3)))))


let digit : FStar_BaseTypes.char  ->  Prims.int = (fun d -> (

let dd = (FStar_Util.int_of_char d)
in (match (((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9')))) with
| true -> begin
((FStar_Util.int_of_char d) - (FStar_Util.int_of_char '0'))
end
| uu____145 -> begin
(failwith "digit")
end)))


let hexdigit : FStar_BaseTypes.char  ->  Prims.int = (fun d -> (

let dd = (FStar_Util.int_of_char d)
in (match (((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9')))) with
| true -> begin
(digit d)
end
| uu____150 -> begin
(match (((dd >= (FStar_Util.int_of_char 'a')) && (dd <= (FStar_Util.int_of_char 'f')))) with
| true -> begin
((dd - (FStar_Util.int_of_char 'a')) + (Prims.parse_int "10"))
end
| uu____151 -> begin
(match (((dd >= (FStar_Util.int_of_char 'A')) && (dd <= (FStar_Util.int_of_char 'F')))) with
| true -> begin
((dd - (FStar_Util.int_of_char 'A')) + (Prims.parse_int "10"))
end
| uu____152 -> begin
(failwith "hexdigit")
end)
end)
end)))


let unicodegraph_short : Prims.string  ->  FStar_BaseTypes.uint16 = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "4"))) with
| true -> begin
(failwith "unicodegraph")
end
| uu____158 -> begin
(

let uu____159 = (

let uu____160 = (

let uu____161 = (

let uu____162 = (

let uu____163 = (

let uu____164 = (FStar_Util.char_at s (Prims.parse_int "0"))
in (hexdigit uu____164))
in (FStar_Mul.op_Star uu____163 (Prims.parse_int "4096")))
in (

let uu____165 = (

let uu____166 = (

let uu____167 = (FStar_Util.char_at s (Prims.parse_int "1"))
in (hexdigit uu____167))
in (FStar_Mul.op_Star uu____166 (Prims.parse_int "256")))
in (uu____162 + uu____165)))
in (

let uu____168 = (

let uu____169 = (

let uu____170 = (FStar_Util.char_at s (Prims.parse_int "2"))
in (hexdigit uu____170))
in (FStar_Mul.op_Star uu____169 (Prims.parse_int "16")))
in (uu____161 + uu____168)))
in (

let uu____171 = (

let uu____172 = (FStar_Util.char_at s (Prims.parse_int "3"))
in (hexdigit uu____172))
in (uu____160 + uu____171)))
in (FStar_Util.uint16_of_int uu____159))
end))


let hexgraph_short : Prims.string  ->  FStar_BaseTypes.uint16 = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "2"))) with
| true -> begin
(failwith "hexgraph")
end
| uu____178 -> begin
(

let uu____179 = (

let uu____180 = (

let uu____181 = (

let uu____182 = (FStar_Util.char_at s (Prims.parse_int "0"))
in (hexdigit uu____182))
in (FStar_Mul.op_Star uu____181 (Prims.parse_int "16")))
in (

let uu____183 = (

let uu____184 = (FStar_Util.char_at s (Prims.parse_int "1"))
in (hexdigit uu____184))
in (uu____180 + uu____183)))
in (FStar_Util.uint16_of_int uu____179))
end))


let unicodegraph_long : Prims.string  ->  (FStar_BaseTypes.uint16 Prims.option * FStar_BaseTypes.uint16) = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "8"))) with
| true -> begin
(failwith "unicodegraph_long")
end
| uu____199 -> begin
(

let high = (

let uu____201 = (

let uu____202 = (

let uu____203 = (

let uu____204 = (

let uu____205 = (FStar_Util.char_at s (Prims.parse_int "0"))
in (hexdigit uu____205))
in (FStar_Mul.op_Star uu____204 (Prims.parse_int "4096")))
in (

let uu____206 = (

let uu____207 = (

let uu____208 = (FStar_Util.char_at s (Prims.parse_int "1"))
in (hexdigit uu____208))
in (FStar_Mul.op_Star uu____207 (Prims.parse_int "256")))
in (uu____203 + uu____206)))
in (

let uu____209 = (

let uu____210 = (

let uu____211 = (FStar_Util.char_at s (Prims.parse_int "2"))
in (hexdigit uu____211))
in (FStar_Mul.op_Star uu____210 (Prims.parse_int "16")))
in (uu____202 + uu____209)))
in (

let uu____212 = (

let uu____213 = (FStar_Util.char_at s (Prims.parse_int "3"))
in (hexdigit uu____213))
in (uu____201 + uu____212)))
in (

let low = (

let uu____215 = (

let uu____216 = (

let uu____217 = (

let uu____218 = (

let uu____219 = (FStar_Util.char_at s (Prims.parse_int "4"))
in (hexdigit uu____219))
in (FStar_Mul.op_Star uu____218 (Prims.parse_int "4096")))
in (

let uu____220 = (

let uu____221 = (

let uu____222 = (FStar_Util.char_at s (Prims.parse_int "5"))
in (hexdigit uu____222))
in (FStar_Mul.op_Star uu____221 (Prims.parse_int "256")))
in (uu____217 + uu____220)))
in (

let uu____223 = (

let uu____224 = (

let uu____225 = (FStar_Util.char_at s (Prims.parse_int "6"))
in (hexdigit uu____225))
in (FStar_Mul.op_Star uu____224 (Prims.parse_int "16")))
in (uu____216 + uu____223)))
in (

let uu____226 = (

let uu____227 = (FStar_Util.char_at s (Prims.parse_int "7"))
in (hexdigit uu____227))
in (uu____215 + uu____226)))
in (match ((high = (Prims.parse_int "0"))) with
| true -> begin
((None), ((FStar_Util.uint16_of_int low)))
end
| uu____232 -> begin
((Some ((FStar_Util.uint16_of_int ((Prims.parse_int "0xD800") + (((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) + (low - (Prims.parse_int "0x10000"))) / (Prims.parse_int "0x400")))))), ((FStar_Util.uint16_of_int ((Prims.parse_int "0xDF30") + (((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) + (low - (Prims.parse_int "0x10000"))) mod (Prims.parse_int "0x400"))))))
end)))
end))


let escape : FStar_Char.char  ->  FStar_Char.char = (fun c -> (match (c) with
| '\\' -> begin
'\\'
end
| '\'' -> begin
'\''
end
| 'n' -> begin
'\n'
end
| 't' -> begin
'\t'
end
| 'b' -> begin
'\b'
end
| 'r' -> begin
'\r'
end
| c -> begin
c
end))

type compatibilityMode =
| ALWAYS
| FSHARP


let uu___is_ALWAYS : compatibilityMode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ALWAYS -> begin
true
end
| uu____241 -> begin
false
end))


let uu___is_FSHARP : compatibilityMode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FSHARP -> begin
true
end
| uu____245 -> begin
false
end))


let keywords : (compatibilityMode * Prims.string * FStar_Parser_Parse.token) Prims.list = (((ALWAYS), ("abstract"), (FStar_Parser_Parse.ABSTRACT)))::(((ALWAYS), ("attributes"), (FStar_Parser_Parse.ATTRIBUTES)))::(((ALWAYS), ("noeq"), (FStar_Parser_Parse.NOEQUALITY)))::(((ALWAYS), ("unopteq"), (FStar_Parser_Parse.UNOPTEQUALITY)))::(((ALWAYS), ("and"), (FStar_Parser_Parse.AND)))::(((ALWAYS), ("assert"), (FStar_Parser_Parse.ASSERT)))::(((ALWAYS), ("assume"), (FStar_Parser_Parse.ASSUME)))::(((ALWAYS), ("begin"), (FStar_Parser_Parse.BEGIN)))::(((FSHARP), ("default"), (FStar_Parser_Parse.DEFAULT)))::(((ALWAYS), ("effect"), (FStar_Parser_Parse.EFFECT)))::(((ALWAYS), ("effect_actions"), (FStar_Parser_Parse.ACTIONS)))::(((ALWAYS), ("else"), (FStar_Parser_Parse.ELSE)))::(((ALWAYS), ("end"), (FStar_Parser_Parse.END)))::(((ALWAYS), ("ensures"), (FStar_Parser_Parse.ENSURES)))::(((ALWAYS), ("exception"), (FStar_Parser_Parse.EXCEPTION)))::(((ALWAYS), ("exists"), (FStar_Parser_Parse.EXISTS)))::(((ALWAYS), ("false"), (FStar_Parser_Parse.FALSE)))::(((ALWAYS), ("False"), (FStar_Parser_Parse.L_FALSE)))::(((ALWAYS), ("forall"), (FStar_Parser_Parse.FORALL)))::(((ALWAYS), ("fun"), (FStar_Parser_Parse.FUN)))::(((ALWAYS), ("function"), (FStar_Parser_Parse.FUNCTION)))::(((ALWAYS), ("if"), (FStar_Parser_Parse.IF)))::(((ALWAYS), ("in"), (FStar_Parser_Parse.IN)))::(((ALWAYS), ("include"), (FStar_Parser_Parse.INCLUDE)))::(((ALWAYS), ("inline"), (FStar_Parser_Parse.INLINE)))::(((ALWAYS), ("inline_for_extraction"), (FStar_Parser_Parse.INLINE_FOR_EXTRACTION)))::(((ALWAYS), ("irreducible"), (FStar_Parser_Parse.IRREDUCIBLE)))::(((ALWAYS), ("let"), (FStar_Parser_Parse.LET (false))))::(((ALWAYS), ("logic"), (FStar_Parser_Parse.LOGIC)))::(((ALWAYS), ("match"), (FStar_Parser_Parse.MATCH)))::(((ALWAYS), ("module"), (FStar_Parser_Parse.MODULE)))::(((ALWAYS), ("mutable"), (FStar_Parser_Parse.MUTABLE)))::(((ALWAYS), ("new"), (FStar_Parser_Parse.NEW)))::(((ALWAYS), ("new_effect"), (FStar_Parser_Parse.NEW_EFFECT)))::(((ALWAYS), ("new_effect_for_free"), (FStar_Parser_Parse.NEW_EFFECT_FOR_FREE)))::(((ALWAYS), ("noextract"), (FStar_Parser_Parse.NOEXTRACT)))::(((ALWAYS), ("of"), (FStar_Parser_Parse.OF)))::(((ALWAYS), ("open"), (FStar_Parser_Parse.OPEN)))::(((ALWAYS), ("opaque"), (FStar_Parser_Parse.OPAQUE)))::(((ALWAYS), ("private"), (FStar_Parser_Parse.PRIVATE)))::(((ALWAYS), ("rec"), (FStar_Parser_Parse.REC)))::(((ALWAYS), ("reifiable"), (FStar_Parser_Parse.REIFIABLE)))::(((ALWAYS), ("reify"), (FStar_Parser_Parse.REIFY)))::(((ALWAYS), ("reflectable"), (FStar_Parser_Parse.REFLECTABLE)))::(((ALWAYS), ("requires"), (FStar_Parser_Parse.REQUIRES)))::(((ALWAYS), ("sub_effect"), (FStar_Parser_Parse.SUB_EFFECT)))::(((ALWAYS), ("then"), (FStar_Parser_Parse.THEN)))::(((ALWAYS), ("total"), (FStar_Parser_Parse.TOTAL)))::(((ALWAYS), ("true"), (FStar_Parser_Parse.TRUE)))::(((ALWAYS), ("True"), (FStar_Parser_Parse.L_TRUE)))::(((ALWAYS), ("try"), (FStar_Parser_Parse.TRY)))::(((ALWAYS), ("type"), (FStar_Parser_Parse.TYPE)))::(((ALWAYS), ("unfold"), (FStar_Parser_Parse.UNFOLD)))::(((ALWAYS), ("unfoldable"), (FStar_Parser_Parse.UNFOLDABLE)))::(((ALWAYS), ("val"), (FStar_Parser_Parse.VAL)))::(((ALWAYS), ("when"), (FStar_Parser_Parse.WHEN)))::(((ALWAYS), ("with"), (FStar_Parser_Parse.WITH)))::(((ALWAYS), ("_"), (FStar_Parser_Parse.UNDERSCORE)))::[]


let stringKeywords : Prims.string Prims.list = (FStar_List.map (fun uu____431 -> (match (uu____431) with
| (uu____435, w, uu____437) -> begin
w
end)) keywords)


let unreserve_words : Prims.string Prims.list = (FStar_List.choose (fun uu____442 -> (match (uu____442) with
| (mode, keyword, uu____449) -> begin
(match ((mode = FSHARP)) with
| true -> begin
Some (keyword)
end
| uu____451 -> begin
None
end)
end)) keywords)


let kwd_table : FStar_Parser_Parse.token FStar_Util.smap = (

let tab = (FStar_Util.smap_create (Prims.parse_int "1000"))
in ((FStar_List.iter (fun uu____459 -> (match (uu____459) with
| (mode, keyword, token) -> begin
(FStar_Util.smap_add tab keyword token)
end)) keywords);
tab;
))


let kwd : Prims.string  ->  FStar_Parser_Parse.token Prims.option = (fun s -> (FStar_Util.smap_try_find kwd_table s))

type lexargs =
{getSourceDirectory : Prims.unit  ->  Prims.string; filename : Prims.string; contents : Prims.string}


let mkLexargs : ((Prims.unit  ->  Prims.string) * Prims.string * Prims.string)  ->  lexargs = (fun uu____506 -> (match (uu____506) with
| (srcdir, filename, contents) -> begin
{getSourceDirectory = srcdir; filename = filename; contents = contents}
end))


let kwd_or_id : lexargs  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Parser_Parse.token = (fun args r s -> (

let uu____528 = (kwd s)
in (match (uu____528) with
| Some (v) -> begin
v
end
| None -> begin
(match (s) with
| "__SOURCE_DIRECTORY__" -> begin
(

let uu____531 = (

let uu____532 = (args.getSourceDirectory ())
in (FStar_Bytes.string_as_unicode_bytes uu____532))
in FStar_Parser_Parse.STRING (uu____531))
end
| "__SOURCE_FILE__" -> begin
(

let uu____533 = (

let uu____534 = (FStar_Range.file_of_range r)
in (FStar_Bytes.string_as_unicode_bytes uu____534))
in FStar_Parser_Parse.STRING (uu____533))
end
| "__LINE__" -> begin
(

let uu____535 = (

let uu____538 = (

let uu____539 = (

let uu____540 = (FStar_Range.start_of_range r)
in (FStar_Range.line_of_pos uu____540))
in (FStar_All.pipe_left FStar_Util.string_of_int uu____539))
in ((uu____538), (false)))
in FStar_Parser_Parse.INT (uu____535))
end
| uu____541 -> begin
(match ((FStar_Util.starts_with s FStar_Ident.reserved_prefix)) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat FStar_Ident.reserved_prefix " is a reserved prefix for an identifier")), (r)))))
end
| uu____542 -> begin
(

let uu____543 = (intern_string s)
in FStar_Parser_Parse.IDENT (uu____543))
end)
end)
end)))




