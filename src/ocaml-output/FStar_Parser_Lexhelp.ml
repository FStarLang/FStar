
open Prims
open FStar_Pervasives

let intern_string : Prims.string  ->  Prims.string = (

let strings = (FStar_Util.smap_create (Prims.parse_int "100"))
in (fun s -> (

let uu____6 = (FStar_Util.smap_try_find strings s)
in (match (uu____6) with
| FStar_Pervasives_Native.Some (res) -> begin
res
end
| FStar_Pervasives_Native.None -> begin
((FStar_Util.smap_add strings s s);
s;
)
end))))


let default_string_finish = (fun endm b s -> (

let uu____29 = (FStar_Bytes.unicode_bytes_as_string s)
in FStar_Parser_Parse.STRING (uu____29)))


let call_string_finish = (fun fin buf endm b -> (let _0_26 = (FStar_Bytes.close buf)
in (fin endm b _0_26)))


let add_string : FStar_Bytes.bytebuf  ->  Prims.string  ->  Prims.unit = (fun buf x -> (

let uu____77 = (FStar_Bytes.string_as_unicode_bytes x)
in (FStar_Bytes.emit_bytes buf uu____77)))


let add_int_char : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> ((FStar_Bytes.emit_int_as_byte buf (c mod (Prims.parse_int "256")));
(FStar_Bytes.emit_int_as_byte buf (c / (Prims.parse_int "256")));
))


let add_unichar : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> (add_int_char buf c))


let add_byte_char : FStar_Bytes.bytebuf  ->  FStar_BaseTypes.char  ->  Prims.unit = (fun buf c -> (add_int_char buf ((FStar_Util.int_of_char c) mod (Prims.parse_int "256"))))


let stringbuf_as_bytes : FStar_Bytes.bytebuf  ->  FStar_Bytes.bytes = (fun buf -> (

let bytes = (FStar_Bytes.close buf)
in (

let uu____101 = (

let uu____102 = (FStar_Bytes.length bytes)
in (uu____102 / (Prims.parse_int "2")))
in (FStar_Bytes.make (fun i -> (FStar_Bytes.get bytes (FStar_Mul.op_Star i (Prims.parse_int "2")))) uu____101))))


let stringbuf_is_bytes : FStar_Bytes.bytebuf  ->  Prims.bool = (fun buf -> (

let bytes = (FStar_Bytes.close buf)
in (

let ok = (FStar_Util.mk_ref true)
in ((

let uu____115 = (

let uu____116 = (

let uu____117 = (FStar_Bytes.length bytes)
in (uu____117 / (Prims.parse_int "2")))
in (uu____116 - (Prims.parse_int "1")))
in (FStar_Util.for_range (Prims.parse_int "0") uu____115 (fun i -> (

let uu____122 = (

let uu____123 = (FStar_Bytes.get bytes ((FStar_Mul.op_Star i (Prims.parse_int "2")) + (Prims.parse_int "1")))
in (uu____123 <> (Prims.parse_int "0")))
in (match (uu____122) with
| true -> begin
(FStar_ST.write ok false)
end
| uu____126 -> begin
()
end)))));
(FStar_ST.read ok);
))))


let trigraph : FStar_BaseTypes.char  ->  FStar_BaseTypes.char  ->  FStar_BaseTypes.char  ->  FStar_BaseTypes.char = (fun c1 c2 c3 -> (

let digit = (fun c -> ((FStar_Util.int_of_char c) - (FStar_Util.int_of_char 48 (*0*))))
in (FStar_Util.char_of_int (((FStar_Mul.op_Star (digit c1) (Prims.parse_int "100")) + (FStar_Mul.op_Star (digit c2) (Prims.parse_int "10"))) + (digit c3)))))


let digit : FStar_BaseTypes.char  ->  Prims.int = (fun d -> (

let dd = (FStar_Util.int_of_char d)
in (match (((dd >= (FStar_Util.int_of_char 48 (*0*))) && (dd <= (FStar_Util.int_of_char 57 (*9*))))) with
| true -> begin
((FStar_Util.int_of_char d) - (FStar_Util.int_of_char 48 (*0*)))
end
| uu____146 -> begin
(failwith "digit")
end)))


let hexdigit : FStar_BaseTypes.char  ->  Prims.int = (fun d -> (

let dd = (FStar_Util.int_of_char d)
in (match (((dd >= (FStar_Util.int_of_char 48 (*0*))) && (dd <= (FStar_Util.int_of_char 57 (*9*))))) with
| true -> begin
(digit d)
end
| uu____151 -> begin
(match (((dd >= (FStar_Util.int_of_char 97 (*a*))) && (dd <= (FStar_Util.int_of_char 102 (*f*))))) with
| true -> begin
((dd - (FStar_Util.int_of_char 97 (*a*))) + (Prims.parse_int "10"))
end
| uu____152 -> begin
(match (((dd >= (FStar_Util.int_of_char 65 (*A*))) && (dd <= (FStar_Util.int_of_char 70 (*F*))))) with
| true -> begin
((dd - (FStar_Util.int_of_char 65 (*A*))) + (Prims.parse_int "10"))
end
| uu____153 -> begin
(failwith "hexdigit")
end)
end)
end)))


let unicodegraph_short : Prims.string  ->  FStar_BaseTypes.uint16 = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "4"))) with
| true -> begin
(failwith "unicodegraph")
end
| uu____159 -> begin
(

let uu____160 = (

let uu____161 = (

let uu____162 = (

let uu____163 = (

let uu____164 = (

let uu____165 = (FStar_Util.char_at s (Prims.parse_int "0"))
in (hexdigit uu____165))
in (FStar_Mul.op_Star uu____164 (Prims.parse_int "4096")))
in (

let uu____166 = (

let uu____167 = (

let uu____168 = (FStar_Util.char_at s (Prims.parse_int "1"))
in (hexdigit uu____168))
in (FStar_Mul.op_Star uu____167 (Prims.parse_int "256")))
in (uu____163 + uu____166)))
in (

let uu____169 = (

let uu____170 = (

let uu____171 = (FStar_Util.char_at s (Prims.parse_int "2"))
in (hexdigit uu____171))
in (FStar_Mul.op_Star uu____170 (Prims.parse_int "16")))
in (uu____162 + uu____169)))
in (

let uu____172 = (

let uu____173 = (FStar_Util.char_at s (Prims.parse_int "3"))
in (hexdigit uu____173))
in (uu____161 + uu____172)))
in (FStar_Util.uint16_of_int uu____160))
end))


let hexgraph_short : Prims.string  ->  FStar_BaseTypes.uint16 = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "2"))) with
| true -> begin
(failwith "hexgraph")
end
| uu____179 -> begin
(

let uu____180 = (

let uu____181 = (

let uu____182 = (

let uu____183 = (FStar_Util.char_at s (Prims.parse_int "0"))
in (hexdigit uu____183))
in (FStar_Mul.op_Star uu____182 (Prims.parse_int "16")))
in (

let uu____184 = (

let uu____185 = (FStar_Util.char_at s (Prims.parse_int "1"))
in (hexdigit uu____185))
in (uu____181 + uu____184)))
in (FStar_Util.uint16_of_int uu____180))
end))


let unicodegraph_long : Prims.string  ->  (FStar_BaseTypes.uint16 FStar_Pervasives_Native.option * FStar_BaseTypes.uint16) = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "8"))) with
| true -> begin
(failwith "unicodegraph_long")
end
| uu____200 -> begin
(

let high = (

let uu____202 = (

let uu____203 = (

let uu____204 = (

let uu____205 = (

let uu____206 = (FStar_Util.char_at s (Prims.parse_int "0"))
in (hexdigit uu____206))
in (FStar_Mul.op_Star uu____205 (Prims.parse_int "4096")))
in (

let uu____207 = (

let uu____208 = (

let uu____209 = (FStar_Util.char_at s (Prims.parse_int "1"))
in (hexdigit uu____209))
in (FStar_Mul.op_Star uu____208 (Prims.parse_int "256")))
in (uu____204 + uu____207)))
in (

let uu____210 = (

let uu____211 = (

let uu____212 = (FStar_Util.char_at s (Prims.parse_int "2"))
in (hexdigit uu____212))
in (FStar_Mul.op_Star uu____211 (Prims.parse_int "16")))
in (uu____203 + uu____210)))
in (

let uu____213 = (

let uu____214 = (FStar_Util.char_at s (Prims.parse_int "3"))
in (hexdigit uu____214))
in (uu____202 + uu____213)))
in (

let low = (

let uu____216 = (

let uu____217 = (

let uu____218 = (

let uu____219 = (

let uu____220 = (FStar_Util.char_at s (Prims.parse_int "4"))
in (hexdigit uu____220))
in (FStar_Mul.op_Star uu____219 (Prims.parse_int "4096")))
in (

let uu____221 = (

let uu____222 = (

let uu____223 = (FStar_Util.char_at s (Prims.parse_int "5"))
in (hexdigit uu____223))
in (FStar_Mul.op_Star uu____222 (Prims.parse_int "256")))
in (uu____218 + uu____221)))
in (

let uu____224 = (

let uu____225 = (

let uu____226 = (FStar_Util.char_at s (Prims.parse_int "6"))
in (hexdigit uu____226))
in (FStar_Mul.op_Star uu____225 (Prims.parse_int "16")))
in (uu____217 + uu____224)))
in (

let uu____227 = (

let uu____228 = (FStar_Util.char_at s (Prims.parse_int "7"))
in (hexdigit uu____228))
in (uu____216 + uu____227)))
in (match ((high = (Prims.parse_int "0"))) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Util.uint16_of_int low)))
end
| uu____233 -> begin
((FStar_Pervasives_Native.Some ((FStar_Util.uint16_of_int ((Prims.parse_int "0xD800") + ((((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) + low) - (Prims.parse_int "0x10000")) / (Prims.parse_int "0x400")))))), ((FStar_Util.uint16_of_int ((Prims.parse_int "0xDF30") + ((((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) + low) - (Prims.parse_int "0x10000")) mod (Prims.parse_int "0x400"))))))
end)))
end))


let escape : FStar_Char.char  ->  FStar_Char.char = (fun c -> (match (c) with
| 92 (*\*) -> begin
92 (*\*)
end
| 39 (*'*) -> begin
39 (*'*)
end
| 110 (*n*) -> begin
10
end
| 116 (*t*) -> begin
9
end
| 98 (*b*) -> begin
8
end
| 114 (*r*) -> begin
13
end
| c1 -> begin
c1
end))

type compatibilityMode =
| ALWAYS
| FSHARP


let uu___is_ALWAYS : compatibilityMode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ALWAYS -> begin
true
end
| uu____242 -> begin
false
end))


let uu___is_FSHARP : compatibilityMode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FSHARP -> begin
true
end
| uu____246 -> begin
false
end))


let keywords : (compatibilityMode * Prims.string * FStar_Parser_Parse.token) Prims.list = (((ALWAYS), ("abstract"), (FStar_Parser_Parse.ABSTRACT)))::(((ALWAYS), ("attributes"), (FStar_Parser_Parse.ATTRIBUTES)))::(((ALWAYS), ("noeq"), (FStar_Parser_Parse.NOEQUALITY)))::(((ALWAYS), ("unopteq"), (FStar_Parser_Parse.UNOPTEQUALITY)))::(((ALWAYS), ("and"), (FStar_Parser_Parse.AND)))::(((ALWAYS), ("assert"), (FStar_Parser_Parse.ASSERT)))::(((ALWAYS), ("assume"), (FStar_Parser_Parse.ASSUME)))::(((ALWAYS), ("begin"), (FStar_Parser_Parse.BEGIN)))::(((ALWAYS), ("by"), (FStar_Parser_Parse.BY)))::(((FSHARP), ("default"), (FStar_Parser_Parse.DEFAULT)))::(((ALWAYS), ("effect"), (FStar_Parser_Parse.EFFECT)))::(((ALWAYS), ("else"), (FStar_Parser_Parse.ELSE)))::(((ALWAYS), ("end"), (FStar_Parser_Parse.END)))::(((ALWAYS), ("ensures"), (FStar_Parser_Parse.ENSURES)))::(((ALWAYS), ("exception"), (FStar_Parser_Parse.EXCEPTION)))::(((ALWAYS), ("exists"), (FStar_Parser_Parse.EXISTS)))::(((ALWAYS), ("false"), (FStar_Parser_Parse.FALSE)))::(((ALWAYS), ("False"), (FStar_Parser_Parse.L_FALSE)))::(((ALWAYS), ("forall"), (FStar_Parser_Parse.FORALL)))::(((ALWAYS), ("fun"), (FStar_Parser_Parse.FUN)))::(((ALWAYS), ("function"), (FStar_Parser_Parse.FUNCTION)))::(((ALWAYS), ("if"), (FStar_Parser_Parse.IF)))::(((ALWAYS), ("in"), (FStar_Parser_Parse.IN)))::(((ALWAYS), ("include"), (FStar_Parser_Parse.INCLUDE)))::(((ALWAYS), ("inline"), (FStar_Parser_Parse.INLINE)))::(((ALWAYS), ("inline_for_extraction"), (FStar_Parser_Parse.INLINE_FOR_EXTRACTION)))::(((ALWAYS), ("irreducible"), (FStar_Parser_Parse.IRREDUCIBLE)))::(((ALWAYS), ("let"), (FStar_Parser_Parse.LET (false))))::(((ALWAYS), ("logic"), (FStar_Parser_Parse.LOGIC)))::(((ALWAYS), ("match"), (FStar_Parser_Parse.MATCH)))::(((ALWAYS), ("module"), (FStar_Parser_Parse.MODULE)))::(((ALWAYS), ("mutable"), (FStar_Parser_Parse.MUTABLE)))::(((ALWAYS), ("new"), (FStar_Parser_Parse.NEW)))::(((ALWAYS), ("new_effect"), (FStar_Parser_Parse.NEW_EFFECT)))::(((ALWAYS), ("noextract"), (FStar_Parser_Parse.NOEXTRACT)))::(((ALWAYS), ("of"), (FStar_Parser_Parse.OF)))::(((ALWAYS), ("open"), (FStar_Parser_Parse.OPEN)))::(((ALWAYS), ("opaque"), (FStar_Parser_Parse.OPAQUE)))::(((ALWAYS), ("private"), (FStar_Parser_Parse.PRIVATE)))::(((ALWAYS), ("rec"), (FStar_Parser_Parse.REC)))::(((ALWAYS), ("reifiable"), (FStar_Parser_Parse.REIFIABLE)))::(((ALWAYS), ("reify"), (FStar_Parser_Parse.REIFY)))::(((ALWAYS), ("reflectable"), (FStar_Parser_Parse.REFLECTABLE)))::(((ALWAYS), ("requires"), (FStar_Parser_Parse.REQUIRES)))::(((ALWAYS), ("sub_effect"), (FStar_Parser_Parse.SUB_EFFECT)))::(((ALWAYS), ("then"), (FStar_Parser_Parse.THEN)))::(((ALWAYS), ("total"), (FStar_Parser_Parse.TOTAL)))::(((ALWAYS), ("true"), (FStar_Parser_Parse.TRUE)))::(((ALWAYS), ("True"), (FStar_Parser_Parse.L_TRUE)))::(((ALWAYS), ("try"), (FStar_Parser_Parse.TRY)))::(((ALWAYS), ("type"), (FStar_Parser_Parse.TYPE)))::(((ALWAYS), ("unfold"), (FStar_Parser_Parse.UNFOLD)))::(((ALWAYS), ("unfoldable"), (FStar_Parser_Parse.UNFOLDABLE)))::(((ALWAYS), ("val"), (FStar_Parser_Parse.VAL)))::(((ALWAYS), ("when"), (FStar_Parser_Parse.WHEN)))::(((ALWAYS), ("with"), (FStar_Parser_Parse.WITH)))::(((ALWAYS), ("_"), (FStar_Parser_Parse.UNDERSCORE)))::[]


let stringKeywords : Prims.string Prims.list = (FStar_List.map (fun uu____429 -> (match (uu____429) with
| (uu____433, w, uu____435) -> begin
w
end)) keywords)


let unreserve_words : Prims.string Prims.list = (FStar_List.choose (fun uu____440 -> (match (uu____440) with
| (mode, keyword, uu____447) -> begin
(match ((mode = FSHARP)) with
| true -> begin
FStar_Pervasives_Native.Some (keyword)
end
| uu____449 -> begin
FStar_Pervasives_Native.None
end)
end)) keywords)


let kwd_table : FStar_Parser_Parse.token FStar_Util.smap = (

let tab = (FStar_Util.smap_create (Prims.parse_int "1000"))
in ((FStar_List.iter (fun uu____457 -> (match (uu____457) with
| (mode, keyword, token) -> begin
(FStar_Util.smap_add tab keyword token)
end)) keywords);
tab;
))


let kwd : Prims.string  ->  FStar_Parser_Parse.token FStar_Pervasives_Native.option = (fun s -> (FStar_Util.smap_try_find kwd_table s))

type lexargs =
{getSourceDirectory : Prims.unit  ->  Prims.string; filename : Prims.string; contents : Prims.string}


let mkLexargs : ((Prims.unit  ->  Prims.string) * Prims.string * Prims.string)  ->  lexargs = (fun uu____508 -> (match (uu____508) with
| (srcdir, filename, contents) -> begin
{getSourceDirectory = srcdir; filename = filename; contents = contents}
end))


let kwd_or_id : lexargs  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Parser_Parse.token = (fun args r s -> (

let uu____530 = (kwd s)
in (match (uu____530) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(match (s) with
| "__SOURCE_DIRECTORY__" -> begin
(

let uu____533 = (args.getSourceDirectory ())
in FStar_Parser_Parse.STRING (uu____533))
end
| "__SOURCE_FILE__" -> begin
(

let uu____534 = (FStar_Range.file_of_range r)
in FStar_Parser_Parse.STRING (uu____534))
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
(FStar_Pervasives.raise (FStar_Errors.Error ((((Prims.strcat FStar_Ident.reserved_prefix " is a reserved prefix for an identifier")), (r)))))
end
| uu____542 -> begin
(

let uu____543 = (intern_string s)
in FStar_Parser_Parse.IDENT (uu____543))
end)
end)
end)))




