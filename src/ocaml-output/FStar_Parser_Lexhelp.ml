
open Prims
open FStar_Pervasives

let intern_string : Prims.string  ->  Prims.string = (

let strings = (FStar_Util.smap_create (Prims.parse_int "100"))
in (fun s -> (

let uu____7 = (FStar_Util.smap_try_find strings s)
in (match (uu____7) with
| FStar_Pervasives_Native.Some (res) -> begin
res
end
| FStar_Pervasives_Native.None -> begin
((FStar_Util.smap_add strings s s);
s;
)
end))))


let default_string_finish = (fun endm b s -> FStar_Parser_Parse.STRING (s))


let call_string_finish = (fun fin buf endm b -> (let _0_26 = (FStar_Bytes.close buf)
in (fin endm b _0_26)))


let add_string : FStar_Bytes.bytebuf  ->  Prims.string  ->  Prims.unit = (fun buf x -> (

let uu____91 = (FStar_Bytes.string_as_unicode_bytes x)
in (FStar_Bytes.emit_bytes buf uu____91)))


let add_int_char : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> ((FStar_Bytes.emit_int_as_byte buf (c mod (Prims.parse_int "256")));
(FStar_Bytes.emit_int_as_byte buf (c / (Prims.parse_int "256")));
))


let add_unichar : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> (add_int_char buf c))


let add_byte_char : FStar_Bytes.bytebuf  ->  FStar_BaseTypes.char  ->  Prims.unit = (fun buf c -> (add_int_char buf ((FStar_Util.int_of_char c) mod (Prims.parse_int "256"))))


let stringbuf_as_bytes : FStar_Bytes.bytebuf  ->  FStar_Bytes.bytes = (fun buf -> (

let bytes = (FStar_Bytes.close buf)
in (

let uu____122 = (

let uu____123 = (FStar_Bytes.length bytes)
in (uu____123 / (Prims.parse_int "2")))
in (FStar_Bytes.make (fun i -> (FStar_Bytes.get bytes (FStar_Mul.op_Star i (Prims.parse_int "2")))) uu____122))))


let stringbuf_is_bytes : FStar_Bytes.bytebuf  ->  Prims.bool = (fun buf -> (

let bytes = (FStar_Bytes.close buf)
in (

let ok = (FStar_Util.mk_ref true)
in ((

let uu____142 = (

let uu____143 = (

let uu____144 = (FStar_Bytes.length bytes)
in (uu____144 / (Prims.parse_int "2")))
in (uu____143 - (Prims.parse_int "1")))
in (FStar_Util.for_range (Prims.parse_int "0") uu____142 (fun i -> (

let uu____154 = (

let uu____155 = (FStar_Bytes.get bytes ((FStar_Mul.op_Star i (Prims.parse_int "2")) + (Prims.parse_int "1")))
in (uu____155 <> (Prims.parse_int "0")))
in (match (uu____154) with
| true -> begin
(FStar_ST.write ok false)
end
| uu____158 -> begin
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
| uu____182 -> begin
(failwith "digit")
end)))


let hexdigit : FStar_BaseTypes.char  ->  Prims.int = (fun d -> (

let dd = (FStar_Util.int_of_char d)
in (match (((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9')))) with
| true -> begin
(digit d)
end
| uu____188 -> begin
(match (((dd >= (FStar_Util.int_of_char 'a')) && (dd <= (FStar_Util.int_of_char 'f')))) with
| true -> begin
((dd - (FStar_Util.int_of_char 'a')) + (Prims.parse_int "10"))
end
| uu____189 -> begin
(match (((dd >= (FStar_Util.int_of_char 'A')) && (dd <= (FStar_Util.int_of_char 'F')))) with
| true -> begin
((dd - (FStar_Util.int_of_char 'A')) + (Prims.parse_int "10"))
end
| uu____190 -> begin
(failwith "hexdigit")
end)
end)
end)))


let unicodegraph_short : Prims.string  ->  FStar_BaseTypes.uint16 = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "4"))) with
| true -> begin
(failwith "unicodegraph")
end
| uu____199 -> begin
(

let uu____200 = (

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
in (FStar_Util.uint16_of_int uu____200))
end))


let hexgraph_short : Prims.string  ->  FStar_BaseTypes.uint16 = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "2"))) with
| true -> begin
(failwith "hexgraph")
end
| uu____222 -> begin
(

let uu____223 = (

let uu____224 = (

let uu____225 = (

let uu____226 = (FStar_Util.char_at s (Prims.parse_int "0"))
in (hexdigit uu____226))
in (FStar_Mul.op_Star uu____225 (Prims.parse_int "16")))
in (

let uu____227 = (

let uu____228 = (FStar_Util.char_at s (Prims.parse_int "1"))
in (hexdigit uu____228))
in (uu____224 + uu____227)))
in (FStar_Util.uint16_of_int uu____223))
end))


let unicodegraph_long : Prims.string  ->  (FStar_BaseTypes.uint16 FStar_Pervasives_Native.option * FStar_BaseTypes.uint16) = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "8"))) with
| true -> begin
(failwith "unicodegraph_long")
end
| uu____246 -> begin
(

let high = (

let uu____248 = (

let uu____249 = (

let uu____250 = (

let uu____251 = (

let uu____252 = (FStar_Util.char_at s (Prims.parse_int "0"))
in (hexdigit uu____252))
in (FStar_Mul.op_Star uu____251 (Prims.parse_int "4096")))
in (

let uu____253 = (

let uu____254 = (

let uu____255 = (FStar_Util.char_at s (Prims.parse_int "1"))
in (hexdigit uu____255))
in (FStar_Mul.op_Star uu____254 (Prims.parse_int "256")))
in (uu____250 + uu____253)))
in (

let uu____256 = (

let uu____257 = (

let uu____258 = (FStar_Util.char_at s (Prims.parse_int "2"))
in (hexdigit uu____258))
in (FStar_Mul.op_Star uu____257 (Prims.parse_int "16")))
in (uu____249 + uu____256)))
in (

let uu____259 = (

let uu____260 = (FStar_Util.char_at s (Prims.parse_int "3"))
in (hexdigit uu____260))
in (uu____248 + uu____259)))
in (

let low = (

let uu____262 = (

let uu____263 = (

let uu____264 = (

let uu____265 = (

let uu____266 = (FStar_Util.char_at s (Prims.parse_int "4"))
in (hexdigit uu____266))
in (FStar_Mul.op_Star uu____265 (Prims.parse_int "4096")))
in (

let uu____267 = (

let uu____268 = (

let uu____269 = (FStar_Util.char_at s (Prims.parse_int "5"))
in (hexdigit uu____269))
in (FStar_Mul.op_Star uu____268 (Prims.parse_int "256")))
in (uu____264 + uu____267)))
in (

let uu____270 = (

let uu____271 = (

let uu____272 = (FStar_Util.char_at s (Prims.parse_int "6"))
in (hexdigit uu____272))
in (FStar_Mul.op_Star uu____271 (Prims.parse_int "16")))
in (uu____263 + uu____270)))
in (

let uu____273 = (

let uu____274 = (FStar_Util.char_at s (Prims.parse_int "7"))
in (hexdigit uu____274))
in (uu____262 + uu____273)))
in (match ((high = (Prims.parse_int "0"))) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Util.uint16_of_int low)))
end
| uu____279 -> begin
((FStar_Pervasives_Native.Some ((FStar_Util.uint16_of_int ((Prims.parse_int "0xD800") + ((((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) + low) - (Prims.parse_int "0x10000")) / (Prims.parse_int "0x400")))))), ((FStar_Util.uint16_of_int ((Prims.parse_int "0xDF30") + ((((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) + low) - (Prims.parse_int "0x10000")) mod (Prims.parse_int "0x400"))))))
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
| uu____290 -> begin
false
end))


let uu___is_FSHARP : compatibilityMode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FSHARP -> begin
true
end
| uu____295 -> begin
false
end))


let keywords : (compatibilityMode * Prims.string * FStar_Parser_Parse.token) Prims.list = (((ALWAYS), ("abstract"), (FStar_Parser_Parse.ABSTRACT)))::(((ALWAYS), ("attributes"), (FStar_Parser_Parse.ATTRIBUTES)))::(((ALWAYS), ("noeq"), (FStar_Parser_Parse.NOEQUALITY)))::(((ALWAYS), ("unopteq"), (FStar_Parser_Parse.UNOPTEQUALITY)))::(((ALWAYS), ("and"), (FStar_Parser_Parse.AND)))::(((ALWAYS), ("assert"), (FStar_Parser_Parse.ASSERT)))::(((ALWAYS), ("assume"), (FStar_Parser_Parse.ASSUME)))::(((ALWAYS), ("begin"), (FStar_Parser_Parse.BEGIN)))::(((ALWAYS), ("by"), (FStar_Parser_Parse.BY)))::(((FSHARP), ("default"), (FStar_Parser_Parse.DEFAULT)))::(((ALWAYS), ("effect"), (FStar_Parser_Parse.EFFECT)))::(((ALWAYS), ("else"), (FStar_Parser_Parse.ELSE)))::(((ALWAYS), ("end"), (FStar_Parser_Parse.END)))::(((ALWAYS), ("ensures"), (FStar_Parser_Parse.ENSURES)))::(((ALWAYS), ("exception"), (FStar_Parser_Parse.EXCEPTION)))::(((ALWAYS), ("exists"), (FStar_Parser_Parse.EXISTS)))::(((ALWAYS), ("false"), (FStar_Parser_Parse.FALSE)))::(((ALWAYS), ("False"), (FStar_Parser_Parse.L_FALSE)))::(((ALWAYS), ("forall"), (FStar_Parser_Parse.FORALL)))::(((ALWAYS), ("fun"), (FStar_Parser_Parse.FUN)))::(((ALWAYS), ("function"), (FStar_Parser_Parse.FUNCTION)))::(((ALWAYS), ("if"), (FStar_Parser_Parse.IF)))::(((ALWAYS), ("in"), (FStar_Parser_Parse.IN)))::(((ALWAYS), ("include"), (FStar_Parser_Parse.INCLUDE)))::(((ALWAYS), ("inline"), (FStar_Parser_Parse.INLINE)))::(((ALWAYS), ("inline_for_extraction"), (FStar_Parser_Parse.INLINE_FOR_EXTRACTION)))::(((ALWAYS), ("irreducible"), (FStar_Parser_Parse.IRREDUCIBLE)))::(((ALWAYS), ("let"), (FStar_Parser_Parse.LET (false))))::(((ALWAYS), ("logic"), (FStar_Parser_Parse.LOGIC)))::(((ALWAYS), ("match"), (FStar_Parser_Parse.MATCH)))::(((ALWAYS), ("module"), (FStar_Parser_Parse.MODULE)))::(((ALWAYS), ("mutable"), (FStar_Parser_Parse.MUTABLE)))::(((ALWAYS), ("new"), (FStar_Parser_Parse.NEW)))::(((ALWAYS), ("new_effect"), (FStar_Parser_Parse.NEW_EFFECT)))::(((ALWAYS), ("noextract"), (FStar_Parser_Parse.NOEXTRACT)))::(((ALWAYS), ("of"), (FStar_Parser_Parse.OF)))::(((ALWAYS), ("open"), (FStar_Parser_Parse.OPEN)))::(((ALWAYS), ("opaque"), (FStar_Parser_Parse.OPAQUE)))::(((ALWAYS), ("private"), (FStar_Parser_Parse.PRIVATE)))::(((ALWAYS), ("rec"), (FStar_Parser_Parse.REC)))::(((ALWAYS), ("reifiable"), (FStar_Parser_Parse.REIFIABLE)))::(((ALWAYS), ("reify"), (FStar_Parser_Parse.REIFY)))::(((ALWAYS), ("reflectable"), (FStar_Parser_Parse.REFLECTABLE)))::(((ALWAYS), ("requires"), (FStar_Parser_Parse.REQUIRES)))::(((ALWAYS), ("sub_effect"), (FStar_Parser_Parse.SUB_EFFECT)))::(((ALWAYS), ("then"), (FStar_Parser_Parse.THEN)))::(((ALWAYS), ("total"), (FStar_Parser_Parse.TOTAL)))::(((ALWAYS), ("true"), (FStar_Parser_Parse.TRUE)))::(((ALWAYS), ("True"), (FStar_Parser_Parse.L_TRUE)))::(((ALWAYS), ("try"), (FStar_Parser_Parse.TRY)))::(((ALWAYS), ("type"), (FStar_Parser_Parse.TYPE)))::(((ALWAYS), ("unfold"), (FStar_Parser_Parse.UNFOLD)))::(((ALWAYS), ("unfoldable"), (FStar_Parser_Parse.UNFOLDABLE)))::(((ALWAYS), ("val"), (FStar_Parser_Parse.VAL)))::(((ALWAYS), ("when"), (FStar_Parser_Parse.WHEN)))::(((ALWAYS), ("with"), (FStar_Parser_Parse.WITH)))::(((ALWAYS), ("_"), (FStar_Parser_Parse.UNDERSCORE)))::[]


let stringKeywords : Prims.string Prims.list = (FStar_List.map (fun uu____482 -> (match (uu____482) with
| (uu____486, w, uu____488) -> begin
w
end)) keywords)


let unreserve_words : Prims.string Prims.list = (FStar_List.choose (fun uu____497 -> (match (uu____497) with
| (mode, keyword, uu____504) -> begin
(match ((mode = FSHARP)) with
| true -> begin
FStar_Pervasives_Native.Some (keyword)
end
| uu____506 -> begin
FStar_Pervasives_Native.None
end)
end)) keywords)


let kwd_table : FStar_Parser_Parse.token FStar_Util.smap = (

let tab = (FStar_Util.smap_create (Prims.parse_int "1000"))
in ((FStar_List.iter (fun uu____518 -> (match (uu____518) with
| (mode, keyword, token) -> begin
(FStar_Util.smap_add tab keyword token)
end)) keywords);
tab;
))


let kwd : Prims.string  ->  FStar_Parser_Parse.token FStar_Pervasives_Native.option = (fun s -> (FStar_Util.smap_try_find kwd_table s))

type lexargs =
{getSourceDirectory : Prims.unit  ->  Prims.string; filename : Prims.string; contents : Prims.string}


let __proj__Mklexargs__item__getSourceDirectory : lexargs  ->  Prims.unit  ->  Prims.string = (fun projectee -> (match (projectee) with
| {getSourceDirectory = __fname__getSourceDirectory; filename = __fname__filename; contents = __fname__contents} -> begin
__fname__getSourceDirectory
end))


let __proj__Mklexargs__item__filename : lexargs  ->  Prims.string = (fun projectee -> (match (projectee) with
| {getSourceDirectory = __fname__getSourceDirectory; filename = __fname__filename; contents = __fname__contents} -> begin
__fname__filename
end))


let __proj__Mklexargs__item__contents : lexargs  ->  Prims.string = (fun projectee -> (match (projectee) with
| {getSourceDirectory = __fname__getSourceDirectory; filename = __fname__filename; contents = __fname__contents} -> begin
__fname__contents
end))


let mkLexargs : ((Prims.unit  ->  Prims.string) * Prims.string * Prims.string)  ->  lexargs = (fun uu____587 -> (match (uu____587) with
| (srcdir, filename, contents) -> begin
{getSourceDirectory = srcdir; filename = filename; contents = contents}
end))


let kwd_or_id : lexargs  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Parser_Parse.token = (fun args r s -> (

let uu____612 = (kwd s)
in (match (uu____612) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(match (s) with
| "__SOURCE_DIRECTORY__" -> begin
(

let uu____615 = (

let uu____616 = (args.getSourceDirectory ())
in (FStar_Bytes.string_as_unicode_bytes uu____616))
in FStar_Parser_Parse.STRING (uu____615))
end
| "__SOURCE_FILE__" -> begin
(

let uu____617 = (

let uu____618 = (FStar_Range.file_of_range r)
in (FStar_Bytes.string_as_unicode_bytes uu____618))
in FStar_Parser_Parse.STRING (uu____617))
end
| "__LINE__" -> begin
(

let uu____619 = (

let uu____622 = (

let uu____623 = (

let uu____624 = (FStar_Range.start_of_range r)
in (FStar_Range.line_of_pos uu____624))
in (FStar_All.pipe_left FStar_Util.string_of_int uu____623))
in ((uu____622), (false)))
in FStar_Parser_Parse.INT (uu____619))
end
| uu____625 -> begin
(match ((FStar_Util.starts_with s FStar_Ident.reserved_prefix)) with
| true -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((((Prims.strcat FStar_Ident.reserved_prefix " is a reserved prefix for an identifier")), (r)))))
end
| uu____626 -> begin
(

let uu____627 = (intern_string s)
in FStar_Parser_Parse.IDENT (uu____627))
end)
end)
end)))




