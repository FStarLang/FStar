
open Prims
# 39 "FStar.Parser.Lexhelp.fst"
let intern_string : Prims.string  ->  Prims.string = (
# 40 "FStar.Parser.Lexhelp.fst"
let strings = (FStar_Util.smap_create 100)
in (fun s -> (match ((FStar_Util.smap_try_find strings s)) with
| Some (res) -> begin
res
end
| None -> begin
(
# 44 "FStar.Parser.Lexhelp.fst"
let _53_6 = (FStar_Util.smap_add strings s s)
in s)
end)))

# 46 "FStar.Parser.Lexhelp.fst"
let default_string_finish = (fun endm b s -> FStar_Parser_Parse.STRING (s))

# 48 "FStar.Parser.Lexhelp.fst"
let call_string_finish = (fun fin buf endm b -> (let _134_19 = (FStar_Bytes.close buf)
in (fin endm b _134_19)))

# 50 "FStar.Parser.Lexhelp.fst"
let add_string : FStar_Bytes.bytebuf  ->  Prims.string  ->  Prims.unit = (fun buf x -> (let _134_24 = (FStar_Bytes.string_as_unicode_bytes x)
in (FStar_Bytes.emit_bytes buf _134_24)))

# 52 "FStar.Parser.Lexhelp.fst"
let add_int_char : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> (
# 53 "FStar.Parser.Lexhelp.fst"
let _53_19 = (FStar_Bytes.emit_int_as_byte buf (c % 256))
in (FStar_Bytes.emit_int_as_byte buf (c / 256))))

# 56 "FStar.Parser.Lexhelp.fst"
let add_unichar : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> (add_int_char buf c))

# 57 "FStar.Parser.Lexhelp.fst"
let add_byte_char : FStar_Bytes.bytebuf  ->  Prims.char  ->  Prims.unit = (fun buf c -> (add_int_char buf ((FStar_Util.int_of_char c) % 256)))

# 64 "FStar.Parser.Lexhelp.fst"
let stringbuf_as_bytes : FStar_Bytes.bytebuf  ->  FStar_Bytes.bytes = (fun buf -> (
# 65 "FStar.Parser.Lexhelp.fst"
let bytes = (FStar_Bytes.close buf)
in (let _134_40 = ((FStar_Bytes.length bytes) / 2)
in (FStar_Bytes.make (fun i -> (FStar_Bytes.get bytes (i * 2))) _134_40))))

# 69 "FStar.Parser.Lexhelp.fst"
let stringbuf_is_bytes : FStar_Bytes.bytebuf  ->  Prims.bool = (fun buf -> (
# 70 "FStar.Parser.Lexhelp.fst"
let bytes = (FStar_Bytes.close buf)
in (
# 71 "FStar.Parser.Lexhelp.fst"
let ok = (FStar_Util.mk_ref true)
in (
# 72 "FStar.Parser.Lexhelp.fst"
let _53_32 = (let _134_44 = (((FStar_Bytes.length bytes) / 2) - 1)
in (FStar_Util.for_range 0 _134_44 (fun i -> if ((FStar_Bytes.get bytes ((i * 2) + 1)) <> 0) then begin
(FStar_ST.op_Colon_Equals ok false)
end else begin
()
end)))
in (FStar_ST.read ok)))))

# 78 "FStar.Parser.Lexhelp.fst"
let trigraph : Prims.char  ->  Prims.char  ->  Prims.char  ->  Prims.char = (fun c1 c2 c3 -> (
# 79 "FStar.Parser.Lexhelp.fst"
let digit = (fun c -> ((FStar_Util.int_of_char c) - (FStar_Util.int_of_char '0')))
in (FStar_Util.char_of_int (((digit c1) * 100) + (((digit c2) * 10) + (digit c3))))))

# 82 "FStar.Parser.Lexhelp.fst"
let digit : Prims.char  ->  Prims.int = (fun d -> (
# 83 "FStar.Parser.Lexhelp.fst"
let dd = (FStar_Util.int_of_char d)
in if ((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9'))) then begin
((FStar_Util.int_of_char d) - (FStar_Util.int_of_char '0'))
end else begin
(FStar_All.failwith "digit")
end))

# 87 "FStar.Parser.Lexhelp.fst"
let hexdigit : Prims.char  ->  Prims.int = (fun d -> (
# 88 "FStar.Parser.Lexhelp.fst"
let dd = (FStar_Util.int_of_char d)
in if ((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9'))) then begin
(digit d)
end else begin
if ((dd >= (FStar_Util.int_of_char 'a')) && (dd <= (FStar_Util.int_of_char 'f'))) then begin
((dd - (FStar_Util.int_of_char 'a')) + 10)
end else begin
if ((dd >= (FStar_Util.int_of_char 'A')) && (dd <= (FStar_Util.int_of_char 'F'))) then begin
((dd - (FStar_Util.int_of_char 'A')) + 10)
end else begin
(FStar_All.failwith "hexdigit")
end
end
end))

# 94 "FStar.Parser.Lexhelp.fst"
let unicodegraph_short : Prims.string  ->  Prims.uint16 = (fun s -> if ((FStar_String.length s) <> 4) then begin
(FStar_All.failwith "unicodegraph")
end else begin
(let _134_63 = (((let _134_59 = (FStar_Util.char_at s 0)
in (hexdigit _134_59)) * 4096) + (((let _134_60 = (FStar_Util.char_at s 1)
in (hexdigit _134_60)) * 256) + (((let _134_61 = (FStar_Util.char_at s 2)
in (hexdigit _134_61)) * 16) + (let _134_62 = (FStar_Util.char_at s 3)
in (hexdigit _134_62)))))
in (FStar_Util.uint16_of_int _134_63))
end)

# 99 "FStar.Parser.Lexhelp.fst"
let hexgraph_short : Prims.string  ->  Prims.uint16 = (fun s -> if ((FStar_String.length s) <> 2) then begin
(FStar_All.failwith "hexgraph")
end else begin
(let _134_68 = (((let _134_66 = (FStar_Util.char_at s 0)
in (hexdigit _134_66)) * 16) + (let _134_67 = (FStar_Util.char_at s 1)
in (hexdigit _134_67)))
in (FStar_Util.uint16_of_int _134_68))
end)

# 104 "FStar.Parser.Lexhelp.fst"
let unicodegraph_long : Prims.string  ->  (Prims.uint16 Prims.option * Prims.uint16) = (fun s -> if ((FStar_String.length s) <> 8) then begin
(FStar_All.failwith "unicodegraph_long")
end else begin
(
# 108 "FStar.Parser.Lexhelp.fst"
let high = (((let _134_71 = (FStar_Util.char_at s 0)
in (hexdigit _134_71)) * 4096) + (((let _134_72 = (FStar_Util.char_at s 1)
in (hexdigit _134_72)) * 256) + (((let _134_73 = (FStar_Util.char_at s 2)
in (hexdigit _134_73)) * 16) + (let _134_74 = (FStar_Util.char_at s 3)
in (hexdigit _134_74)))))
in (
# 109 "FStar.Parser.Lexhelp.fst"
let low = (((let _134_75 = (FStar_Util.char_at s 4)
in (hexdigit _134_75)) * 4096) + (((let _134_76 = (FStar_Util.char_at s 5)
in (hexdigit _134_76)) * 256) + (((let _134_77 = (FStar_Util.char_at s 6)
in (hexdigit _134_77)) * 16) + (let _134_78 = (FStar_Util.char_at s 7)
in (hexdigit _134_78)))))
in if (high = 0) then begin
(None, (FStar_Util.uint16_of_int low))
end else begin
(Some ((FStar_Util.uint16_of_int (0xD800 + (((high * 0x10000) + (low - 0x10000)) / 0x400)))), (FStar_Util.uint16_of_int (0xDF30 + (((high * 0x10000) + (low - 0x10000)) % 0x400))))
end))
end)

# 116 "FStar.Parser.Lexhelp.fst"
let escape : Prims.char  ->  Prims.char = (fun c -> (match (c) with
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

# 130 "FStar.Parser.Lexhelp.fst"
type compatibilityMode =
| ALWAYS
| FSHARP

# 131 "FStar.Parser.Lexhelp.fst"
let is_ALWAYS = (fun _discr_ -> (match (_discr_) with
| ALWAYS (_) -> begin
true
end
| _ -> begin
false
end))

# 132 "FStar.Parser.Lexhelp.fst"
let is_FSHARP = (fun _discr_ -> (match (_discr_) with
| FSHARP (_) -> begin
true
end
| _ -> begin
false
end))

# 134 "FStar.Parser.Lexhelp.fst"
let keywords : (compatibilityMode * Prims.string * FStar_Parser_Parse.token) Prims.list = (let _134_84 = (FStar_List.map (fun s -> (FSHARP, s, FStar_Parser_Parse.RESERVED)) (("atomic")::("break")::("checked")::("component")::("constraint")::("constructor")::("continue")::("eager")::("fixed")::("functor")::("global")::("include")::("mixin")::("parallel")::("process")::("protected")::("pure")::("sealed")::("trait")::("tailcall")::("volatile")::[]))
in (FStar_List.append (((ALWAYS, "abstract", FStar_Parser_Parse.ABSTRACT))::((ALWAYS, "and", FStar_Parser_Parse.AND))::((ALWAYS, "as", FStar_Parser_Parse.AS))::((ALWAYS, "assert", FStar_Parser_Parse.ASSERT))::((ALWAYS, "assume", FStar_Parser_Parse.ASSUME))::((ALWAYS, "begin", FStar_Parser_Parse.BEGIN))::((FSHARP, "default", FStar_Parser_Parse.DEFAULT))::((ALWAYS, "effect", FStar_Parser_Parse.EFFECT))::((ALWAYS, "else", FStar_Parser_Parse.ELSE))::((ALWAYS, "end", FStar_Parser_Parse.END))::((ALWAYS, "ensures", FStar_Parser_Parse.ENSURES))::((ALWAYS, "exception", FStar_Parser_Parse.EXCEPTION))::((ALWAYS, "exists", FStar_Parser_Parse.EXISTS))::((ALWAYS, "false", FStar_Parser_Parse.FALSE))::((ALWAYS, "finally", FStar_Parser_Parse.FINALLY))::((ALWAYS, "for", FStar_Parser_Parse.FOR))::((ALWAYS, "forall", FStar_Parser_Parse.FORALL))::((ALWAYS, "fun", FStar_Parser_Parse.FUN))::((ALWAYS, "function", FStar_Parser_Parse.FUNCTION))::((ALWAYS, "if", FStar_Parser_Parse.IF))::((ALWAYS, "kind", FStar_Parser_Parse.KIND))::((ALWAYS, "in", FStar_Parser_Parse.IN))::((ALWAYS, "inline", FStar_Parser_Parse.INLINE))::((ALWAYS, "irreducible", FStar_Parser_Parse.IRREDUCIBLE))::((ALWAYS, "lazy", FStar_Parser_Parse.LAZY))::((ALWAYS, "let", FStar_Parser_Parse.LET (false)))::((ALWAYS, "logic", FStar_Parser_Parse.LOGIC))::((ALWAYS, "match", FStar_Parser_Parse.MATCH))::((ALWAYS, "module", FStar_Parser_Parse.MODULE))::((ALWAYS, "new", FStar_Parser_Parse.NEW))::((ALWAYS, "new_effect", FStar_Parser_Parse.NEW_EFFECT))::((ALWAYS, "of", FStar_Parser_Parse.OF))::((ALWAYS, "open", FStar_Parser_Parse.OPEN))::((ALWAYS, "or", FStar_Parser_Parse.OR))::((ALWAYS, "opaque", FStar_Parser_Parse.OPAQUE))::((ALWAYS, "private", FStar_Parser_Parse.PRIVATE))::((FSHARP, "public", FStar_Parser_Parse.PUBLIC))::((ALWAYS, "rec", FStar_Parser_Parse.REC))::((ALWAYS, "requires", FStar_Parser_Parse.REQUIRES))::((ALWAYS, "sub_effect", FStar_Parser_Parse.SUB_EFFECT))::((ALWAYS, "then", FStar_Parser_Parse.THEN))::((ALWAYS, "to", FStar_Parser_Parse.TO))::((ALWAYS, "total", FStar_Parser_Parse.TOTAL))::((ALWAYS, "true", FStar_Parser_Parse.TRUE))::((ALWAYS, "try", FStar_Parser_Parse.TRY))::((ALWAYS, "type", FStar_Parser_Parse.TYPE))::((ALWAYS, "unfoldable", FStar_Parser_Parse.UNFOLDABLE))::((ALWAYS, "val", FStar_Parser_Parse.VAL))::((ALWAYS, "when", FStar_Parser_Parse.WHEN))::((ALWAYS, "with", FStar_Parser_Parse.WITH))::((ALWAYS, "_", FStar_Parser_Parse.UNDERSCORE))::[]) _134_84))

# 199 "FStar.Parser.Lexhelp.fst"
let stringKeywords : Prims.string Prims.list = (FStar_List.map (fun _53_62 -> (match (_53_62) with
| (_53_58, w, _53_61) -> begin
w
end)) keywords)

# 205 "FStar.Parser.Lexhelp.fst"
let unreserve_words : Prims.string Prims.list = (FStar_List.choose (fun _53_67 -> (match (_53_67) with
| (mode, keyword, _53_66) -> begin
if (mode = FSHARP) then begin
Some (keyword)
end else begin
None
end
end)) keywords)

# 208 "FStar.Parser.Lexhelp.fst"
let kwd_table : FStar_Parser_Parse.token FStar_Util.smap = (
# 209 "FStar.Parser.Lexhelp.fst"
let tab = (FStar_Util.smap_create 1000)
in (
# 210 "FStar.Parser.Lexhelp.fst"
let _53_73 = (FStar_List.iter (fun _53_72 -> (match (_53_72) with
| (mode, keyword, token) -> begin
(FStar_Util.smap_add tab keyword token)
end)) keywords)
in tab))

# 212 "FStar.Parser.Lexhelp.fst"
let kwd : Prims.string  ->  FStar_Parser_Parse.token Prims.option = (fun s -> (FStar_Util.smap_try_find kwd_table s))

# 213 "FStar.Parser.Lexhelp.fst"
exception ReservedKeyword of ((Prims.string * FStar_Range.range))

# 213 "FStar.Parser.Lexhelp.fst"
let is_ReservedKeyword = (fun _discr_ -> (match (_discr_) with
| ReservedKeyword (_) -> begin
true
end
| _ -> begin
false
end))

# 213 "FStar.Parser.Lexhelp.fst"
let ___ReservedKeyword____0 : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| ReservedKeyword (_53_77) -> begin
_53_77
end))

# 214 "FStar.Parser.Lexhelp.fst"
exception IndentationProblem of ((Prims.string * FStar_Range.range))

# 214 "FStar.Parser.Lexhelp.fst"
let is_IndentationProblem = (fun _discr_ -> (match (_discr_) with
| IndentationProblem (_) -> begin
true
end
| _ -> begin
false
end))

# 214 "FStar.Parser.Lexhelp.fst"
let ___IndentationProblem____0 : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| IndentationProblem (_53_79) -> begin
_53_79
end))

# 216 "FStar.Parser.Lexhelp.fst"
type lexargs =
{getSourceDirectory : Prims.unit  ->  Prims.string; contents : Prims.string}

# 216 "FStar.Parser.Lexhelp.fst"
let is_Mklexargs : lexargs  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklexargs"))))

# 221 "FStar.Parser.Lexhelp.fst"
let mkLexargs = (fun _53_86 -> (match (_53_86) with
| (srcdir, filename, contents) -> begin
{getSourceDirectory = srcdir; contents = contents}
end))

# 226 "FStar.Parser.Lexhelp.fst"
let kwd_or_id : lexargs  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Parser_Parse.token = (fun args r s -> (match ((kwd s)) with
| Some (v) -> begin
if (v = FStar_Parser_Parse.RESERVED) then begin
(
# 231 "FStar.Parser.Lexhelp.fst"
let _53_92 = (let _134_127 = (let _134_126 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "The keyword \'%s\' is reserved for future use by F#. (%s)" s _134_126))
in (FStar_Util.print_string _134_127))
in (let _134_128 = (intern_string s)
in FStar_Parser_Parse.IDENT (_134_128)))
end else begin
v
end
end
| None -> begin
(match (s) with
| "__SOURCE_DIRECTORY__" -> begin
(let _134_130 = (let _134_129 = (args.getSourceDirectory ())
in (FStar_Bytes.string_as_unicode_bytes _134_129))
in FStar_Parser_Parse.STRING (_134_130))
end
| "__SOURCE_FILE__" -> begin
(let _134_132 = (let _134_131 = (FStar_Range.file_of_range r)
in (FStar_Bytes.string_as_unicode_bytes _134_131))
in FStar_Parser_Parse.STRING (_134_132))
end
| "__LINE__" -> begin
(let _134_136 = (let _134_135 = (let _134_134 = (let _134_133 = (FStar_Range.start_of_range r)
in (FStar_Range.line_of_pos _134_133))
in (FStar_All.pipe_left FStar_Util.string_of_int _134_134))
in (_134_135, false))
in FStar_Parser_Parse.INT (_134_136))
end
| _53_99 -> begin
(let _134_137 = (intern_string s)
in FStar_Parser_Parse.IDENT (_134_137))
end)
end))




