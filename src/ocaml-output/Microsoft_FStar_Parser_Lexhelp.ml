
let intern_string = (let strings = (Support.Microsoft.FStar.Util.smap_create 100)
in (fun ( s ) -> (match ((Support.Microsoft.FStar.Util.smap_try_find strings s)) with
| Some (res) -> begin
res
end
| None -> begin
(let _43_6 = (Support.Microsoft.FStar.Util.smap_add strings s s)
in s)
end)))

let default_string_finish = (fun ( endm ) ( b ) ( s ) -> Microsoft_FStar_Parser_Parse.STRING (s))

let call_string_finish = (fun ( fin ) ( buf ) ( endm ) ( b ) -> (let _68_20068 = (Support.Microsoft.FStar.Bytes.close buf)
in (fin endm b _68_20068)))

let add_string = (fun ( buf ) ( x ) -> (let _68_20073 = (Support.Microsoft.FStar.Bytes.string_as_unicode_bytes x)
in (Support.Microsoft.FStar.Bytes.emit_bytes buf _68_20073)))

let add_int_char = (fun ( buf ) ( c ) -> (let _43_19 = (Support.Microsoft.FStar.Bytes.emit_int_as_byte buf (c mod 256))
in (Support.Microsoft.FStar.Bytes.emit_int_as_byte buf (c / 256))))

let add_unichar = (fun ( buf ) ( c ) -> (add_int_char buf c))

let add_byte_char = (fun ( buf ) ( c ) -> (add_int_char buf ((Support.Microsoft.FStar.Util.int_of_char c) mod 256)))

let stringbuf_as_bytes = (fun ( buf ) -> (let bytes = (Support.Microsoft.FStar.Bytes.close buf)
in (let _68_20089 = ((Support.Microsoft.FStar.Bytes.length bytes) / 2)
in (Support.Microsoft.FStar.Bytes.make (fun ( i ) -> (Support.Microsoft.FStar.Bytes.get bytes (i * 2))) _68_20089))))

let stringbuf_is_bytes = (fun ( buf ) -> (let bytes = (Support.Microsoft.FStar.Bytes.close buf)
in (let ok = (Support.Microsoft.FStar.Util.mk_ref true)
in (let _43_32 = (let _68_20093 = (((Support.Microsoft.FStar.Bytes.length bytes) / 2) - 1)
in (Support.Microsoft.FStar.Util.for_range 0 _68_20093 (fun ( i ) -> (match (((Support.Microsoft.FStar.Bytes.get bytes ((i * 2) + 1)) <> 0)) with
| true -> begin
(Support.ST.op_Colon_Equals ok false)
end
| false -> begin
()
end))))
in (Support.ST.read ok)))))

let trigraph = (fun ( c1 ) ( c2 ) ( c3 ) -> (let digit = (fun ( c ) -> ((Support.Microsoft.FStar.Util.int_of_char c) - (Support.Microsoft.FStar.Util.int_of_char '0')))
in (Support.Microsoft.FStar.Util.char_of_int (((digit c1) * 100) + (((digit c2) * 10) + (digit c3))))))

let digit = (fun ( d ) -> (let dd = (Support.Microsoft.FStar.Util.int_of_char d)
in (match (((dd >= (Support.Microsoft.FStar.Util.int_of_char '0')) && (dd <= (Support.Microsoft.FStar.Util.int_of_char '9')))) with
| true -> begin
((Support.Microsoft.FStar.Util.int_of_char d) - (Support.Microsoft.FStar.Util.int_of_char '0'))
end
| false -> begin
(failwith ("digit"))
end)))

let hexdigit = (fun ( d ) -> (let dd = (Support.Microsoft.FStar.Util.int_of_char d)
in (match (((dd >= (Support.Microsoft.FStar.Util.int_of_char '0')) && (dd <= (Support.Microsoft.FStar.Util.int_of_char '9')))) with
| true -> begin
(digit d)
end
| false -> begin
(match (((dd >= (Support.Microsoft.FStar.Util.int_of_char 'a')) && (dd <= (Support.Microsoft.FStar.Util.int_of_char 'f')))) with
| true -> begin
((dd - (Support.Microsoft.FStar.Util.int_of_char 'a')) + 10)
end
| false -> begin
(match (((dd >= (Support.Microsoft.FStar.Util.int_of_char 'A')) && (dd <= (Support.Microsoft.FStar.Util.int_of_char 'F')))) with
| true -> begin
((dd - (Support.Microsoft.FStar.Util.int_of_char 'A')) + 10)
end
| false -> begin
(failwith ("hexdigit"))
end)
end)
end)))

let unicodegraph_short = (fun ( s ) -> (match (((Support.String.length s) <> 4)) with
| true -> begin
(failwith ("unicodegraph"))
end
| false -> begin
(let _68_20112 = (((let _68_20108 = (Support.Microsoft.FStar.Util.char_at s 0)
in (hexdigit _68_20108)) * 4096) + (((let _68_20109 = (Support.Microsoft.FStar.Util.char_at s 1)
in (hexdigit _68_20109)) * 256) + (((let _68_20110 = (Support.Microsoft.FStar.Util.char_at s 2)
in (hexdigit _68_20110)) * 16) + (let _68_20111 = (Support.Microsoft.FStar.Util.char_at s 3)
in (hexdigit _68_20111)))))
in (Support.Microsoft.FStar.Util.uint16_of_int _68_20112))
end))

let hexgraph_short = (fun ( s ) -> (match (((Support.String.length s) <> 2)) with
| true -> begin
(failwith ("hexgraph"))
end
| false -> begin
(let _68_20117 = (((let _68_20115 = (Support.Microsoft.FStar.Util.char_at s 0)
in (hexdigit _68_20115)) * 16) + (let _68_20116 = (Support.Microsoft.FStar.Util.char_at s 1)
in (hexdigit _68_20116)))
in (Support.Microsoft.FStar.Util.uint16_of_int _68_20117))
end))

let unicodegraph_long = (fun ( s ) -> (match (((Support.String.length s) <> 8)) with
| true -> begin
(failwith ("unicodegraph_long"))
end
| false -> begin
(let high = (((let _68_20120 = (Support.Microsoft.FStar.Util.char_at s 0)
in (hexdigit _68_20120)) * 4096) + (((let _68_20121 = (Support.Microsoft.FStar.Util.char_at s 1)
in (hexdigit _68_20121)) * 256) + (((let _68_20122 = (Support.Microsoft.FStar.Util.char_at s 2)
in (hexdigit _68_20122)) * 16) + (let _68_20123 = (Support.Microsoft.FStar.Util.char_at s 3)
in (hexdigit _68_20123)))))
in (let low = (((let _68_20124 = (Support.Microsoft.FStar.Util.char_at s 4)
in (hexdigit _68_20124)) * 4096) + (((let _68_20125 = (Support.Microsoft.FStar.Util.char_at s 5)
in (hexdigit _68_20125)) * 256) + (((let _68_20126 = (Support.Microsoft.FStar.Util.char_at s 6)
in (hexdigit _68_20126)) * 16) + (let _68_20127 = (Support.Microsoft.FStar.Util.char_at s 7)
in (hexdigit _68_20127)))))
in (match ((high = 0)) with
| true -> begin
(None, (Support.Microsoft.FStar.Util.uint16_of_int low))
end
| false -> begin
(Some ((Support.Microsoft.FStar.Util.uint16_of_int (55296 + (((high * 65536) + (low - 65536)) / 1024)))), (Support.Microsoft.FStar.Util.uint16_of_int (57136 + (((high * 65536) + (low - 65536)) mod 1024))))
end)))
end))

let escape = (fun ( c ) -> (match (c) with
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

let is_ALWAYS = (fun ( _discr_ ) -> (match (_discr_) with
| ALWAYS -> begin
true
end
| _ -> begin
false
end))

let is_FSHARP = (fun ( _discr_ ) -> (match (_discr_) with
| FSHARP -> begin
true
end
| _ -> begin
false
end))

let keywords = (let _68_20133 = (Support.List.map (fun ( s ) -> (FSHARP, s, Microsoft_FStar_Parser_Parse.RESERVED)) (("atomic")::("break")::("checked")::("component")::("constraint")::("constructor")::("continue")::("eager")::("fixed")::("functor")::("global")::("include")::("mixin")::("parallel")::("process")::("protected")::("pure")::("sealed")::("trait")::("tailcall")::("volatile")::[]))
in (Support.List.append (((ALWAYS, "and", Microsoft_FStar_Parser_Parse.AND))::((ALWAYS, "as", Microsoft_FStar_Parser_Parse.AS))::((ALWAYS, "assert", Microsoft_FStar_Parser_Parse.ASSERT))::((ALWAYS, "assume", Microsoft_FStar_Parser_Parse.ASSUME))::((ALWAYS, "begin", Microsoft_FStar_Parser_Parse.BEGIN))::((FSHARP, "default", Microsoft_FStar_Parser_Parse.DEFAULT))::((ALWAYS, "effect", Microsoft_FStar_Parser_Parse.EFFECT))::((ALWAYS, "else", Microsoft_FStar_Parser_Parse.ELSE))::((ALWAYS, "end", Microsoft_FStar_Parser_Parse.END))::((ALWAYS, "ensures", Microsoft_FStar_Parser_Parse.ENSURES))::((ALWAYS, "exception", Microsoft_FStar_Parser_Parse.EXCEPTION))::((ALWAYS, "exists", Microsoft_FStar_Parser_Parse.EXISTS))::((ALWAYS, "false", Microsoft_FStar_Parser_Parse.FALSE))::((ALWAYS, "finally", Microsoft_FStar_Parser_Parse.FINALLY))::((ALWAYS, "for", Microsoft_FStar_Parser_Parse.FOR))::((ALWAYS, "forall", Microsoft_FStar_Parser_Parse.FORALL))::((ALWAYS, "fun", Microsoft_FStar_Parser_Parse.FUN))::((ALWAYS, "function", Microsoft_FStar_Parser_Parse.FUNCTION))::((ALWAYS, "if", Microsoft_FStar_Parser_Parse.IF))::((ALWAYS, "in", Microsoft_FStar_Parser_Parse.IN))::((ALWAYS, "lazy", Microsoft_FStar_Parser_Parse.LAZY))::((ALWAYS, "let", Microsoft_FStar_Parser_Parse.LET (false)))::((ALWAYS, "logic", Microsoft_FStar_Parser_Parse.LOGIC))::((ALWAYS, "match", Microsoft_FStar_Parser_Parse.MATCH))::((ALWAYS, "module", Microsoft_FStar_Parser_Parse.MODULE))::((ALWAYS, "of", Microsoft_FStar_Parser_Parse.OF))::((ALWAYS, "open", Microsoft_FStar_Parser_Parse.OPEN))::((ALWAYS, "or", Microsoft_FStar_Parser_Parse.OR))::((ALWAYS, "opaque", Microsoft_FStar_Parser_Parse.OPAQUE))::((ALWAYS, "private", Microsoft_FStar_Parser_Parse.PRIVATE))::((FSHARP, "public", Microsoft_FStar_Parser_Parse.PUBLIC))::((ALWAYS, "rec", Microsoft_FStar_Parser_Parse.REC))::((ALWAYS, "requires", Microsoft_FStar_Parser_Parse.REQUIRES))::((ALWAYS, "then", Microsoft_FStar_Parser_Parse.THEN))::((ALWAYS, "to", Microsoft_FStar_Parser_Parse.TO))::((ALWAYS, "true", Microsoft_FStar_Parser_Parse.TRUE))::((ALWAYS, "try", Microsoft_FStar_Parser_Parse.TRY))::((ALWAYS, "type", Microsoft_FStar_Parser_Parse.TYPE))::((ALWAYS, "val", Microsoft_FStar_Parser_Parse.VAL))::((ALWAYS, "when", Microsoft_FStar_Parser_Parse.WHEN))::((ALWAYS, "with", Microsoft_FStar_Parser_Parse.WITH))::((ALWAYS, "new_effect", Microsoft_FStar_Parser_Parse.NEW_EFFECT))::((ALWAYS, "sub_effect", Microsoft_FStar_Parser_Parse.SUB_EFFECT))::((ALWAYS, "total", Microsoft_FStar_Parser_Parse.TOTAL))::((ALWAYS, "kind", Microsoft_FStar_Parser_Parse.KIND))::((ALWAYS, "_", Microsoft_FStar_Parser_Parse.UNDERSCORE))::[]) _68_20133))

let stringKeywords = (Support.List.map (fun ( _43_62 ) -> (match (_43_62) with
| (_, w, _) -> begin
w
end)) keywords)

let unreserve_words = (Support.List.choose (fun ( _43_67 ) -> (match (_43_67) with
| (mode, keyword, _) -> begin
(match ((mode = FSHARP)) with
| true -> begin
Some (keyword)
end
| false -> begin
None
end)
end)) keywords)

let kwd_table = (let tab = (Support.Microsoft.FStar.Util.smap_create 1000)
in (let _43_73 = (Support.List.iter (fun ( _43_72 ) -> (match (_43_72) with
| (mode, keyword, token) -> begin
(Support.Microsoft.FStar.Util.smap_add tab keyword token)
end)) keywords)
in tab))

let kwd = (fun ( s ) -> (Support.Microsoft.FStar.Util.smap_try_find kwd_table s))

exception ReservedKeyword of ((string * Support.Microsoft.FStar.Range.range))

let is_ReservedKeyword = (fun ( _discr_ ) -> (match (_discr_) with
| ReservedKeyword (_) -> begin
true
end
| _ -> begin
false
end))

exception IndentationProblem of ((string * Support.Microsoft.FStar.Range.range))

let is_IndentationProblem = (fun ( _discr_ ) -> (match (_discr_) with
| IndentationProblem (_) -> begin
true
end
| _ -> begin
false
end))

type lexargs =
{getSourceDirectory : unit  ->  string; contents : string}

let is_Mklexargs = (fun ( _ ) -> (failwith ("Not yet implemented")))

let mkLexargs = (fun ( _43_84 ) -> (match (_43_84) with
| (srcdir, filename, contents) -> begin
{getSourceDirectory = srcdir; contents = contents}
end))

let kwd_or_id = (fun ( args ) ( r ) ( s ) -> (match ((kwd s)) with
| Some (v) -> begin
(match ((v = Microsoft_FStar_Parser_Parse.RESERVED)) with
| true -> begin
(let _43_90 = (let _68_20172 = (let _68_20171 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "The keyword \'%s\' is reserved for future use by F#. (%s)" s _68_20171))
in (Support.Microsoft.FStar.Util.print_string _68_20172))
in (let _68_20173 = (intern_string s)
in Microsoft_FStar_Parser_Parse.IDENT (_68_20173)))
end
| false -> begin
v
end)
end
| None -> begin
(match (s) with
| "__SOURCE_DIRECTORY__" -> begin
(let _68_20175 = (let _68_20174 = (args.getSourceDirectory ())
in (Support.Microsoft.FStar.Bytes.string_as_unicode_bytes _68_20174))
in Microsoft_FStar_Parser_Parse.STRING (_68_20175))
end
| "__SOURCE_FILE__" -> begin
(let _68_20177 = (let _68_20176 = (Support.Microsoft.FStar.Range.file_of_range r)
in (Support.Microsoft.FStar.Bytes.string_as_unicode_bytes _68_20176))
in Microsoft_FStar_Parser_Parse.STRING (_68_20177))
end
| "__LINE__" -> begin
(let _68_20181 = (let _68_20180 = (let _68_20179 = (let _68_20178 = (Support.Microsoft.FStar.Range.start_of_range r)
in (Support.Microsoft.FStar.Range.line_of_pos _68_20178))
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int _68_20179))
in (_68_20180, false))
in Microsoft_FStar_Parser_Parse.INT (_68_20181))
end
| _ -> begin
(let _68_20182 = (intern_string s)
in Microsoft_FStar_Parser_Parse.IDENT (_68_20182))
end)
end))




