
let intern_string = (let strings = (Support.Microsoft.FStar.Util.smap_create 100)
in (fun ( s  :  string ) -> (match ((Support.Microsoft.FStar.Util.smap_try_find strings s)) with
| Some (res) -> begin
res
end
| None -> begin
(let _43_6 = (Support.Microsoft.FStar.Util.smap_add strings s s)
in s)
end)))

let default_string_finish = (fun ( endm  :  'u43u138 ) ( b  :  'u43u137 ) ( s  :  Support.Prims.byte array ) -> Microsoft_FStar_Parser_Parse.STRING (s))

let call_string_finish = (fun ( fin  :  'u43u153  ->  'u43u152  ->  Support.Microsoft.FStar.Bytes.bytes  ->  'u43u151 ) ( buf  :  Support.Microsoft.FStar.Bytes.bytebuf ) ( endm  :  'u43u153 ) ( b  :  'u43u152 ) -> (let _52_16765 = (Support.Microsoft.FStar.Bytes.close buf)
in (fin endm b _52_16765)))

let add_string = (fun ( buf  :  Support.Microsoft.FStar.Bytes.bytebuf ) ( x  :  string ) -> (let _52_16770 = (Support.Microsoft.FStar.Bytes.string_as_unicode_bytes x)
in (Support.Microsoft.FStar.Bytes.emit_bytes buf _52_16770)))

let add_int_char = (fun ( buf  :  Support.Microsoft.FStar.Bytes.bytebuf ) ( c  :  int ) -> (let _43_19 = (Support.Microsoft.FStar.Bytes.emit_int_as_byte buf (c mod 256))
in (Support.Microsoft.FStar.Bytes.emit_int_as_byte buf (c / 256))))

let add_unichar = (fun ( buf  :  Support.Microsoft.FStar.Bytes.bytebuf ) ( c  :  int ) -> (add_int_char buf c))

let add_byte_char = (fun ( buf  :  Support.Microsoft.FStar.Bytes.bytebuf ) ( c  :  char ) -> (add_int_char buf ((Support.Microsoft.FStar.Util.int_of_char c) mod 256)))

let stringbuf_as_bytes = (fun ( buf  :  Support.Microsoft.FStar.Bytes.bytebuf ) -> (let bytes = (Support.Microsoft.FStar.Bytes.close buf)
in (let _52_16787 = (let _52_16786 = (Support.Microsoft.FStar.Bytes.length bytes)
in (_52_16786 / 2))
in (Support.Microsoft.FStar.Bytes.make (fun ( i  :  int ) -> (Support.Microsoft.FStar.Bytes.get bytes (i * 2))) _52_16787))))

let stringbuf_is_bytes = (fun ( buf  :  Support.Microsoft.FStar.Bytes.bytebuf ) -> (let bytes = (Support.Microsoft.FStar.Bytes.close buf)
in (let ok = (Support.Microsoft.FStar.Util.mk_ref true)
in (let _43_32 = (let _52_16794 = (let _52_16791 = (let _52_16790 = (Support.Microsoft.FStar.Bytes.length bytes)
in (_52_16790 / 2))
in (_52_16791 - 1))
in (Support.Microsoft.FStar.Util.for_range 0 _52_16794 (fun ( i  :  int ) -> (match ((let _52_16793 = (Support.Microsoft.FStar.Bytes.get bytes ((i * 2) + 1))
in (_52_16793 <> 0))) with
| true -> begin
(Support.ST.op_Colon_Equals ok false)
end
| false -> begin
()
end))))
in (Support.ST.read ok)))))

let trigraph = (fun ( c1  :  char ) ( c2  :  char ) ( c3  :  char ) -> (let digit = (fun ( c  :  char ) -> ((Support.Microsoft.FStar.Util.int_of_char c) - (Support.Microsoft.FStar.Util.int_of_char '0')))
in (Support.Microsoft.FStar.Util.char_of_int (((digit c1) * 100) + (((digit c2) * 10) + (digit c3))))))

let digit = (fun ( d  :  char ) -> (let dd = (Support.Microsoft.FStar.Util.int_of_char d)
in (match (((dd >= (Support.Microsoft.FStar.Util.int_of_char '0')) && (dd <= (Support.Microsoft.FStar.Util.int_of_char '9')))) with
| true -> begin
((Support.Microsoft.FStar.Util.int_of_char d) - (Support.Microsoft.FStar.Util.int_of_char '0'))
end
| false -> begin
(failwith ("digit"))
end)))

let hexdigit = (fun ( d  :  char ) -> (let dd = (Support.Microsoft.FStar.Util.int_of_char d)
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

let unicodegraph_short = (fun ( s  :  string ) -> (match (((Support.String.length s) <> 4)) with
| true -> begin
(failwith ("unicodegraph"))
end
| false -> begin
(let _52_16822 = (let _52_16821 = (let _52_16810 = (let _52_16809 = (Support.Microsoft.FStar.Util.char_at s 0)
in (hexdigit _52_16809))
in (_52_16810 * 4096))
in (let _52_16820 = (let _52_16819 = (let _52_16812 = (let _52_16811 = (Support.Microsoft.FStar.Util.char_at s 1)
in (hexdigit _52_16811))
in (_52_16812 * 256))
in (let _52_16818 = (let _52_16817 = (let _52_16814 = (let _52_16813 = (Support.Microsoft.FStar.Util.char_at s 2)
in (hexdigit _52_16813))
in (_52_16814 * 16))
in (let _52_16816 = (let _52_16815 = (Support.Microsoft.FStar.Util.char_at s 3)
in (hexdigit _52_16815))
in (_52_16817 + _52_16816)))
in (_52_16819 + _52_16818)))
in (_52_16821 + _52_16820)))
in (Support.Microsoft.FStar.Util.uint16_of_int _52_16822))
end))

let hexgraph_short = (fun ( s  :  string ) -> (match (((Support.String.length s) <> 2)) with
| true -> begin
(failwith ("hexgraph"))
end
| false -> begin
(let _52_16830 = (let _52_16829 = (let _52_16826 = (let _52_16825 = (Support.Microsoft.FStar.Util.char_at s 0)
in (hexdigit _52_16825))
in (_52_16826 * 16))
in (let _52_16828 = (let _52_16827 = (Support.Microsoft.FStar.Util.char_at s 1)
in (hexdigit _52_16827))
in (_52_16829 + _52_16828)))
in (Support.Microsoft.FStar.Util.uint16_of_int _52_16830))
end))

let unicodegraph_long = (fun ( s  :  string ) -> (match (((Support.String.length s) <> 8)) with
| true -> begin
(failwith ("unicodegraph_long"))
end
| false -> begin
(let high = (let _52_16845 = (let _52_16834 = (let _52_16833 = (Support.Microsoft.FStar.Util.char_at s 0)
in (hexdigit _52_16833))
in (_52_16834 * 4096))
in (let _52_16844 = (let _52_16843 = (let _52_16836 = (let _52_16835 = (Support.Microsoft.FStar.Util.char_at s 1)
in (hexdigit _52_16835))
in (_52_16836 * 256))
in (let _52_16842 = (let _52_16841 = (let _52_16838 = (let _52_16837 = (Support.Microsoft.FStar.Util.char_at s 2)
in (hexdigit _52_16837))
in (_52_16838 * 16))
in (let _52_16840 = (let _52_16839 = (Support.Microsoft.FStar.Util.char_at s 3)
in (hexdigit _52_16839))
in (_52_16841 + _52_16840)))
in (_52_16843 + _52_16842)))
in (_52_16845 + _52_16844)))
in (let low = (let _52_16858 = (let _52_16847 = (let _52_16846 = (Support.Microsoft.FStar.Util.char_at s 4)
in (hexdigit _52_16846))
in (_52_16847 * 4096))
in (let _52_16857 = (let _52_16856 = (let _52_16849 = (let _52_16848 = (Support.Microsoft.FStar.Util.char_at s 5)
in (hexdigit _52_16848))
in (_52_16849 * 256))
in (let _52_16855 = (let _52_16854 = (let _52_16851 = (let _52_16850 = (Support.Microsoft.FStar.Util.char_at s 6)
in (hexdigit _52_16850))
in (_52_16851 * 16))
in (let _52_16853 = (let _52_16852 = (Support.Microsoft.FStar.Util.char_at s 7)
in (hexdigit _52_16852))
in (_52_16854 + _52_16853)))
in (_52_16856 + _52_16855)))
in (_52_16858 + _52_16857)))
in (match ((high = 0)) with
| true -> begin
(None, (Support.Microsoft.FStar.Util.uint16_of_int low))
end
| false -> begin
(Some ((Support.Microsoft.FStar.Util.uint16_of_int (55296 + (((high * 65536) + (low - 65536)) / 1024)))), (Support.Microsoft.FStar.Util.uint16_of_int (57136 + (((high * 65536) + (low - 65536)) mod 1024))))
end)))
end))

let escape = (fun ( c  :  char ) -> (match (c) with
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

let keywords = (let _52_16864 = (Support.List.map (fun ( s  :  string ) -> (FSHARP, s, Microsoft_FStar_Parser_Parse.RESERVED)) (("atomic")::("break")::("checked")::("component")::("constraint")::("constructor")::("continue")::("eager")::("fixed")::("functor")::("global")::("include")::("mixin")::("parallel")::("process")::("protected")::("pure")::("sealed")::("trait")::("tailcall")::("volatile")::[]))
in (Support.List.append (((ALWAYS, "and", Microsoft_FStar_Parser_Parse.AND))::((ALWAYS, "as", Microsoft_FStar_Parser_Parse.AS))::((ALWAYS, "assert", Microsoft_FStar_Parser_Parse.ASSERT))::((ALWAYS, "assume", Microsoft_FStar_Parser_Parse.ASSUME))::((ALWAYS, "begin", Microsoft_FStar_Parser_Parse.BEGIN))::((FSHARP, "default", Microsoft_FStar_Parser_Parse.DEFAULT))::((ALWAYS, "effect", Microsoft_FStar_Parser_Parse.EFFECT))::((ALWAYS, "else", Microsoft_FStar_Parser_Parse.ELSE))::((ALWAYS, "end", Microsoft_FStar_Parser_Parse.END))::((ALWAYS, "ensures", Microsoft_FStar_Parser_Parse.ENSURES))::((ALWAYS, "exception", Microsoft_FStar_Parser_Parse.EXCEPTION))::((ALWAYS, "exists", Microsoft_FStar_Parser_Parse.EXISTS))::((ALWAYS, "false", Microsoft_FStar_Parser_Parse.FALSE))::((ALWAYS, "finally", Microsoft_FStar_Parser_Parse.FINALLY))::((ALWAYS, "for", Microsoft_FStar_Parser_Parse.FOR))::((ALWAYS, "forall", Microsoft_FStar_Parser_Parse.FORALL))::((ALWAYS, "fun", Microsoft_FStar_Parser_Parse.FUN))::((ALWAYS, "function", Microsoft_FStar_Parser_Parse.FUNCTION))::((ALWAYS, "if", Microsoft_FStar_Parser_Parse.IF))::((ALWAYS, "in", Microsoft_FStar_Parser_Parse.IN))::((ALWAYS, "lazy", Microsoft_FStar_Parser_Parse.LAZY))::((ALWAYS, "let", Microsoft_FStar_Parser_Parse.LET (false)))::((ALWAYS, "logic", Microsoft_FStar_Parser_Parse.LOGIC))::((ALWAYS, "match", Microsoft_FStar_Parser_Parse.MATCH))::((ALWAYS, "module", Microsoft_FStar_Parser_Parse.MODULE))::((ALWAYS, "of", Microsoft_FStar_Parser_Parse.OF))::((ALWAYS, "open", Microsoft_FStar_Parser_Parse.OPEN))::((ALWAYS, "or", Microsoft_FStar_Parser_Parse.OR))::((ALWAYS, "opaque", Microsoft_FStar_Parser_Parse.OPAQUE))::((ALWAYS, "private", Microsoft_FStar_Parser_Parse.PRIVATE))::((FSHARP, "public", Microsoft_FStar_Parser_Parse.PUBLIC))::((ALWAYS, "rec", Microsoft_FStar_Parser_Parse.REC))::((ALWAYS, "requires", Microsoft_FStar_Parser_Parse.REQUIRES))::((ALWAYS, "then", Microsoft_FStar_Parser_Parse.THEN))::((ALWAYS, "to", Microsoft_FStar_Parser_Parse.TO))::((ALWAYS, "true", Microsoft_FStar_Parser_Parse.TRUE))::((ALWAYS, "try", Microsoft_FStar_Parser_Parse.TRY))::((ALWAYS, "type", Microsoft_FStar_Parser_Parse.TYPE))::((ALWAYS, "val", Microsoft_FStar_Parser_Parse.VAL))::((ALWAYS, "when", Microsoft_FStar_Parser_Parse.WHEN))::((ALWAYS, "with", Microsoft_FStar_Parser_Parse.WITH))::((ALWAYS, "new_effect", Microsoft_FStar_Parser_Parse.NEW_EFFECT))::((ALWAYS, "sub_effect", Microsoft_FStar_Parser_Parse.SUB_EFFECT))::((ALWAYS, "total", Microsoft_FStar_Parser_Parse.TOTAL))::((ALWAYS, "kind", Microsoft_FStar_Parser_Parse.KIND))::((ALWAYS, "_", Microsoft_FStar_Parser_Parse.UNDERSCORE))::[]) _52_16864))

let stringKeywords = (Support.List.map (fun ( _43_62  :  (compatibilityMode * string * Microsoft_FStar_Parser_Parse.token) ) -> (match (_43_62) with
| (_, w, _) -> begin
w
end)) keywords)

let unreserve_words = (Support.List.choose (fun ( _43_67  :  (compatibilityMode * string * Microsoft_FStar_Parser_Parse.token) ) -> (match (_43_67) with
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
in (let _43_73 = (Support.List.iter (fun ( _43_72  :  (compatibilityMode * string * Microsoft_FStar_Parser_Parse.token) ) -> (match (_43_72) with
| (mode, keyword, token) -> begin
(Support.Microsoft.FStar.Util.smap_add tab keyword token)
end)) keywords)
in tab))

let kwd = (fun ( s  :  string ) -> (Support.Microsoft.FStar.Util.smap_try_find kwd_table s))

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

let is_Mklexargs = (fun ( _  :  lexargs ) -> (failwith ("Not yet implemented")))

let mkLexargs = (fun ( _43_84  :  ((unit  ->  string) * 'u43u1472 * string) ) -> (match (_43_84) with
| (srcdir, filename, contents) -> begin
{getSourceDirectory = srcdir; contents = contents}
end))

let kwd_or_id = (fun ( args  :  lexargs ) ( r  :  Support.Microsoft.FStar.Range.range ) ( s  :  string ) -> (match ((kwd s)) with
| Some (v) -> begin
(match ((v = Microsoft_FStar_Parser_Parse.RESERVED)) with
| true -> begin
(let _43_90 = (let _52_16903 = (let _52_16902 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "The keyword \'%s\' is reserved for future use by F#. (%s)" s _52_16902))
in (Support.Microsoft.FStar.Util.print_string _52_16903))
in (let _52_16904 = (intern_string s)
in Microsoft_FStar_Parser_Parse.IDENT (_52_16904)))
end
| false -> begin
v
end)
end
| None -> begin
(match (s) with
| "__SOURCE_DIRECTORY__" -> begin
(let _52_16906 = (let _52_16905 = (Microsoft_FStar_Parser_Lexhelp_Mklexargs.getSourceDirectory args ())
in (Support.Microsoft.FStar.Bytes.string_as_unicode_bytes _52_16905))
in Microsoft_FStar_Parser_Parse.STRING (_52_16906))
end
| "__SOURCE_FILE__" -> begin
(let _52_16908 = (let _52_16907 = (Support.Microsoft.FStar.Range.file_of_range r)
in (Support.Microsoft.FStar.Bytes.string_as_unicode_bytes _52_16907))
in Microsoft_FStar_Parser_Parse.STRING (_52_16908))
end
| "__LINE__" -> begin
(let _52_16912 = (let _52_16911 = (let _52_16910 = (let _52_16909 = (Support.Microsoft.FStar.Range.start_of_range r)
in (Support.Microsoft.FStar.Range.line_of_pos _52_16909))
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int _52_16910))
in (_52_16911, false))
in Microsoft_FStar_Parser_Parse.INT (_52_16912))
end
| _ -> begin
(let _52_16913 = (intern_string s)
in Microsoft_FStar_Parser_Parse.IDENT (_52_16913))
end)
end))




