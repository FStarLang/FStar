module Microsoft.FStar.Parser.ParseIt
open Microsoft.FStar.Parser
open Microsoft.FStar.Util

val parse_file: either<string,string> -> either<AST.file, string>
