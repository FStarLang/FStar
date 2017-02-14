#light "off"

module FStar.Extraction.ML.PrintML

open FStar.Extraction.ML.Syntax

val is_default_printer: bool

val print: option<string> -> string -> mllib -> unit