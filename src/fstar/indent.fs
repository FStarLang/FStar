module FStar.Indent

open FStar.Util
open FStar.Parser.ToDocument

module D = FStar.Parser.Driver
module P = FStar.Pprint

let generate filenames =
    let modules = List.collect (fun filename -> D.parse_file filename) filenames in
    List.iter (fun module_ -> P.pretty_out_channel 1.0 100 (modul_to_document module_) stdout) modules
