#light "off"

module FStar.Extraction.ML.PrintML

open FStar.Extraction.ML.Syntax
open FStar.Extraction.ML.Code

let print (_: option<string>) (ext: string) (l: mllib) =
    let newDoc = FStar.Extraction.ML.Code.doc_of_mllib l in
    List.iter (fun (n,d) ->
        FStar.Util.write_file (FStar.Options.prepend_output_dir (n^ext)) (FStar.Extraction.ML.Code.pretty 120 d)) newDoc