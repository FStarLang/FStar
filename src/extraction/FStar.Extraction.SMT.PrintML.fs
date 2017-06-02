#light "off"

module FStar.Extraction.SMT.PrintML

open FStar.Extraction.ML.Syntax

let print (_: option<string>) (ext: string) (l: mllib) = 
    let newDoc = FStar.Extraction.SMT.Code.doc_of_mllib l in
    List.iter (fun (n,d) ->
        FStar.Util.write_file (FStar.Options.prepend_output_dir (n^ext)) (FStar.Format.pretty 120 d)) newDoc
