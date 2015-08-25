(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"
module FStar.Parser.ParseIt
open FStar
open FStar.Util

let resetLexbufPos filename (lexbuf: Microsoft.FSharp.Text.Lexing.LexBuffer<char>) =
  lexbuf.EndPos <- {lexbuf.EndPos with
    pos_fname= Range.encode_file filename;
    pos_cnum=0;
    pos_lnum=1 }

let bc_start = "(*--build-config"
let bc_end   = "--*)"
let open_file (filename:string) =
    let include_path = Options.get_include_path() in
    try 
        let p = Util.find_map include_path (fun p -> 
                let path = System.IO.Path.Combine(p, filename) in
                if System.IO.File.Exists(path)
                then Some path
                else None) in
        match p with 
        | Some f -> 
            if !Options.debug <> []
            then Util.fprint1 "Opening file: %s\n" f;
            new System.IO.StreamReader(f) 
        | _ -> raise (Absyn.Syntax.Err("unable to open file")) 
    with e -> raise (Absyn.Syntax.Err (Util.format2 "Unable to open file: %s\n%s\n" filename (e.ToString())))


let read_build_config (filename:string) =
    let fail msg = raise (Absyn.Syntax.Err(Util.format2 "Could not parse a valid build configuration from %s; %s" filename msg)) in
    let options = ref None in
    let filenames = ref None in 
    let variables = ref [] in 
    let set_options v = match !options with 
        | None -> options := Some v 
        | _ -> fail "more than one 'options' field" in
    let set_filenames v = match !filenames with 
        | None -> filenames := Some v
        | _ -> fail "more than one 'other-files' field" in
    let set_variable (x, v) = variables := (x,v)::!variables in
    let substitute_variables (f:string) = !variables |> List.fold_left (fun (f:string) (x,v) -> f.Replace("$"^x, v)) f  in
    let fs = open_file filename in
    let contents = fs.ReadToEnd() in
    if contents.StartsWith(bc_start)
    then 
        let bc_end_index = contents.IndexOf(bc_end) in
        let bc = contents.Substring(bc_start.Length, bc_end_index - bc_start.Length) in
        let fields = bc.Split([|';'|]) in
        fields |> Array.iter (fun field -> 
        let field = field.Trim() in
        if field = "" then ()
        else
            let nv = field.Split([|':'|]) in
            if nv.Length <> 2 
            then fail ("could not parse field: " ^ field)
            else let name, value = nv.(0), nv.(1) in
                 match name with 
                    | "options" -> set_options value
                    | "other-files" -> 
                        set_filenames (Util.split value " " 
                                        |> List.collect 
                                            (fun x ->
                                            let x = Util.trim_string x in
                                            if String.length x = 0
                                            then []
                                            else [x]))
                    | "variables" -> 
                      let vars = value.Split([|' '|]) in 
                      vars |> Array.iter (fun v -> 
                        let v = Util.trim_string v in
                        if String.length v = 0
                        then ()
                        else let xv = v.Split([|'='|]) in
                             if xv.Length <> 2
                             then fail ("could not parse variable: " ^ v)
                             else set_variable (xv.(0).Trim(), xv.(1).Trim()))
                    | _ -> fail ("unexpected config option: " ^ name));

        begin match !options with 
            | None -> ()
            | Some v -> 
              begin match Options.set_options v with 
                    | Getopt.GoOn ->
                      Options.reset_options_string := Some v
                    | Getopt.Help  -> fail ("Invalid options: " ^ v)
                    | Getopt.Die s -> fail ("Invalid options : " ^ s)
              end 
        end;
        match !filenames with 
            | None ->  [filename]
            | Some other_files -> 
              let files = List.map substitute_variables other_files@[filename] in
              files
    else if !Options.use_build_config //the user claimed that the build config exists
    then fail ""
    else (Options.admit_fsi := "Set"::!Options.admit_fsi;
          ["set.fsi"; "heap.fst"; "st.fst"; "all.fst"; filename])

let parse fn =
  Parser.Util.warningHandler := (function
    | Lexhelp.ReservedKeyword(m,s) -> Printf.printf "%s:%s" (Range.string_of_range s) m
    | e -> Printf.printf "Warning: %A\n" e);

  Parser.Util.errorHandler := (function
    | e -> raise e);

  let filename,sr,fs = match fn with
    | Inl (filename:string) ->
      let fs = open_file filename in
      let contents = fs.ReadToEnd() in
      filename, new System.IO.StringReader(contents) :> System.IO.TextReader, contents      
    | Inr (s:string) -> "<input>", new System.IO.StringReader(s) :> System.IO.TextReader, s  in

  let lexbuf = Microsoft.FSharp.Text.Lexing.LexBuffer<char>.FromTextReader(sr) in
  resetLexbufPos filename lexbuf;
  let lexargs = Lexhelp.mkLexargs ((fun () -> "."), filename,fs) in
  let lexer = LexFStar.token lexargs in
  try
    let fileOrFragment = Parse.inputFragment lexer lexbuf in
    let frags = match fileOrFragment with 
        | Inl mods -> 
           if Util.ends_with filename ".fsi" || Util.ends_with filename ".fsti"
           then Inl (mods |> List.map (function
                | AST.Module(l,d) ->
                  AST.Interface(l, d, Util.for_some (fun m -> m=l.str) !Options.admit_fsi)
                | _ -> failwith "Impossible"))
           else Inl mods
        | _ -> fileOrFragment in
    Inl frags
  with
    | Absyn.Syntax.Error(msg, r) ->
      Inr (msg, r)
    | e ->
      let pos = lexbuf.EndPos in
      let p = Range.mk_pos pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) in
      let r = Range.mk_range filename p p in
      Inr ("Syntax error", r)
