open Support.Microsoft.FStar
open Support.Microsoft.FStar.Util
open Microsoft_FStar_Absyn_Syntax
open Lexing

let resetLexbufPos filename lexbuf =
  lexbuf.lex_curr_p <- {
    pos_fname= Range.encode_file filename;
    pos_cnum = 0; pos_bol = 0;
    pos_lnum=1 }
  
let bc_start = "(*--build-config"
let bc_end   = "--*)"

let read_build_config (filename:string) =
    let fail msg = raise (Err(Util.format2 "Could not parse a valid build configuration from %s; %s" filename msg)) in
    let options = ref None in
    let filenames = ref None in 
    let variables = ref [] in 
    let set_options v = match !options with 
        | None -> options := Some v 
        | _ -> fail "more than one 'options' field" in
    let set_filenames v = match !filenames with 
        | None -> filenames := Some v
        | _ -> fail "more than on 'other-files' field" in
    let set_variable (x, v) = variables := (x,v)::!variables in
    let substitute_variables (f:string) = !variables |> List.fold_left 
      (fun (f:string) (x,v) -> BatString.replace f ("$"^x) v |> snd) f in
    let contents = 
        try BatFile.with_file_in filename BatIO.read_all 
        with e -> raise (Err (Util.format1 "Unable to open file: %s\n" filename)) in
    if Util.starts_with contents bc_start
    then 
        let bc_end_index = BatString.find contents bc_end in
        let bc = Util.substring contents (String.length bc_start) (bc_end_index - (String.length bc_start)) in
        let fields = Util.split bc ";" in
        fields |> List.iter (fun field -> 
        let field = Util.trim_string field in
        let nv = Util.split field ":" in
        if List.length nv <> 2 
        then fail ("could not parse field: " ^ field)
        else let [name; value] = nv in
             match name with 
                | "options" -> set_options value
                | "other-files" -> set_filenames (Util.split value " " |> List.map Util.trim_string)
                | "variables" -> 
                  let vars = Util.split value " " in
                  vars |> List.iter (fun v -> 
                    let xv = Util.split v "=" in
                    if List.length xv <> 2
                    then fail ("could not parse variable: " ^ v)
                    else let [x;v] = xv in 
                          set_variable (Util.trim_string x, Util.trim_string v))
                | _ -> fail ("unexpected config option: " ^ name));

        begin match !options with 
            | None -> ()
            | Some v -> 
              begin match Microsoft_FStar_Options.set_options v with 
                    | Support.Microsoft.FStar.Getopt.GoOn -> Microsoft_FStar_Options.reset_options_string := Some v
                    | Support.Microsoft.FStar.Getopt.Help  -> fail ("Invalid options: " ^ v)
                    | Support.Microsoft.FStar.Getopt.Die s -> fail ("Invalid options : " ^ s)
              end 
        end;
        match !filenames with 
            | None ->  [filename]
            | Some other_files -> 
              let files = List.map substitute_variables other_files@[filename] in
              files
    else if !Microsoft_FStar_Options.use_build_config (* the user claimed that the build config exists *)
    then fail ""
    else [filename]

let parse_file fn =
  Parser.Util.warningHandler := (function
    | Microsoft_FStar_Parser_Lexhelp.ReservedKeyword(m,s) -> Printf.printf "%s:%s" (Range.string_of_range s) m
    | e -> Printf.printf "There was some warning (TODO)\n");

  let filename,channel = match fn with
    | Inl(f) -> f,open_in f
    | Inr(s) -> failwith "not supported" in

  let lexbuf = Lexing.from_channel channel in
  resetLexbufPos filename lexbuf;
  let lexer = Microsoft_FStar_Parser_LexFStar.token in
  try
    let file = Microsoft_FStar_Parser_Parse.file lexer lexbuf in
    let mods = if Util.ends_with filename ".fsi"
               then file |> List.map (function
                | Microsoft_FStar_Parser_AST.Module(l,d) ->
                  Microsoft_FStar_Parser_AST.Interface(l,d,Util.for_some (fun m -> m=l.str) (!Microsoft_FStar_Options.admit_fsi))
                | _ -> failwith "Impossible")
               else file in
     Inl mods
  with
    | Microsoft_FStar_Absyn_Syntax.Error(msg, r) ->
      let msg = Util.format2 "ERROR %s: %s\n" (Range.string_of_range r) msg in
      Inr msg
    | e ->
      let pos = lexbuf.lex_curr_p in
      Inr  (Util.format3 "ERROR: Syntax error near line %s, character %s in file %s\n"
              (Util.string_of_int pos.pos_lnum)
              (Util.string_of_int (pos.pos_cnum - pos.pos_bol))
              filename)
