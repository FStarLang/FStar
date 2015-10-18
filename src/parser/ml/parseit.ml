open FStar_Util
open FStar_Absyn_Syntax
open Lexing

let resetLexbufPos filename lexbuf =
  lexbuf.lex_curr_p <- {
    pos_fname= FStar_Range.encode_file filename;
    pos_cnum = 0; pos_bol = 0;
    pos_lnum=1 }

let bc_start = "(*--build-config"
let bc_end   = "--*)"

let get_bc_start_string (_:unit) = bc_start

module Path = BatPathGen.OfString

let find_file (filename:string) =
  if Path.is_relative (Path.of_string filename) then
    let include_path = FStar_Options.get_include_path () in
    let f = find_map include_path (fun p ->
      let p = p ^ "/" ^ filename in
      if Sys.file_exists p then Some p else None) in
    try
      match f with
        | None -> raise (Err "")
        | Some f -> f
    with e -> raise (Err (FStar_Util.format1 "Unable to open file: %s\n" filename))
  else filename

let open_file (filename:string) =
  let f = find_file filename in
  try
    BatFile.with_file_in f BatIO.read_all
  with e -> raise (Err (FStar_Util.format1 "Unable to open file: %s\n" filename))

let read_build_config_from_string (filename:string) (use_filename:bool) (contents:string)  =
    let fail msg = raise (Err(FStar_Util.format2 "Could not parse a valid build configuration from %s; %s\n" filename msg)) in
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
    let substitute_variables (f:string) = !variables |> FStar_List.fold_left
      (fun (f:string) (x,v) -> BatString.replace f ("$"^x) v |> snd) f in
    if FStar_Util.starts_with contents bc_start
    then
        let bc_end_index = BatString.find contents bc_end in
        let bc = FStar_Util.substring contents (String.length bc_start) (bc_end_index - (String.length bc_start)) in
        let fields = FStar_Util.split bc ";" in
        fields |> FStar_List.iter (fun field ->
        let field = FStar_Util.trim_string field in
        if field = "" then ()
        else
          let nv = FStar_Util.split field ":" in
          if FStar_List.length nv <> 2
          then fail ("could not parse field: " ^ field)
          else let [name; value] = nv in
               match name with
                  | "options" -> set_options value
                  | "other-files" ->
                     set_filenames (FStar_Util.split value " "
                                    |> FStar_List.map
                                         (fun x ->
                                          let x = FStar_Util.trim_string x in
                                          if String.length x = 0
                                          then []
                                          else [x])
                                   |> FStar_List.flatten)
                  | "variables" ->
                    let vars = FStar_Util.split value " " in
                    vars |> FStar_List.iter (fun v ->
                      let v = FStar_Util.trim_string v in
                      if String.length v = 0
                      then ()
                      else
                        let xv = FStar_Util.split v "=" in
                        if FStar_List.length xv <> 2
                        then fail (FStar_Util.format1 "could not parse variable:<%s>"  v)
                        else let [x;v] = xv in
                             set_variable (FStar_Util.trim_string x, FStar_Util.trim_string v))
                  | _ -> fail ("unexpected config option: " ^ name));

        begin match !options with
            | None -> ()
            | Some v ->
              begin match FStar_Options.set_options v with
                    | FStar_Getopt.GoOn ->
                      FStar_Options.reset_options_string := Some v
                    | FStar_Getopt.Help  -> fail ("Invalid options: " ^ v)
                    | FStar_Getopt.Die s -> fail ("Invalid options : " ^ s)
              end
        end;
        match !filenames with
            | None -> if use_filename then [filename] else []
            | Some other_files ->
	      let files = if use_filename then other_files@[filename] else other_files
	      in
              FStar_List.map substitute_variables files
    else if !FStar_Options.use_build_config (* the user claimed that the build config exists *)
    then fail ""
    else (let stdlib = ["FStar.Set"; "FStar.Heap"; "FStar.ST"; "FStar.All"; "FStar.IO"] in
          let admit_string = FStar_List.map (fun x -> "--admit_fsi " ^ x) stdlib in
          let admit_string = FStar_String.concat " " admit_string in
	  let common_files = ["set.fsi"; "heap.fst"; "st.fst"; "all.fst"; "io.fsti"] in
	  let files = if use_filename then common_files@[filename] else common_files
	  in
          FStar_Options.admit_fsi := stdlib @ (!FStar_Options.admit_fsi);
          let _ = match !FStar_Options.reset_options_string with 
            | None -> FStar_Options.reset_options_string := Some admit_string
            | Some x -> FStar_Options.reset_options_string := Some (admit_string ^ " " ^ x) in
          files)

let read_build_config (filename:string) =
    let contents = open_file filename in
    read_build_config_from_string filename true contents

let parse fn =
  FStar_Parser_Util.warningHandler := (function
    | FStar_Parser_Lexhelp.ReservedKeyword(m,s) -> Printf.printf "%s:%s" (FStar_Range.string_of_range s) m
    | e -> Printf.printf "There was some warning (TODO)\n");

  let filename,lexbuf = match fn with
    | Inl(f) ->
       (try f, Lexing.from_channel (open_in (find_file f))
        with _ -> raise (Err(FStar_Util.format1 "Unable to open file: %s\n" f)))
    | Inr(s) ->
      "<input>", Lexing.from_string s in

  resetLexbufPos filename lexbuf;
  let lexer = FStar_Parser_LexFStar.token in
  try
      let fileOrFragment = FStar_Parser_Parse.inputFragment lexer lexbuf in
      let frags = match fileOrFragment with
          | Inl mods ->
             if FStar_Util.ends_with filename ".fsi" || FStar_Util.ends_with filename ".fsti"
             then Inl (mods |> FStar_List.map (function
                  | FStar_Parser_AST.Module(l,d) ->
                    FStar_Parser_AST.Interface(l, d, FStar_Util.for_some (fun m -> m=l.str) !FStar_Options.admit_fsi)
                  | _ -> failwith "Impossible"))
             else Inl mods
          | _ -> fileOrFragment in
      Inl frags
  with
    | FStar_Absyn_Syntax.Error(msg, r) ->
      Inr (msg, r)

    | e ->
      let pos = lexbuf.lex_curr_p in
      let p = FStar_Range.mk_pos pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) in
      let r = FStar_Range.mk_range filename p p in
      Inr ("Syntax error: " ^ (Printexc.to_string e), r)
