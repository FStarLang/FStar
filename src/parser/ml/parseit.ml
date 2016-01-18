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

let find_file (context:string) (filename:string) : string =
    try
      let result =
        if FStar_Util.is_path_absolute filename then
          if Sys.file_exists filename then
            Some filename
          else
            None
        else
            let cwd = Path.to_string (Path.parent (Path.of_string context)) in
            let search_path = FStar_Options.get_include_path(cwd) in
            find_map 
                search_path 
                    (fun p -> 
                    let path = FStar_Util.join_paths p filename in
                        if Sys.file_exists path then 
                            Some path
                        else 
                            None)
        in
      match result with
        | None -> raise (Err "")
      | Some p -> FStar_Util.normalize_file_path p
    with e -> raise(Err (FStar_Util.format1 "Unable to open file: %s\n" filename))

let read_file (filename:string) =
  try
    BatFile.with_file_in filename BatIO.read_all
  with e -> raise (Err (FStar_Util.format1 "Unable to open file: %s\n" filename))

let rec read_build_config_from_string (filename:string) (use_filename:bool) (contents:string)  (is_root:bool) =
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

        begin 
          if is_root then
            match !options with
              | None -> ()
              | Some v ->
                begin match FStar_Options.set_options v with
                      | FStar_Getopt.GoOn ->
                        FStar_Options.reset_options_string := Some v
                      | FStar_Getopt.Help  -> fail ("Invalid options: " ^ v)
                      | FStar_Getopt.Die s -> fail ("Invalid options : " ^ s)
                end
          else
            ()
        end;
        match !filenames with
            | None -> if use_filename then [filename] else []
            | Some other_files ->
              if not !FStar_Options.auto_deps || filename == "" then
                let files = if use_filename then other_files@[filename] else other_files in
              FStar_List.map substitute_variables files
              else
                (* auto_deps *)
                let included_files =
                  (FStar_List.collect 
                      (fun include_spec ->
                        let found_filen = find_file filename (substitute_variables include_spec) in
                        let contents = read_file found_filen in
                        read_build_config_from_string found_filen true contents false)
                      other_files) in
                let included_files = 
                  if use_filename then
                    included_files@[normalize_file_path filename]
                  else
                    included_files in
                (* the semantics of FStar.List.unique preserve the final occurance of a repeated term, so we need to do a double-reverse
                 * in order to preserve the dependency order. this isn't terribly efficient but this isn't a critical path and fewer code
                 * modifications seems more prudent at the moment. *)
                FStar_List.rev (FStar_List.unique (FStar_List.rev included_files))
    else if !FStar_Options.use_build_config && is_root (* the user claimed that the build config exists *)
    then fail ""
    else (let stdlib = ["FStar.Set"; "FStar.Heap"; "FStar.ST"; "FStar.All"; "FStar.IO"] in
          let admit_string = FStar_List.map (fun x -> "--admit_fsi " ^ x) stdlib in
          let admit_string = FStar_String.concat " " admit_string in
	  let common_files = [(find_file "." "FStar.Set.fsi"); (find_file "." "FStar.Heap.fst"); (find_file "." "FStar.ST.fst"); (find_file "." "FStar.All.fst"); (find_file "." "FStar.IO.fsti")] in
	  let files = if use_filename then common_files@[filename] else common_files
	  in
          FStar_Options.admit_fsi := stdlib @ (!FStar_Options.admit_fsi);
          let _ = match !FStar_Options.reset_options_string with 
            | None -> FStar_Options.reset_options_string := Some admit_string
            | Some x -> FStar_Options.reset_options_string := Some (admit_string ^ " " ^ x) in
          files)

let read_build_config (filename:string) (is_root:bool) =
    let contents = read_file filename in
    read_build_config_from_string filename true contents is_root

let parse fn =
  FStar_Parser_Util.warningHandler := (function
    | FStar_Parser_Lexhelp.ReservedKeyword(m,s) -> Printf.printf "%s:%s" (FStar_Range.string_of_range s) m
    | e -> Printf.printf "There was some warning (TODO)\n");

  let filename,lexbuf = match fn with
    | Inl(f) ->
       let f' = find_file "." f in
       (try f', Lexing.from_channel (open_in f')
        with _ -> raise (Err(FStar_Util.format1 "Unable to open file: %s\n" f')))
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
