open Microsoft_FStar_Util
open Microsoft_FStar_Absyn_Syntax
open Lexing

let resetLexbufPos filename lexbuf =
  lexbuf.lex_curr_p <- {
    pos_fname= Microsoft_FStar_Range.encode_file filename;
    pos_cnum = 0; pos_bol = 0;
    pos_lnum=1 }

let bc_start = "(*--build-config"
let bc_end   = "--*)"

let find_file (filename:string) =
  let include_path = Microsoft_FStar_Options.get_include_path () in
  let f = find_map include_path (fun p ->
    let p = p ^ "/" ^ filename in
    if Sys.file_exists p then Some p else None) in
  try
    match f with
      | None -> raise (Err "")
      | Some f -> f
  with e -> raise (Err (Microsoft_FStar_Util.format1 "Unable to open file: %s\n" filename))

let open_file (filename:string) =
  let f = find_file filename in
  try
    BatFile.with_file_in f BatIO.read_all
  with e -> raise (Err (Microsoft_FStar_Util.format1 "Unable to open file: %s\n" filename))

let read_build_config (filename:string) =
    let fail msg = raise (Err(Microsoft_FStar_Util.format2 "Could not parse a valid build configuration from %s; %s" filename msg)) in
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
    let substitute_variables (f:string) = !variables |> Microsoft_FStar_List.fold_left
      (fun (f:string) (x,v) -> BatString.replace f ("$"^x) v |> snd) f in
    let contents = open_file filename in
    if Microsoft_FStar_Util.starts_with contents bc_start
    then
        let bc_end_index = BatString.find contents bc_end in
        let bc = Microsoft_FStar_Util.substring contents (String.length bc_start) (bc_end_index - (String.length bc_start)) in
        let fields = Microsoft_FStar_Util.split bc ";" in
        fields |> Microsoft_FStar_List.iter (fun field ->
        let field = Microsoft_FStar_Util.trim_string field in
        if field = "" then ()
        else
          let nv = Microsoft_FStar_Util.split field ":" in
          if Microsoft_FStar_List.length nv <> 2
          then fail ("could not parse field: " ^ field)
          else let [name; value] = nv in
               match name with
                  | "options" -> set_options value
                  | "other-files" ->
                     set_filenames (Microsoft_FStar_Util.split value " "
                                    |> Microsoft_FStar_List.map
                                         (fun x ->
                                          let x = Microsoft_FStar_Util.trim_string x in
                                          if String.length x = 0
                                          then []
                                          else [x])
                                   |> Microsoft_FStar_List.flatten)
                  | "variables" ->
                    let vars = Microsoft_FStar_Util.split value " " in
                    vars |> Microsoft_FStar_List.iter (fun v ->
                      let v = Microsoft_FStar_Util.trim_string v in
                      if String.length v = 0
                      then ()
                      else
                        let xv = Microsoft_FStar_Util.split v "=" in
                        if Microsoft_FStar_List.length xv <> 2
                        then fail (Microsoft_FStar_Util.format1 "could not parse variable:<%s>"  v)
                        else let [x;v] = xv in
                             set_variable (Microsoft_FStar_Util.trim_string x, Microsoft_FStar_Util.trim_string v))
                  | _ -> fail ("unexpected config option: " ^ name));

        begin match !options with
            | None -> ()
            | Some v ->
              begin match Microsoft_FStar_Options.set_options v with
                    | Microsoft_FStar_Getopt.GoOn ->
                      Microsoft_FStar_Options.reset_options_string := Some v
                    | Microsoft_FStar_Getopt.Help  -> fail ("Invalid options: " ^ v)
                    | Microsoft_FStar_Getopt.Die s -> fail ("Invalid options : " ^ s)
              end
        end;
        match !filenames with
            | None ->  [filename]
            | Some other_files ->
              let files = Microsoft_FStar_List.map substitute_variables other_files@[filename] in
              files
    else if !Microsoft_FStar_Options.use_build_config (* the user claimed that the build config exists *)
    then fail ""
    else (Microsoft_FStar_Options.admit_fsi := "Set"::!Microsoft_FStar_Options.admit_fsi;
          ["set.fsi"; "heap.fst"; "st.fst"; "all.fst"; filename])

let parse fn =
  Microsoft_FStar_Parser_Util.warningHandler := (function
    | Microsoft_FStar_Parser_Lexhelp.ReservedKeyword(m,s) -> Printf.printf "%s:%s" (Microsoft_FStar_Range.string_of_range s) m
    | e -> Printf.printf "There was some warning (TODO)\n");

  let filename,lexbuf = match fn with
    | Inl(f) ->
       (try f, Lexing.from_channel (open_in (find_file f))
        with _ -> raise (Err(Microsoft_FStar_Util.format1 "Unable to open file: %s\n" f)))
    | Inr(s) ->
      "<input>", Lexing.from_string s in

  resetLexbufPos filename lexbuf;
  let lexer = Microsoft_FStar_Parser_LexFStar.token in
  try
      let fileOrFragment = Microsoft_FStar_Parser_Parse.inputFragment lexer lexbuf in
      let frags = match fileOrFragment with
          | Inl mods ->
             if Microsoft_FStar_Util.ends_with filename ".fsi" || Microsoft_FStar_Util.ends_with filename ".fsti"
             then Inl (mods |> Microsoft_FStar_List.map (function
                  | Microsoft_FStar_Parser_AST.Module(l,d) ->
                    Microsoft_FStar_Parser_AST.Interface(l, d, Microsoft_FStar_Util.for_some (fun m -> m=l.str) !Microsoft_FStar_Options.admit_fsi)
                  | _ -> failwith "Impossible"))
             else Inl mods
          | _ -> fileOrFragment in
      Inl frags
  with
    | Microsoft_FStar_Absyn_Syntax.Error(msg, r) ->
      Inr (msg, r)

    | e ->
      let pos = lexbuf.lex_curr_p in
      let p = Microsoft_FStar_Range.mk_pos pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) in
      let r = Microsoft_FStar_Range.mk_range filename p p in
      Inr ("Syntax error: " ^ (Printexc.to_string e), r)
