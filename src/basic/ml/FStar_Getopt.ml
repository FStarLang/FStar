let noshort = 0
type 'a opt_variant =
  | ZeroArgs of (unit -> 'a)
  | OneArg of (string -> 'a) * string
type 'a opt' = FStar_Char.char * string * 'a opt_variant * string
type opt = unit opt'
type parse_cmdline_res =
  | Help
  | Error of string
  | Success

let bind l f =
    match l with
    | Help
    | Error _ -> l
    | Success -> f ()

(* remark: doesn't work with files starting with -- *)
let rec parse (opts:opt list) def ar ix max i =
  if ix > max then Success
  else
    let arg = ar.(ix) in
    let go_on () = let _ = def arg in parse opts def ar (ix + 1) max (i + 1) in
    if String.length arg < 2 then
      go_on ()
    else
      let hd = String.sub arg 0 2 in
      if hd = "--" then
        let argtrim = String.sub arg 2 ((String.length arg) - 2) in
        match FStar_List.tryFind (fun (_, option, _, _) -> option = argtrim) opts with
        | Some (_, _, p, _) ->
           (match p with
            | ZeroArgs f -> f (); parse opts def ar (ix + 1) max (i + 1)
            | OneArg (f, _) ->
               if ix + 1 > max
               then Error ("last option '" ^ argtrim ^ "' takes an argument but has none\n")
               else
                 let r =
                     try (f (ar.(ix + 1)); Success)
                     with _ -> Error ("wrong argument given to option `" ^ argtrim ^ "`\n")
                 in bind r (fun () -> parse opts def ar (ix + 2) max (i + 1)))
        | None -> Error ("unrecognized option '" ^ arg ^ "'\n")
      else go_on ()

let parse_cmdline specs others =
  let len = Array.length Sys.argv in
  let go_on () = parse specs others Sys.argv 1 (len - 1) 0 in
  if len = 1 then Help
  else go_on ()

let parse_string specs others (str:string) =
    let split_spaces (str:string) =
        Str.split (Str.regexp "[ \t]+") str
    in
    (* to match the style of the F# code in FStar.GetOpt.fs *)
    let index_of str c =
      try
        String.index str c
      with Not_found -> -1
    in
    let substring_from s j =
        let len = String.length s - j in
        String.sub s j len
    in
    let rec split_quoted_fragments (str:string) =
        let i = index_of str '\'' in
        if i < 0 then Some (split_spaces str)
        else let prefix = String.sub str 0 i in
             let suffix = substring_from str (i + 1) in
             let j = index_of suffix '\'' in
             if j < 0 then None
             else let quoted_frag = String.sub suffix 0 j in
                  let rest = split_quoted_fragments (substring_from suffix (j + 1)) in
                  match rest with
                  | None -> None
                  | Some rest -> Some (split_spaces prefix @ quoted_frag::rest)

    in
    match split_quoted_fragments str with
    | None -> Error("Failed to parse options; unmatched quote \"'\"")
    | Some args ->
      let args = Array.of_list args in
      parse specs others args 0 (Array.length args - 1) 0
