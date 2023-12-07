let noshort = 0
type 'a opt_variant =
  | ZeroArgs of (unit -> 'a)
  | OneArg of (string -> 'a) * string
type 'a opt' = FStar_Char.char * string * 'a opt_variant
type opt = unit opt'
type parse_cmdline_res =
  | Empty
  | Help
  | Error of string
  | Success

let bind l f =
    match l with
    | Help
    | Error _ -> l
    | Success -> f ()
    (* | Empty  *)
    (* ^ Empty does not occur internally. *)

(* Returns None if this wasn't an option arg (did not start with "-")
 * Otherwise, returns Some (o, s) where [s] is the trimmed option, and [o]
 * is the opt we found in specs (possibly None if not present, which should
 * trigger an error) *)
let find_matching_opt specs s : (opt option * string) option =
  if String.length s < 2 then
    None
  else if String.sub s 0 2 = "--" then
    (* long opts *)
    let strim = String.sub s 2 ((String.length s) - 2) in
    let o = FStar_List.tryFind (fun (_, option, _) -> option = strim) specs in
    Some (o, strim)
  else if String.sub s 0 1 = "-" then
    (* short opts *)
    let strim = String.sub s 1 ((String.length s) - 1) in
    let o = FStar_List.tryFind (fun (shortoption, _, _) -> FStar_String.make Z.one shortoption = strim) specs in
    Some (o, strim)
  else
    None

(* remark: doesn't work with files starting with -- *)
let rec parse (opts:opt list) def ar ix max i : parse_cmdline_res =
  if ix > max then Success
  else
    let arg = ar.(ix) in
    let go_on () = bind (def arg) (fun _ -> parse opts def ar (ix + 1) max (i + 1)) in
    match find_matching_opt opts arg with
    | None -> go_on ()
    | Some (None, _) -> Error ("unrecognized option '" ^ arg ^ "'\n")
    | Some (Some (_, _, p), argtrim) ->
      begin match p with
      | ZeroArgs f -> f (); parse opts def ar (ix + 1) max (i + 1)
      | OneArg (f, _) ->
         if ix + 1 > max
         then Error ("last option '" ^ argtrim ^ "' takes an argument but has none\n")
         else
           let r =
               try (f (ar.(ix + 1)); Success)
               with _ -> Error ("wrong argument given to option `" ^ argtrim ^ "`\n")
           in bind r (fun () -> parse opts def ar (ix + 2) max (i + 1))
      end

let parse_array specs others args offset =
  parse specs others args offset (Array.length args - 1) 0

let parse_cmdline specs others =
  if Array.length Sys.argv = 1 then Empty
  else parse_array specs others Sys.argv 1

let parse_string specs others (str:string) =
    let split_spaces (str:string) =
      let seps = [int_of_char ' '; int_of_char '\t'] in
      FStar_List.filter (fun s -> s != "") (FStar_String.split seps str)
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
      parse_array specs others (Array.of_list args) 0

let parse_list specs others lst =
  parse_array specs others (Array.of_list lst) 0

let cmdline () =
   Array.to_list (Sys.argv)
