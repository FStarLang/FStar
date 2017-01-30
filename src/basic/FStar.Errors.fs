#light "off"
module FStar.Errors
open FStar.Util
open FStar.Range

exception Err of string
exception Error of string * Range.range
exception Warning of string * Range.range

module BU = FStar.Util

let diag r msg =
  if Options.debug_any()
  then BU.print_string (format2 "%s : (Diagnostic) %s\n" (Range.string_of_range r) msg)

let warn r msg =
  BU.print2_error "%s: (Warning) %s\n" (Range.string_of_range r) msg

let num_errs = BU.mk_ref 0
let verification_errs : ref<list<(Range.range * string)>> = BU.mk_ref []
type error_message_prefix = {
    set_prefix: string -> unit;
    append_prefix: string -> string;
    clear_prefix: unit -> unit;
}
let message_prefix =
    let pfx = BU.mk_ref None in
    let set_prefix s = pfx := Some s in
    let clear_prefix () = pfx := None in
    let append_prefix s = match !pfx with
        | None -> s
        | Some p -> p ^ ": " ^ s in
    {set_prefix=set_prefix;
     clear_prefix=clear_prefix;
     append_prefix=append_prefix}

let add_errors errs =
    let errs =
        errs |> List.map (fun (msg, r) -> r, message_prefix.append_prefix msg) in
    let n_errs = List.length errs in
    atomically (fun () -> verification_errs := errs @ (!verification_errs);
                          num_errs := !num_errs + n_errs)

let mk_error msg r =
    if r.use_range <> r.def_range
    then BU.format3 "%s: (Error) %s (see %s)\n" (Range.string_of_use_range r) msg (Range.string_of_range r)
    else BU.format2 "%s: (Error) %s\n" (Range.string_of_range r) msg

let report_all () =
    let all_errs = atomically (fun () -> let x = !verification_errs in verification_errs := []; x) in
    let all_errs = List.sortWith (fun (r1, _) (r2, _) -> Range.compare_use_range r1 r2) all_errs in
    all_errs |> List.iter (fun (r, msg) -> BU.print_error (mk_error msg r));
    List.length all_errs

let handle_err warning e =
  match e with
    | Error(msg, r) ->
        let msg = message_prefix.append_prefix msg in
        BU.print3_error "%s : %s %s\n" (Range.string_of_range r) (if warning then "(Warning)" else "(Error)") msg
    | NYI msg ->
        let msg = message_prefix.append_prefix msg in
        BU.print1_error "Feature not yet implemented: %s" msg
    | Err msg ->
        let msg = message_prefix.append_prefix msg in
        BU.print1_error "Error: %s" msg
    | _ -> raise e

let handleable = function
  | Error _
  | NYI _
  | Err _ -> true
  | _ -> false

let report r msg =
  incr num_errs;
  let msg = message_prefix.append_prefix msg in
  BU.print_error (mk_error msg r)

let get_err_count () = !num_errs
