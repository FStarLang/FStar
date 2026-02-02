open FStarC_Json

let stdout_isatty () = Some (Unix.isatty Unix.stdout)

(* NOTE: this is deciding whether or not to color by looking
   at stdout_isatty(), which may be a wrong choice if
   we're instead outputting to stderr. e.g.
     fstar.exe Blah.fst 2>errlog
   will colorize the errors in the file if stdout is not
   also redirected.
*)
let colorize (o, c) s =
  match stdout_isatty () with
  | Some true -> o^s^c
  | _ -> s

let colorize_bold    = colorize ("\x1b[39;1m", "\x1b[0m")
let colorize_red     = colorize ("\x1b[31;1m", "\x1b[0m")
let colorize_yellow  = colorize ("\x1b[33;1m", "\x1b[0m")
let colorize_cyan    = colorize ("\x1b[36;1m", "\x1b[0m")
let colorize_green   = colorize ("\x1b[32;1m", "\x1b[0m")
let colorize_magenta = colorize ("\x1b[35;1m", "\x1b[0m")

type printer = {
  printer_prinfo: string -> unit;
  printer_prwarning: string -> unit;
  printer_prerror: string -> unit;
  printer_prgeneric: string -> (unit -> string) -> (unit -> json) -> unit
}

let pr = Printf.printf
let fpr = Printf.fprintf

let default_printer =
  { printer_prinfo = (fun s -> pr "%s" s; flush stdout);
    printer_prwarning = (fun s -> fpr stderr "%s" (colorize_yellow s); flush stdout; flush stderr);
    printer_prerror = (fun s -> fpr stderr "%s" (colorize_red s); flush stdout; flush stderr);
    printer_prgeneric = fun label get_string get_json -> pr "%s: %s" label (get_string ())}

let current_printer = ref default_printer
let set_printer printer = current_printer := printer

let print_raw s = set_binary_mode_out stdout true; pr "%s" s; flush stdout
let print_string s = (!current_printer).printer_prinfo s
let print_generic label to_string to_json a = (!current_printer).printer_prgeneric label (fun () -> to_string a) (fun () -> to_json a)
let print_any s = (!current_printer).printer_prinfo (Marshal.to_string s [])

(* restore pre-2.11 BatString.nsplit behavior,
   see https://github.com/ocaml-batteries-team/batteries-included/issues/845 *)
let batstring_nsplit s t =
  if s = "" then [] else BatString.split_on_string t s

let fmt (fmt:string) (args:string list) =
  let frags = batstring_nsplit fmt "%s" in
  if BatList.length frags <> BatList.length args + 1 then
    failwith ("Not enough arguments to format string " ^fmt^ " : expected " ^ (Stdlib.string_of_int (BatList.length frags)) ^ " got [" ^ (BatString.concat ", " args) ^ "] frags are [" ^ (BatString.concat ", " frags) ^ "]")
  else
    let open FStarC_StringBuffer in
    let sbldr = create (Z.of_int 80) in
    ignore (add (List.hd frags) sbldr);
    BatList.iter2
        (fun frag arg -> sbldr |> add arg |> add frag |> ignore)
        (List.tl frags) args;
    contents sbldr

let fmt1 f a = fmt f [a]
let fmt2 f a b = fmt f [a;b]
let fmt3 f a b c = fmt f [a;b;c]
let fmt4 f a b c d = fmt f [a;b;c;d]
let fmt5 f a b c d e = fmt f [a;b;c;d;e]
let fmt6 f a b c d e g = fmt f [a;b;c;d;e;g]

let flush_stdout () = flush stdout

let print1 a b = print_string (fmt1 a b)
let print2 a b c = print_string (fmt2 a b c)
let print3 a b c d = print_string (fmt3 a b c d)
let print4 a b c d e = print_string (fmt4 a b c d e)
let print5 a b c d e f = print_string (fmt5 a b c d e f)
let print6 a b c d e f g = print_string (fmt6 a b c d e f g)
let print f args = print_string (fmt f args)

let print_error s = (!current_printer).printer_prerror s
let print1_error a b = print_error (fmt1 a b)
let print2_error a b c = print_error (fmt2 a b c)
let print3_error a b c d = print_error (fmt3 a b c d)

let print_warning s = (!current_printer).printer_prwarning s
let print1_warning a b = print_warning (fmt1 a b)
let print2_warning a b c = print_warning (fmt2 a b c)
let print3_warning a b c d = print_warning (fmt3 a b c d)
