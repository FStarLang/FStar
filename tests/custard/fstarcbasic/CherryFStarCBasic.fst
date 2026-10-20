module CherryFStarCBasic

(* The Cherry implementations of FStarC.Format, FStarC.Filepath,
   FStarC.Getopt, FStarC.Platform.Base and FStarC.Plugins.Base, and the
   definitions of FStar.Char.  Run with the
   arguments [--flag -v 7 rest], stdout and stderr redirected to files, and
   CHERRY_UTIL_TMP naming an empty directory. *)
open FStarC.Effect
module F = FStarC.Format
module P = FStarC.Filepath
module G = FStarC.Getopt
module U = FStarC.Util

let check (b:bool) (n:int) (acc:int) : int = if b then acc else acc * 100 + n

let fails (#a:Type) (f:unit -> ML a) : ML bool =
  try_with (fun () -> let _ = f () in false)
           (fun e -> match e with Failure _ -> true | _ -> false)

(* Each pair is what BatPathGen gives for the path. *)
let canonical : list (string & string) = [
  "", "/"; "/", "/"; "a", "a"; "a/", "a"; "/a/b/../c", "/a/c"; "a/./b", "a/b";
  "../a", "../a"; "a/../..", ".."; "./", "."; "..", ".."; "a//b", "a/b"; "//a", "/a";
  "a/..", "."; "./a", "a"; "a/../../b", "../b"; "../../a/b/../c", "../../a/c";
  "/a/..", "/"; "/./a", "/a"; "a/b/c/../../d", "a/d"; "..a/b", "..a/b"; "a/.../b", "a/.../b";
]

let joined : list (string & string & string) = [
  "a", "b", "a/b"; "a/", "b", "a/b"; "/a", "b/c", "/a/b/c"; "", "b", "/b"; "/", "b", "/b";
  "a/b", "..", "a/b/.."; "a", "./b", "a/./b"; "a//", "b", "a/b"; ".", "..", "./.."; "a", "b//c", "a/b/c";
]

let rec all (#a:Type) (f:a -> ML bool) (l:list a) : ML bool =
  match l with
  | [] -> true
  | x :: l -> f x && all f l

let main () : ML FStar.UInt32.t =
  let e = 0 in
  (* Format. *)
  let e = check (F.fmt "%s+%s=%s" ["1"; "2"; "3"] = "1+2=3" && F.fmt "" [] = "" && F.fmt "x" [] = "x"
                 && F.fmt2 "%s%s" "a" "b" = "ab") 1 e in
  let e = check (F.stdout_isatty () = Some false && F.colorize_red "x" = "x") 2 e in
  F.print1 "hello %s\n" "world";
  F.print_raw "raw\n";
  F.print1_warning "warn %s\n" "w";
  F.print_error "err\n";
  let got = mk_ref "" in
  F.set_printer { F.default_printer with F.printer_prinfo = (fun s -> got := !got ^ s) };
  F.print2 "%s-%s" "a" "b";
  F.set_printer F.default_printer;
  F.print_string "done\n";
  F.flush_stdout ();
  let e = check (!got = "a-b") 3 e in
  (* Filepath, as BatPathGen and OCaml's Filename, except where they
     raise. *)
  let e = check (all (fun (p, c) -> P.canonicalize p = c) canonical) 4 e in
  let e = check (P.canonicalize "/.." = "/" && P.canonicalize "/a/../../b" = "/b") 5 e in
  let e = check (all (fun (p, q, r) -> P.join_paths p q = r) joined) 6 e in
  let e = check (P.join_paths "a" "/b//c" = "/b/c" && P.join_paths "a" "" = "/"
                 && P.get_file_extension "noext" = ""
                 && P.is_path_absolute "" && P.is_path_absolute "/a"
                 && not (P.is_path_absolute "a") && P.get_file_extension "a.b.fst" = "fst"
                 && P.get_file_extension "a." = "" && P.get_file_extension "d.x/f" = "x/f") 7 e in
  let e = check (P.basename "/a/b/" = "b" && P.basename "" = "." && P.dirname "a//b" = "a"
                 && P.dirname "/a" = "/" && P.dirname "a" = ".") 8 e in
  let cwd = P.getcwd () in
  let e = check (P.normalize_file_path "x/../y" = P.canonicalize (cwd ^ "/y")
                 && P.normalize_file_path "/q/./r" = "/q/r") 9 e in
  let tmp = match U.expand_environment_variable "CHERRY_UTIL_TMP" with Some d -> d | None -> "" in
  let empty = P.readdir tmp in
  U.write_file (tmp ^ "/f2") "2";
  U.write_file (tmp ^ "/f1") "1";
  U.mkdir false false (tmp ^ "/d");
  let entries = FStar.List.Tot.sortWith FStar.String.compare (P.readdir tmp) in
  let f1 = fails (fun () -> P.readdir (tmp ^ "/none")) in
  let e = check (tmp <> "" && empty = [] && entries = ["d"; "f1"; "f2"] && f1) 10 e in
  let same = P.paths_to_same_file (tmp ^ "/f1") (tmp ^ "/d/../f1") in
  let diff = P.paths_to_same_file (tmp ^ "/f1") (tmp ^ "/f2") in
  let f1 = fails (fun () -> P.paths_to_same_file (tmp ^ "/f1") (tmp ^ "/none")) in
  let e = check (same && not diff && f1 && P.file_exists (tmp ^ "/d") && P.is_directory (tmp ^ "/d")
                 && not (P.is_directory (tmp ^ "/f1")) && not (P.file_exists (tmp ^ "/none"))) 11 e in
  (* Getopt. *)
  let flag = mk_ref false in
  let v = mk_ref 0 in
  let rest = mk_ref [] in
  let specs : list G.opt = [
    (G.noshort, "flag", G.ZeroArgs (fun () -> flag := true));
    ('v', "val", G.OneArg ((fun s -> v := U.int_of_string s), "n"));
  ] in
  let others (s:string) : ML G.parse_cmdline_res = rest := s :: !rest; G.Success in
  let r = G.parse_cmdline specs others in
  let e = check (G.Success? r && !flag && !v = 7 && !rest = ["rest"]
                 && FStar.List.Tot.length (G.cmdline ()) = 5) 12 e in
  let r1 = G.parse_string specs others "-v 3 'a b'" in
  let r2 = G.parse_string specs others "--val 'x y'" in
  let r3 = G.parse_string specs others "'a" in
  let r4 = G.parse_list specs others ["--nope"] in
  let r5 = G.parse_list specs others ["--val"] in
  let e = check (G.Success? r1 && !v = 3 && !rest = ["a b"; "rest"] && G.Error? r2 && G.Error? r3
                 && r4 = G.Error ("unrecognized option '--nope'\n", "--nope") && G.Error? r5) 13 e in
  (* Platform.Base and Plugins.Base. *)
  let dyn = try_with (fun () -> FStarC.Plugins.Base.dynlink_loadfile "p.cmxs"; false)
                     (fun e -> match e with FStarC.Plugins.Base.DynlinkError _ -> true | _ -> false) in
  let e = check (FStarC.Platform.Base.Unix? FStarC.Platform.Base.system
                 && FStarC.Platform.Base.kernel () <> "" && dyn) 14 e in
  (* FStar.Char's definitions, which Cherry maps to its runtime. *)
  let e = check (FStar.Char.int_of_char 'A' = 65 && FStar.Char.char_of_int 0x3bb = '\u03bb'
                 && FStar.Char.uppercase 'q' = 'Q' && FStar.Char.lowercase 'Q' = 'q'
                 && FStar.Char.uppercase '\u00e9' = '\u00e9' && FStar.Char.lowercase '[' = '[') 15 e in
  if e <> 0 then (U.print_endline (string_of_int e); 1ul) else 0ul
