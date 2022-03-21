module FStar_IO
exception EOF
open System
open System.IO
type fd_read  = TextReader
type fd_write = TextWriter

let print_newline _ = Printf.printf "\n"
let print_string x   = Printf.printf "%s" x
let print_uint8 x    = Printf.printf "%02x" x
let print_uint32 x    = Printf.printf "%04x" x
let print_uint64 x    = Printf.printf "%08x" x
let print_any x      = Printf.printf "%A" x
let input_line ()    = System.Console.ReadLine()
let input_int  ()    = Int32.Parse(System.Console.ReadLine())
let input_float ()   = Single.Parse(System.Console.ReadLine(), System.Globalization.CultureInfo.InvariantCulture);
let open_read_file (x:string)  = new StreamReader(x)
let open_write_file (x:string) = File.CreateText(x)
let close_read_file (x:fd_read)   = x.Close()
let close_write_file (x:fd_write) = x.Close()
let read_line (fd:fd_read)     =
    let x = fd.ReadLine() in
    if x=null
    then raise EOF
    else x
let write_string (fd:fd_write) (x:string) =
    fd.Write(x)
