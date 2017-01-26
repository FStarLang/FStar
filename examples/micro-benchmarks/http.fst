module Http

let host = "google.com"
let a = Tcp.connect host 80
let req = "GET / HTTP/1.0\r\nHost: "^host^"\r\n\r\n"
let b = Tcp.write a (Bytes.string_as_utf8_bytes req)
let r = 
  let x = Tcp.read a 1000 in
  match x with
  | Some b -> IO.print_string (Bytes.unicode_bytes_as_string b)
  | None -> IO.print_string "Fail!\n"

