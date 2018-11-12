(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
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

