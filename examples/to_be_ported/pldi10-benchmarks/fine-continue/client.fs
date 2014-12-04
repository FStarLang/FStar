(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

open Common

open System.Net
open System.Net.Sockets

let clientLoop () = 
  try begin
    if Array.length Sys.argv < 2 then (pr "usage: client <port>"; exit 1); 

    pr "\nStarting the Fine conference client...\n\n";

    let ip         = System.Net.IPAddress.Parse "127.0.0.1" in
    let port       = ios Sys.argv.(1) in
    let connection = new Socket(AddressFamily.InterNetwork,
                                SocketType.Stream,
                                ProtocolType.IP) in

    connection.Connect(new System.Net.IPEndPoint(ip, port));
    let buf = Bytearray.create 256 in

    while true do 
      pr "> ";
      let s = System.Console.In.ReadLine() in 
      if s.Length > 0 then begin 
        let data = System.Text.Encoding.ASCII.GetBytes(s) in 
        let n = connection.Send(data) in 
        pr "\nMessage sent. Waiting for reply...\n";
        let n = connection.Receive(buf) in 
        let reply = System.Text.Encoding.ASCII.GetString(buf,0,n) in
        pr "Server reply: %s\n\n" reply
      end
    done;
  end
  with e when (e :? Sockets.SocketException) or
              (e :? System.IO.IOException) ->
    pr "Goodbye.\n\n"

let _ = clientLoop ()

