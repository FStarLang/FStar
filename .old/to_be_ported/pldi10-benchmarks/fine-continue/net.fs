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
module Net

open System.Net
open System.Net.Sockets
open System.Threading
open Common
open Types

type socket=Sock of Socket
type stream=Stream of NetworkStream

type requestAndStream =
  | RS of request * stream
  | Dummy (* F# code generator specializes code generator for variants with only one case *)

(* TODO make this part of ref monitor state, and use id-less papers and reviews from here *)
let paperCount = ref 0
let reviewCount = ref 0
let mkid k = incr k; !k

let parseRequest s =
  match (List.map trim (String.split ['#'] s)) with
    | [s0;"AdvanceState"] -> (ReqAdvancePhase (strToPrin s0))
    | [s0;"AddReviewer";s2] -> (ReqAddReviewer (strToPrin s0, strToPrin s2))
    | [s0;"BecomeAuthor"] -> (ReqBecomeAuthor (strToPrin s0))
    | [s0;"SubmitPaper";s2;s3] ->
        let req = (ReqSubmitPaper (strToPrin s0, {papid=mkid paperCount; title=s2; author=strToPrin s0; paperdata=s3})) in
          print_any req; req
    | [s0;"ReadPaperList"] -> (ReqReadPaperList (strToPrin s0))
    | [s0;"ReadPaper";s2] -> (ReqReadPaper (strToPrin s0, ios s2))
    | [s0;"BidPaper";s2] -> (ReqBidPaper (strToPrin s0, ios s2))
    | [s0;"MarkConflict";s2] -> (ReqMarkConflict (strToPrin s0, ios s2))
    | [s0;"AssignPaper";s2;s3] -> (ReqAssignPaper (strToPrin s0, strToPrin s2, ios s3))
    | [s0;"ReviewPaper";s2;s3] ->
         (ReqReviewPaper (strToPrin s0, ios s2, {rid=mkid reviewCount; pid=ios s2; reviewer=strToPrin s0; reviewdata=s3}))
    | [s0;"ReadReviews";s2] -> (ReqReadReviews (strToPrin s0, ios s2))
    | [s0;"MakeDecision";s2] -> (ReqMakeDecision (strToPrin s0, ios s2))
    | _ -> ReqGarbage

let startConnection numConnections = 
  let sock = new Socket(AddressFamily.InterNetwork,
                        SocketType.Stream, ProtocolType.IP) in 
    sock.Bind(new IPEndPoint(IPAddress.Parse("127.0.0.1"), 0));
    sock.Listen(numConnections);
    pr "\nStarting the Fine conference server. Listening on port %d...\n\n"
      ((sock.LocalEndPoint :?> IPEndPoint).Port);
    Sock sock

let getRequest (Sock sock) = 
  let connection = sock.Accept() in
    pr "Beginning of client connection.\n\n";
    try
      let buf = Bytearray.create 256 in
      let stream = new NetworkStream(connection) in
      let nread = stream.Read(buf,0,256) in
      let reqstr = System.Text.Encoding.ASCII.GetString(buf,0,nread) in
      let _ = pr "Read from client:\n[%s]\n\n" reqstr in
        RS(parseRequest reqstr, Stream stream)
    with e when 
      (e :? Sockets.SocketException) or (e :? System.IO.IOException) ->
        pr "End of client connection.\n\n";
        exit 0
          
let sendResponse (Stream stream) str = 
  try
    pr "Sending reply:\n[%s]\n\n" str;
    let reply = System.Text.Encoding.ASCII.GetBytes(str) in
    let len = String.length str in
    let _ = stream.Write(reply, 0, len) in
      len
  with e when 
    (e :? Sockets.SocketException) or (e :? System.IO.IOException) ->
      pr "End of client connection.\n\n";
      exit 0
        
