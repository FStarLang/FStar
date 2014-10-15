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
module DB

open System.IO

open Common
open Types

let strItemDbFile     = "data/itemdb.txt"
let strPaperDbFile    = "data/paperdb.txt"
let strReviewDbFile   = "data/reviewdb.txt"

let delim = "========================================"


let strToRole = function
  | "Author" -> Author
  | "Reviewer" -> Reviewer
  | "Chair" -> Chair
  | s -> failwith (spr "strToRole: %s" s)

let strToPhase = function
  | "Init" -> Init 
  | "PreSubmission" -> PreSubmission 
  | "Submission" -> Submission 
  | "Bidding" -> Bidding 
  | "Assignment" -> Assignment 
  | "Reviewing" -> Reviewing 
  | "Discussion" -> Discussion 
  | "Notification" -> Notification 
  | "Done" -> Done 
  | s -> failwith (spr "strToPhase: %s" s)

let strToItem s =
  match (List.map trim (String.split ['#'] s)) with
    | ["Phase";s1] -> Phase (strToPhase s1)
    | ["Role";s1;s2] -> Role (strToPrin s1, strToRole s2)
    | ["Submitted";s1;s2] -> Submitted (strToPrin s1, ios s2)
    | ["Bid";s1;s2] -> Bid (strToPrin s1, ios s2)
    | ["Conflict";s1;s2] -> Conflict (strToPrin s1, ios s2)
    | ["Assigned";s1;s2] -> Assigned (strToPrin s1, ios s2)
    | ["Reviewed";s1;s2] -> Reviewed (strToPrin s1, ios s2)
    | ["PendingReview";s1;s2] -> PendingReview (strToPrin s1, ios s2)
    | _ -> failwith (spr "strToItem: %s" s)


let strOfPrin = function
  | Admin -> "Admin"
  | U(s) -> s

let strOfRole = function
  | Author -> "Author"
  | Reviewer -> "Reviewer"
  | Chair -> "Chair"

let strOfPhase = function
  | Init  -> "Init"
  | PreSubmission  -> "PreSubmission"
  | Submission  -> "Submission"
  | Bidding  -> "Bidding"
  | Assignment  -> "Assignment"
  | Reviewing  -> "Reviewing"
  | Discussion  -> "Discussion"
  | Notification -> "Notification"
  | Done  -> "Done"

let strOfItem x =
  let f = String.concat " # " in
  match x with
    | Phase(p) -> f ["Phase"; strOfPhase p]
    | Role(p,r) -> f ["Role"; strOfPrin p; strOfRole r]
    | Submitted(p,i) -> f ["Submitted"; strOfPrin p; soi i]
    | Bid(p,i) -> f ["Bid"; strOfPrin p; soi i]
    | Conflict(p,i) -> f ["Conflict"; strOfPrin p; soi i]
    | Assigned(p,i) -> f ["Assigned"; strOfPrin p; soi i]
    | Reviewed(p,i) -> f ["Reviewed"; strOfPrin p; soi i]
    | PendingReview(p,i) -> f ["PendingReview"; strOfPrin p; soi i]


(* write papid, title, author, paperdata, and delim on 5 lines *)
let writePaperToDB (p:paper) =
  let oc = File.AppendText(strPaperDbFile) in
    fpr oc "%d\n" p.papid;
    fpr oc "%s\n" p.title;
    fpr oc "%s\n" (strOfPrin p.author);
    fpr oc "%s\n" p.paperdata;
    fpr oc "%s\n" delim;
    oc.Flush (); oc.Close ();
    0
      
(* write rid, pid, reviewer, reviewdata, and delim on 5 lines *)
let writeReviewToDB (r:review) =
  let oc = File.AppendText(strReviewDbFile) in
    fpr oc "%d\n" r.rid;
    fpr oc "%d\n" r.pid;
    fpr oc "%s\n" (strOfPrin r.reviewer);
    fpr oc "%s\n" r.reviewdata;
    fpr oc "%s\n" delim;
    oc.Flush (); oc.Close ();
    0

let writeItemToDB_ oc (x:item) =
  fpr oc "%s\n" (strOfItem x);
  oc.Flush (); oc.Close ();
  0

(* append to itemdb.txt *)
let writeItemToDB (x:item) =
  let oc = File.AppendText(strItemDbFile) in
    writeItemToDB_ oc x

(* ovewrite itemdb.txt *)
let rewriteAllItemsToDB (l:items) =
  let oc = new StreamWriter(strItemDbFile) in
  let rec foo = function
    | ANil -> 0
    | ACons(x,tl) -> let _ = writeItemToDB_ oc x in foo tl
  in
    foo l


let mapFileLines (file:string) (f:string -> 'a) : list<'a> =
  let stream = new StreamReader(file) in
  let rec foo acc =
    try foo ((f (stream.ReadLine()))::acc)
    with _ -> acc
  in
  let l = List.rev (foo []) in
  pr "LOADING: Read %d lines from %s.\n" (List.length l) file;
  stream.Close ();
  l

let mapFileEntries (file:string) (f:string list -> 'a) : list<'a> =
  let stream = new StreamReader(file) in
  let rec foo entries currEntry =
    let s = stream.ReadLine() in
    (* using null instead, since exception not being thrown at EOF... *)
    if s = null then entries
    else if s = delim then foo ((f (List.rev currEntry))::entries) []
    else foo entries (s::currEntry)
  in
  let l = List.rev (foo [] []) in
  pr "LOADING: Read %d entries from %s.\n" (List.length l) file;
  stream.Close ();
  l

(* read all papers from paperdb.txt *)
let loadPapers () =
  mapFileEntries strPaperDbFile
    (function [s0;s1;s2;s3] ->
       { papid=ios s0; title=s1; author=strToPrin s2; paperdata=s3 }
    | _ -> failwith "corrupt paperdb entry")

(* read all papers from reviewdb.txt *)
let loadReviews () =
  mapFileEntries strReviewDbFile
    (function [s0;s1;s2;s3] ->
       { rid=ios s0; pid=ios s1; reviewer=strToPrin s2; reviewdata=s3 }
    | _ -> failwith "corrupt reviewdb entry")

(* read all items from itemdb.txt *)
let loadItems () =
  mapFileLines strItemDbFile strToItem

type dbrec = {items:items; papers:papers; reviews: reviews}
type db = 
  | Empty
  | DB of dbrec

let rec listToItems = function
    [] -> ANil
  | hd::tl -> ACons (hd, listToItems tl)

let rec listToReviews = function
    [] -> RNil
  | hd::tl -> RCons (hd, listToReviews tl)

let rec listToPapers = function
    [] -> PNil
  | hd::tl -> PCons (hd, listToPapers tl)

let loadDB (i:int) =
  if not (File.Exists strItemDbFile) then
    Empty 
  else
    let items = listToItems (loadItems ()) in
    let papers = listToPapers (loadPapers ()) in
    let reviews = listToReviews (loadReviews ()) in
      DB {items=items; papers=papers; reviews=reviews}



