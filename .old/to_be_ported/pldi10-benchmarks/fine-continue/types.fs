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
module Types

type prin = | U : string -> prin | Admin : prin

type paper = {papid:int; title:string; author:prin; paperdata:string} 
type review = {rid:int; pid:int; reviewer:prin; reviewdata:string} 

type papers =
  | PNil
  | PCons of paper * papers

type reviews =
  | RNil
  | RCons of review * reviews

type request = 
  | ReqAdvancePhase of prin
  | ReqAddReviewer of prin * prin
  | ReqBecomeAuthor of prin
  | ReqSubmitPaper of prin * paper
  | ReqReadPaperList of prin
  | ReqReadPaper of prin * int
  | ReqBidPaper of prin * int
  | ReqMarkConflict of prin * int
  | ReqAssignPaper of prin * prin * int
  | ReqReviewPaper of prin * int * review
  | ReqReadReviews of prin * int
  | ReqMakeDecision of prin * int
  | ReqGarbage

(* F# types in which all constructors are nullary have specialized code generation. 
   So, add a dummy unary constructor to the end of each *)
type role =
  | Author
  | Reviewer
  | Chair
  | DummyRole of int

type phase =
  | Init       
  | PreSubmission (* polls open, must register before this phase ends *)
  | Submission 
  | Bidding  (* bids and conflicts happen at same time *)
  | Assignment 
  | Reviewing 
  | Discussion 
  | Notification 
  | Done 

type action =
  | AdvancePhase
  | AddReviewer of prin
  | BecomeAuthor
  | SubmitPaper
  | ReadPaperList
  | ReadPaper of  int
  | BidPaper of int
  | MarkConflict of int
  | AssignPaper of prin * int
  | ReviewPaper of int
  | ReadReviews of int
  | MakeDecision of int

type item =
  (* only one phase at a time, so this could be kept elsewhere *)
  | Phase of phase
  (* items to record what actions have occurred *)
  | Role of prin * role
  | Submitted of prin * int
  | Bid of prin * int
  | Conflict of prin * int
  | Assigned of prin * int
  | Reviewed of prin * int
  (* incremental state *)
  | PendingReview of prin * int (* corresponding to Assigned r i *)

type items =
  | ANil
  | ACons of item * items

(* U name must have no spaces -- this requirement is stale I think *)
let strToPrin = function
  | "Admin" -> Admin
  | s -> U s


