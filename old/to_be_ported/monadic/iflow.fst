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
#monadic(DST, returnTX, bindTX)

module Infoflow

type label =
  | High : label
  | Low  : label
  | Join : label -> label -> label

type CanFlow::label => label => P

assume A3:forall (l:label). CanFlow l l
assume A4:forall (l:label). CanFlow Low l
assume A5:forall (src1:label) (src2:label) (dst:label). (CanFlow src1 dst && CanFlow src2 dst) => CanFlow (Join src1 src2) dst
assume A6:forall (src:label) (dst1:label) (dst2:label). (CanFlow src dst1 && CanFlow src dst2) => CanFlow src (Join dst1 dst2)

type labeled::* => label => * =
  | LTuple:'a -> l:label -> labeled 'a l

type closed::* => * =
  | Close: l:label -> labeled 'a l -> closed 'a

val lift:'a -> D (labeled 'a Low)
let lift x = let res = LTuple x Low in res

val bind2: lf:label 
       -> lx:label 
       -> ly:label 
       -> labeled ('a -> 'b -> D 'c) lf 
       -> labeled 'a lx
       -> labeled 'b ly
       -> D (labeled 'b (Join lf (Join lx ly)))
(* let bind lf lx f x = *)
(*   match (f,x) with *)
(*     | LTuple g m, LTuple y n -> *)
(*         let result = g y in *)
(* 	  LTuple result (Join m n) *)
            

val checkFlow: l:label -> m:label -> Ensures (option unit) (fun h u h' => ((exists o. u=Some o) ==> CanFlow l m))
let rec checkFlow l m =
  match l, m with
    | High, Low -> None
    | l1, l2 when l1 = l2  -> Some()
    | Low, _ -> Some()
    | High, Join m1 m2 ->
        begin
          match (checkFlow High m1, checkFlow High m2) with
            | Some _, Some _ -> Some()
            | _ -> None
        end
    | Join l1 l2, _ ->
        begin
          match (checkFlow l1 m, checkFlow l2 m) with
            | Some _, Some _ -> Some()
            | _ -> None
        end
    | _ -> None<unit>

val bool_and             : x:bool -> y:bool -> z:bool { z=true =>  x=true &&  y=true}
val checkFlowBool : l:label -> m:label -> Ensures bool (fun h b h' => (b=true ==> CanFlow l m))
let rec checkFlowBool l (m:label) =
  match l, m with
    | l1, l2 when l1=l2 -> true
    | Low, _ -> true
    | Join l1 l2, _ ->
        let l1m = checkFlowBool l1 m in
        let l2m = checkFlowBool l2 m in
          bool_and l1m l2m
    | High, Join m1 m2 ->
        let hm1 = checkFlowBool High m1 in
        let hm2 = checkFlowBool High m2 in
          bool_and hm1 hm2
    | _ -> false

val read:unit -> D (closed string)
val print: l:label -> labeled string l -> Requires unit (fun h => (CanFlow l Low))
val strcat: string -> string -> D string
end

module Client
open Infoflow

val main1:unit -> D unit
let main1 (x:unit) =
  match read () with
    | Close src s1 ->
        (match checkFlow src Low with
	   | Some _ -> print src s1
           | _ -> ())
          
val main2:unit -> D unit
let main2 (x:unit) =
  match read (), read () with
      Close src1 s1, Close src2 s2 ->
        let lstrcat : labeled (string -> string -> D string) Low = lift strcat in  (* labeled<string -> string -> string; Low> *)
        let result : labeled (string) (Join Low (Join src1 src2)) = bind2 Low src1 src2 lstrcat s1 s2 in (* :labeled<string -> string; Join(Low, src1)> *)
        let lres = (Join Low (Join src1 src2)) in 
          if checkFlowBool lres Low 
          then print (Join Low (Join src1 src2)) result
          else ()

val main3:unit -> D unit
let main3 (x:unit) =
  match read (), read () with
      Close src1 s1, Close src2 s2 ->
        let lstrcat : labeled (string -> string -> D string) Low = lift strcat in  (* labeled<string -> string -> string; Low> *)
        let result : labeled (string) (Join Low (Join src1 src2)) = bind2 Low src1 src2 lstrcat s1 s2 in (* :labeled<string -> string; Join(Low, src1)> *)
        let lres = (Join Low (Join src1 src2)) in 
          match checkFlow lres Low with 
            | Some _ -> print (Join Low (Join src1 src2)) result
            | _ -> ()

end
