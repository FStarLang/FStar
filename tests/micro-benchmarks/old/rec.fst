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
module Foo.Record

type big = {
  a1:int;
  a2:int;
  a3:int;
  a4:int;
  a5:int;
  a6:int;
  a7:int;
  a8:int;
  a9:int;
  a10:int;
  a11:int;
  a12:int;
  a13:int;
  a14:int;
  a15:int;
}

let impure x =
  if x = 0
  then 0
  else if x=1
  then 1
  else if x=2
  then 2
  else if x=3
  then 3
  else x

let set1 b x = {b with a1=impure x}
let set2 b x = {b with a2=impure x}
let set3 b x = {b with a3=impure x}
let set4 b x = {b with a4=impure x}
let set5 b x = {b with a5=impure x}
let set6 b x = {b with a6=impure x}
let set7 b x = {b with a7=impure x}
let set8 b x = {b with a8=impure x}
let set9 b x = {b with a9=impure x}
let set10 b x = {b with a10=impure x}
let set11 b x = {b with a11=impure x}
let set12 b x = {b with a12=impure x}
let set13 b x = {b with a13=impure x}
let set14 b x = {b with a14=impure x}
let set15 b x = {b with a15=impure x}

let rec loop f = loop (fun x -> f x)

let rec visit_pat0 k0 = k0 0
and visit_pats0 k1 = visit_pat0 (fun _ -> visit_pats0 k1)
  
let rec visit_pat1 pat cont = cont (0, pat)
and visit_pats1 pat cont = visit_pat1 pat (fun (_,_) -> visit_pats1 pat (fun z -> cont 0))

let rec visit_pat2 pat cont = cont (0, pat)
and visit_pats2 pats cont = match pats with
  | [] -> failwith ""
  | hd::tl -> visit_pat2 hd (fun (_, hd) ->
    visit_pats2 tl (fun _ ->
      cont (hd::tl)))

let rec visit_pat3 env pat cont = cont (env, pat)
and visit_pats3 env pats cont = match pats with
  | [] -> failwith ""
  | hd::tl -> visit_pat3 env  hd (fun (env, hd) ->
    visit_pats3 env tl (fun (env, tl) ->
      cont (env, hd::tl)))

type r = {
  a:int;
  b:int;
}
let withb b a = {a=a; b=b}
let zr r =
  let w = withb r.b in
  w 0

let rec ff x = let y = 0 in ff y

let rec cps_len x k = match x with
  | [] -> k 0
  | hd::tl -> cps_aux hd (fun n -> cps_len tl (fun i -> k (i + n)))
and cps_aux x k = match x with
  | [] -> k 0
  | hd::tl -> cps_aux tl (fun n -> k (n + 1))

type t =
  | Leaf of int
  | Node of list t

let rec vt x f k = match x with
  | Leaf i -> k (f i)
  | Node xs -> vts xs f k
and vts xs f k = match xs with
  | [] -> k 0
  | hd::tl -> vt hd f (fun l -> vts tl f (fun m -> k (l+m)))
 
let foo x y =
  if x <= y && y <= x
  then 0
  else 1

let matchr r = match r with
  | ({a=_}) -> 1

type pair = {x:int; y:int}
and triple = {fst:pair; z:int}

let mkR i j = {a=i; b=j}
let mkPair i j = {x=i; y=j}
let mkFoo i = {fst={x=i; y=i}; z=i}

let a x = x.a
let f x y = {x=x; y=y}
let g p = p.x
let h p = p.y
let i p = match p with
  | {fst=_} -> ""

let rec even x = x=0 || not (odd (x - 1))
and odd x = x=1 || not (even (x - 1))

