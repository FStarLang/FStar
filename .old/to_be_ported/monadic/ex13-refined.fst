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
#monadic(DST, returnDST, composeDST)
module Ex13_Refined

(*
let add (x:ref int) (y:int) =
  let vx = !x in
  let res = vx + y in
    res
*)

type True_H :: _ = fun (h:heap) => True
type Post_H :: _ = (fun (x:ref int) (y:int) (res:int) (h:heap) => (res = (Plus (Select h x) y)))

val bar : x:ref int -> y:int -> ST True_H int (Post_H x y)

let bar (x:ref int) (y:int) =
  bind_st<
          (fun (h:heap) => Post_H x y (Plus (Select h x) y) h),
          int,
          (fun (vx:int) (h:heap) => Post_H x y (Plus vx y) h),
          int,
          (Post_H x y)>
    (read<int, (fun (vx:int) (h:heap) => Post_H x y (Plus vx y) h)> x)
    (fun vx -> 
      let res = vx + y in
        return_st<int, (Post_H x y)> res)

