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
module Ex12_Refined

(* Source program         *)
(* let copy_refined x y = *)
(*   y := !x              *)

type Pre_H :: _ = (fun (h:heap) => True)
type Post_H :: _ = (fun (x:ref int) (y:ref int) (u:unit) (h:heap) => ((Select h y) = (Select h x)))

val copy_refined : x:ref int
                 -> y:ref int
                 -> ST Pre_H unit (Post_H x y)

let copy_refined (x: ref int) (y: ref int) =
  bind_st<
          (* (fun (h:heap) => Post_H x y () (Update h y (Select h x))), *)
          (fun (h:heap) => ((Select (Update h y (Select h x)) y) = (Select (Update h y (Select h x)) x))),
          int,
          fun (r:int) (h:heap) => Post_H x y () (Update h y r),
          unit,
          (Post_H x y)
         >
    (read<int, fun (r:int) (h:heap) => Post_H x y () (Update h y r)> x)
    (fun (v:int) -> write<int, Post_H x y> y v)

