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
module Ex1_Refined

(* Source program *)
(* val foo : x:int -> ST True_H int (Post_H x) *)
(* let foo (x:int) = *)
(*   let r = ref x in *)
(*     (r := !r + 1); *)
(*     !r *)

type True_H :: _ = fun (h:heap) => True
type Post_H :: _ = (fun (x:int) (y:int) (h:heap) => (y = (Plus x 1)))

val foo : x:int -> ST True_H int (Post_H x)
let foo (x:int) = 
  bind_st<
          (fun (h:heap) => 
            (forall (r:ref int). 
              (Mem r (Domain h) = false) => 
                Post_H x 
                  (Select (Update (Update h r x) r (Plus (Select (Update h r x) r) 1)) r) 
                  (Update (Update h r x) r (Plus (Select (Update h r x) r) 1)))), 
          ref int, 
          (fun (r:ref int) (h:heap) => 
            Post_H x 
              (Select (Update h r (Plus (Select h r) 1)) r) 
              (Update h r (Plus (Select h r) 1))),
          int, 
          (Post_H x)> 
    (ref<int, 
         (fun (r:ref int) (h:heap) => 
           Post_H x 
             (Select (Update h r (Plus (Select h r) 1)) r) 
             (Update h r (Plus (Select h r) 1)))> 
      x)
    (fun (r:ref int) -> 
       bind_st<(fun (h:heap) => 
                 Post_H x 
                   (Select (Update h r (Plus (Select h r) 1)) r) 
                   (Update h r (Plus (Select h r) 1))), 
               int, 
               (fun (tmp:int) (h:heap) => 
                 Post_H x 
                   (Select (Update h r (Plus tmp 1)) r) 
                   (Update h r (Plus tmp 1))), 
               int, 
               Post_H x>
         (read<int, 
               (fun (tmp:int) (h:heap) => 
                 Post_H x 
                   (Select (Update h r (Plus tmp 1)) r) 
                   (Update h r (Plus tmp 1)))> 
           r)
         (fun (tmp:int) -> 
            bind_st<(fun (h:heap) => 
                      Post_H x 
                        (Select (Update h r (Plus tmp 1)) r) 
                        (Update h r (Plus tmp 1))), 
                    unit, 
                    (fun (u:unit) (h:heap) => Post_H x (Select h r) h), 
                    int, 
                    Post_H x>
              (write<int, (fun (u:unit) (h:heap) => Post_H x (Select h r) h)> r (tmp + 1))
              (fun () -> read<int, Post_H x> r)))
    

