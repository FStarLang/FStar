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
module Ex5

let wrap n =
  let rec fact m = (fact m) + 1 in
    fact n

(* Resulting AST:

wrap = \n:Typ_unknown.
let rec fact = \n:Typ_unknown.  
  ((bind_st 
    (return_st op_GreaterThan(n, "0"))) 
    \x_5:Typ_unknown.  
      if x_5 
      then 
        ((bind_st (return_st op_Subtraction(n, "1"))) 
        \x_6:Typ_unknown.  
          ((bind_st (fact x_6)) 
          \x_6_1:Typ_unknown.  
            (return_st op_Multiply(n, x_6_1))))
      else (return_st "1")) 
  in
  (fact n)


let wrap =
  (abs n _
    (let rec fact = 
      (abs n _
        (app
          (app
            (fvar [Prims; bind_st])
            (app
              (fvar [Prims; return_st])
              (primop op_GreaterThan(bvar n) (constant Const_int32 0))))
          (abs x_5 _
            (cond
            (bvar x_5)
            (app
                (app
                  (fvar [Prims; bind_st])
                  (app
                    (fvar [Prims; return_st])
                    (primop op_Subtraction(bvar n) (constant Const_int32 1))))
                (abs x_6 _
                  (app
                    (app (fvar [Prims; bind_st]) (app (bvar fact) (bvar x_6)))
                    (abs x_6_1 _
                      (app (fvar [Prims; return_st]) (primop op_Multiply(bvar n) (bvar x_6_1)))))))
            (app (fvar [Prims; return_st]) (constant Const_int32 1)))))) ))

*)
