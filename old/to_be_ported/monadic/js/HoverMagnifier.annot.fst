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
#monadic(DST,returnTX,bindTX)
module HoverMagnifier
 val main : unit -> DST JSVerify.dyn ((fun ('x_0_2473::(result JSVerify.dyn => (heap => E))) => (fun (x_0_2474:heap) => l_and (pf (DOM.InitialHeap x_0_2474)) (pf (Forall (result JSVerify.dyn) ((fun (x_0_2475:result JSVerify.dyn) => pf (Forall heap ((fun (x_0_2476:heap) => pf ('x_0_2473 x_0_2475 x_0_2476))))))))))) 

 let  main = (fun (x_0_2477:unit) -> 
                let x_0_2479 = JSVerify.update (JSVerify.Obj JSVerify.global) "oldElt" JSVerify.Undef in
                  
                let x_0_2481 = JSVerify.update (JSVerify.Obj JSVerify.global) "oldSize" JSVerify.Undef in
                  
                let x_0_2503 = JSVerify.update (JSVerify.Obj JSVerify.global) "magnify" 
                  (JSVerify.mkFun<(Meta_named "magnify" (Meta_tid 1))> "0,53" 
                     ((fun (x_0_2482:JSVerify.dyn) -> (fun (x_0_2483:JSVerify.dyn) -> 
                                                         let x_0_2485 = 
                                                           let x_0_2484 = JSVerify.alloc () in
                                                             x_0_2484 in
                                                           
                                                         let x_0_2487 = JSVerify.update x_0_2485 "evt" (JSVerify.select x_0_2483 "0") in
                                                           
                                                         let x_0_2489 = JSVerify.update x_0_2485 "elt" (JSVerify.select (JSVerify.select x_0_2485 "evt") "target") in
                                                           
                                                         let x_0_2495 = 
                                                           let x_0_2491 = JSVerify.coerceBool (JSVerify.select (JSVerify.Obj JSVerify.global) "oldElt") in
                                                             if x_0_2491 then 
                                                               let x_0_2493 = JSVerify.update (JSVerify.select (JSVerify.select (JSVerify.Obj JSVerify.global) "oldElt") "style") "fontSize" (JSVerify.select (JSVerify.Obj JSVerify.global) "oldSize") in
                                                                 JSVerify.Undef 
                                                             else JSVerify.Undef in
                                                           
                                                         let x_0_2497 = JSVerify.update (JSVerify.Obj JSVerify.global) "oldElt" (JSVerify.select x_0_2485 "elt") in
                                                           
                                                         let x_0_2499 = JSVerify.update (JSVerify.Obj JSVerify.global) "oldSize" (JSVerify.select (JSVerify.select (JSVerify.select x_0_2485 "elt") "style") "fontSize") in
                                                           
                                                         let x_0_2501 = JSVerify.update (JSVerify.select (JSVerify.select x_0_2485 "elt") "style") "fontSize" (JSVerify.Str "30px") in
                                                           JSVerify.Undef)))) in
 
                let x_0_2508 = JSVerify.update (JSVerify.Obj JSVerify.global) "elts" 
                  (JSVerify.apply_hint<(Meta_named "getElementsByTagName" DOM.GetElementsByTagNameTX)> 
                     (JSVerify.select (JSVerify.select (JSVerify.Obj JSVerify.global) "document") "getElementsByTagName")
                     (JSVerify.select (JSVerify.Obj JSVerify.global) "document") (
                       let x_0_2504 = JSVerify.alloc () in
                         
                       let x_0_2506 = JSVerify.update x_0_2504 "0" (JSVerify.Str "body") in
                         x_0_2504)) in
                  
                let x_0_2511 = JSVerify.update (JSVerify.Obj JSVerify.global) "body" 
                  (JSVerify.apply_hint<(DOM.NextTX (DOM.HasTag (JSVerify.Str "body")))> 
                     (JSVerify.select (JSVerify.select (JSVerify.Obj JSVerify.global) "elts") "Next") (JSVerify.select (JSVerify.Obj JSVerify.global) "elts") (
                       let x_0_2509 = JSVerify.alloc () in
                         x_0_2509)) in
                  
                let x_0_2533 = 
                  let x_0_2513 = JSVerify.coerceBool (JSVerify.select (JSVerify.Obj JSVerify.global) "body") in
                    if x_0_2513 then 
                      let x_0_2526 = JSVerify.update (JSVerify.select (JSVerify.Obj JSVerify.global) "body") "onmousemove" 
                        (JSVerify.mkFun<(Meta_named "onmousemove" (Meta_tid 2))> "0,392" 
                           ((fun (x_0_2514:JSVerify.dyn) -> (fun (x_0_2515:JSVerify.dyn) -> 
                                                               let x_0_2517 = 
                                                                 let x_0_2516 = JSVerify.alloc () in
                                                                   x_0_2516 in
                                                                 
                                                               let x_0_2519 = JSVerify.update x_0_2517 "evt" (JSVerify.select x_0_2515 "0") in
                                                                 
                                                               let x_0_2524 = JSVerify.apply_hint<(Meta_named "magnify" (Meta_tid 1))> 
                                                                 (JSVerify.select (JSVerify.Obj JSVerify.global) "magnify") (JSVerify.Obj JSVerify.global) (
                                                                   let x_0_2520 = JSVerify.alloc () in
                                                                     
                                                                   let x_0_2522 = JSVerify.update x_0_2520 "0" (JSVerify.select x_0_2517 "evt") in
                                                                     x_0_2520) in
                                                                 JSVerify.Undef)))) in
                        
                      let x_0_2531 = JSVerify.apply_hint<(Meta_named "onmousemove" (Meta_tid 2))> 
                        (JSVerify.select (JSVerify.select (JSVerify.Obj JSVerify.global) "body") "onmousemove") 
                        (JSVerify.select (JSVerify.Obj JSVerify.global) "body") (
                          let x_0_2527 = JSVerify.alloc () in
                            
                          let x_0_2529 = JSVerify.update x_0_2527 "0" (JSVerify.select (JSVerify.Obj JSVerify.global) "dummyEvent") in
                            x_0_2527) in
                        JSVerify.Undef 
                    else JSVerify.Undef in
                  JSVerify.Undef)

   
