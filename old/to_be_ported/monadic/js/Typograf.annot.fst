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
module Typograf

 val main : unit -> DST JSVerify.dyn ((fun ('x_0_2467::(result JSVerify.dyn => (heap => E))) => (fun (x_0_2468:heap) => l_and (pf (DOM.InitialHeap x_0_2468)) (pf (Forall (result JSVerify.dyn) ((fun (x_0_2469:result JSVerify.dyn) => pf (Forall heap ((fun (x_0_2470:heap) => pf ('x_0_2467 x_0_2469 x_0_2470))))))))))) 

 let  main = (fun (x_0_2471:unit) -> 
                let x_0_2476 = JSVerify.update (JSVerify.Obj JSVerify.global) "saved_elt" (
                  let x_0_2472 = JSVerify.alloc () in
                    
                  let x_0_2474 = JSVerify.update x_0_2472 "value" JSVerify.Undef in
                    x_0_2472) in
                  
                let x_0_2505 = JSVerify.update (JSVerify.Obj JSVerify.global) "captureText" 
                  (JSVerify.mkFun<(Meta_named "captureText" (Meta_tid 1))> "0,34" 
                     ((fun (x_0_2477:JSVerify.dyn) -> (fun (x_0_2478:JSVerify.dyn) -> 
                                                         let x_0_2480 = 
                                                           let x_0_2479 = JSVerify.alloc () in
                                                             x_0_2479 in
                                                           
                                                         let x_0_2482 = JSVerify.update x_0_2480 "elt" (JSVerify.select x_0_2478 "0") in
                                                           
                                                         let x_0_2484 = JSVerify.update x_0_2480 "callback" (JSVerify.select x_0_2478 "1") in
                                                           
                                                         let x_0_2503 = 
                                                           let x_0_2486 = JSVerify.refEqBool (JSVerify.select (JSVerify.select x_0_2480 "elt") "tagName") (JSVerify.Str "INPUT") in
                                                             if x_0_2486 then 
                                                               let x_0_2488 = JSVerify.update (JSVerify.Obj JSVerify.global) "saved_elt" (JSVerify.select x_0_2480 "elt") in
                                                                 
                                                               let x_0_2496 = JSVerify.apply_hint<(Meta_named "addListenerCBTx" DOM.addListenerCBTx)> (JSVerify.select x_0_2480 "callback") (JSVerify.Obj JSVerify.global) (
                                                                 let x_0_2489 = JSVerify.alloc () in
                                                                   
                                                                 let x_0_2494 = JSVerify.update x_0_2489 "0" (
                                                                   let x_0_2490 = JSVerify.alloc () in
                                                                     
                                                                   let x_0_2492 = JSVerify.update x_0_2490 "text" (JSVerify.select (JSVerify.select x_0_2480 "elt") "value") in
                                                                     x_0_2490) in
                                                                   x_0_2489) in
                                                                 JSVerify.Undef 
                                                             else 
                                                               let x_0_2501 = JSVerify.apply_hint<(Meta_named "consoleLog" DOM.ConsoleLogTX)> (JSVerify.select (JSVerify.Obj JSVerify.global) "consoleLog") (JSVerify.Obj JSVerify.global) (
                                                                 let x_0_2497 = JSVerify.alloc () in
                                                                   
                                                                 let x_0_2499 = JSVerify.update x_0_2497 "0" (JSVerify.Str "Wrong kind of text, man") in
                                                                   x_0_2497) in
                                                                 JSVerify.Undef in
                                                           JSVerify.Undef)))) in
                  
                let x_0_2524 = JSVerify.update (JSVerify.Obj JSVerify.global) "pasteText" 
                  (JSVerify.mkFun<(Meta_named "pasteText" (Meta_tid 2))> "0,219" 
                     ((fun (x_0_2506:JSVerify.dyn) -> (fun (x_0_2507:JSVerify.dyn) -> 
                                                         let x_0_2509 = 
                                                           let x_0_2508 = JSVerify.alloc () in
                                                             x_0_2508 in
                                                           
                                                         let x_0_2511 = JSVerify.update x_0_2509 "text" (JSVerify.select x_0_2507 "0") in
                                                           
                                                         let x_0_2522 = 
                                                           let x_0_2513 = JSVerify.coerceBool (JSVerify.select (JSVerify.Obj JSVerify.global) "saved_elt") in
                                                             if x_0_2513 then 
                                                               let x_0_2515 = JSVerify.update (JSVerify.select (JSVerify.Obj JSVerify.global) "saved_elt") "value" (JSVerify.select x_0_2509 "text") in
                                                                 JSVerify.Undef 
                                                             else 
                                                               let x_0_2520 = JSVerify.apply_hint<(Meta_named "consoleLog" DOM.ConsoleLogTX)> (JSVerify.select (JSVerify.Obj JSVerify.global) "consoleLog") (JSVerify.Obj JSVerify.global) (
                                                                 let x_0_2516 = JSVerify.alloc () in
                                                                   
                                                                 let x_0_2518 = JSVerify.update x_0_2516 "0" (JSVerify.Str "nowhere to paste") in
                                                                   x_0_2516) in
                                                                 JSVerify.Undef in
                                                           JSVerify.Undef)))) in
                  
                let x_0_2557 = 
                  JSVerify.apply_hint_ex_witness'<(Meta_named "addListenerTx" DOM.addListenerTx), 
                                                  DOM.addListenerExTx,
                                                  (Meta_named "callback" (Meta_tid 3))>
                    (JSVerify.select (JSVerify.select (JSVerify.Obj JSVerify.global) "chrome") "addListener") 
                    (JSVerify.select (JSVerify.Obj JSVerify.global) "chrome") (
                      let x_0_2525 = JSVerify.alloc () in
                        
                      let x_0_2555 = JSVerify.update x_0_2525 "0" 
                        (JSVerify.mkFun<(Meta_named "callback" (Meta_tid 3))> "0,404" 
                           ((fun (x_0_2526:JSVerify.dyn) -> (fun (x_0_2527:JSVerify.dyn) -> 
                                                               let x_0_2529 = 
                                                                 let x_0_2528 = JSVerify.alloc () in
                                                                   x_0_2528 in
                                                                 
                                                               let x_0_2531 = JSVerify.update x_0_2529 "request" (JSVerify.select x_0_2527 "0") in
                                                                 
                                                               let x_0_2533 = JSVerify.update x_0_2529 "sender" (JSVerify.select x_0_2527 "1") in
                                                                 
                                                               let x_0_2535 = JSVerify.update x_0_2529 "callback" (JSVerify.select x_0_2527 "2") in
                                                                 
                                                               let x_0_2553 = 
                                                                 let x_0_2537 = JSVerify.refEqBool (JSVerify.select (JSVerify.select x_0_2529 "request") "command") (JSVerify.Str "captureText") in
                                                                   if x_0_2537 then 
                                                                     let x_0_2544 = JSVerify.apply_hint<(Meta_named "captureText" (Meta_tid 1))> (JSVerify.select (JSVerify.Obj JSVerify.global) "captureText") (JSVerify.Obj JSVerify.global) (
                                                                       let x_0_2538 = JSVerify.alloc () in
                                                                         
                                                                       let x_0_2540 = JSVerify.update x_0_2538 "0" (JSVerify.select (JSVerify.select (JSVerify.Obj JSVerify.global) "document") "activeElement") in
                                                                         
                                                                       let x_0_2542 = JSVerify.update x_0_2538 "1" (JSVerify.select x_0_2529 "callback") in
                                                                         x_0_2538) in
                                                                       JSVerify.Undef 
                                                                   else 
                                                                     let x_0_2546 = JSVerify.refEqBool (JSVerify.select (JSVerify.select x_0_2529 "request") "command") (JSVerify.Str "pasteText") in
                                                                       if x_0_2546 then 
                                                                         let x_0_2551 = JSVerify.apply_hint<(Meta_named "pasteText" (Meta_tid 2))> (JSVerify.select (JSVerify.Obj JSVerify.global) "pasteText") (JSVerify.Obj JSVerify.global) (
                                                                           let x_0_2547 = JSVerify.alloc () in
                                                                             
                                                                           let x_0_2549 = JSVerify.update x_0_2547 "0" (JSVerify.select (JSVerify.select x_0_2529 "request") "text") in
                                                                             x_0_2547) in
                                                                           JSVerify.Undef 
                                                                       else JSVerify.Undef in
                                                                 JSVerify.Undef)))) in
                        x_0_2525) in
                  JSVerify.Undef)
   
   
