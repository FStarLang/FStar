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
module facepalm
 val main : unit -> DST JSVerify.dyn ((fun ('x_0_12617::(result JSVerify.dyn => (heap => E))) => (fun (x_0_12618:heap) => l_and (pf (DOM.InitialHeap x_0_12618)) (pf (Forall (result JSVerify.dyn) ((fun (x_0_12619:result JSVerify.dyn) => pf (Forall heap ((fun (x_0_12620:heap) => pf ('x_0_12617 x_0_12619 x_0_12620))))))))))) 

let  main = (fun (x_0_12621:unit) -> 
let x_0_12636 = JSVerify.update (JSVerify.Obj JSVerify.global) "cons" (JSVerify.mkFun<(Meta_tid 1)> "0,0" ((fun (x_0_12622:JSVerify.dyn) -> (fun (x_0_12623:JSVerify.dyn) -> 
let x_0_12625 = 
let x_0_12624 = JSVerify.alloc () in
 x_0_12624 in
 
let x_0_12627 = JSVerify.update x_0_12625 "a" (JSVerify.select x_0_12623 "0") in
 
let x_0_12629 = JSVerify.update x_0_12625 "rest" (JSVerify.select x_0_12623 "1") in
 
let x_0_12630 = JSVerify.alloc () in
 
let x_0_12632 = JSVerify.update x_0_12630 "hd" (JSVerify.select x_0_12625 "a") in
 
let x_0_12634 = JSVerify.update x_0_12630 "tl" (JSVerify.select x_0_12625 "rest") in
 x_0_12630)))) in
 
let x_0_12664 = JSVerify.update (JSVerify.Obj JSVerify.global) "getPath" (JSVerify.mkFun<(Meta_tid 2)> "0,59" ((fun (x_0_12637:JSVerify.dyn) -> (fun (x_0_12638:JSVerify.dyn) -> 
let x_0_12640 = 
let x_0_12639 = JSVerify.alloc () in
 x_0_12639 in
 
let x_0_12642 = JSVerify.update x_0_12640 "cur" (JSVerify.select x_0_12638 "0") in
 
let x_0_12644 = JSVerify.update x_0_12640 "path" (JSVerify.select x_0_12638 "1") in
 
let x_0_12662 = 
let x_0_12645 = get () in
 JSVerify._while ((fun (x_0_12647:unit) -> (JSVerify.Bool (JSVerify.land (
let x_0_12649 = JSVerify.refEqBool (JSVerify.select x_0_12640 "path") JSVerify.Undef in
 if x_0_12649 then (JSVerify.Bool false) 
 else (JSVerify.Bool true)) (
let x_0_12651 = JSVerify.refEqBool (JSVerify.select x_0_12640 "cur") JSVerify.Undef in
 if x_0_12651 then (JSVerify.Bool false) 
 else (JSVerify.Bool true)))))) ((fun (x_0_12653:unit) -> 
let x_0_12658 = JSVerify.update x_0_12640 "cur" (JSVerify.apply (JSVerify.select (JSVerify.select x_0_12640 "cur") "getChild") (JSVerify.select x_0_12640 "cur") (
let x_0_12654 = JSVerify.alloc () in
 
let x_0_12656 = JSVerify.update x_0_12654 "0" (JSVerify.select (JSVerify.select x_0_12640 "path") "hd") in
 x_0_12654)) in
 
let x_0_12660 = JSVerify.update x_0_12640 "path" (JSVerify.select (JSVerify.select x_0_12640 "path") "tl") in
 JSVerify.Undef)) in
 JSVerify.Undef)))) in
 
let x_0_12682 = JSVerify.update (JSVerify.Obj JSVerify.global) "findName" (JSVerify.mkFun<(Meta_tid 3)> "0,238" ((fun (x_0_12665:JSVerify.dyn) -> (fun (x_0_12666:JSVerify.dyn) -> 
let x_0_12668 = 
let x_0_12667 = JSVerify.alloc () in
 x_0_12667 in
 
let x_0_12673 = JSVerify.update x_0_12668 "elts" (JSVerify.apply (JSVerify.select (JSVerify.select (JSVerify.Obj JSVerify.global) "document") "getElementsByTagName") (JSVerify.select (JSVerify.Obj JSVerify.global) "document") (
let x_0_12669 = JSVerify.alloc () in
 
let x_0_12671 = JSVerify.update x_0_12669 "0" (JSVerify.Str "title") in
 x_0_12669)) in
 
let x_0_12676 = JSVerify.update x_0_12668 "elt" (JSVerify.apply (JSVerify.select (JSVerify.select x_0_12668 "elts") "Next") (JSVerify.select x_0_12668 "elts") (
let x_0_12674 = JSVerify.alloc () in
 x_0_12674)) in
 
let x_0_12680 = 
let x_0_12678 = JSVerify.coerceBool (JSVerify.select x_0_12668 "elt") in
 if x_0_12678 then JSVerify.select (JSVerify.select x_0_12668 "elt") "text" 
 else JSVerify.Undef in
 JSVerify.Undef)))) in
 
let x_0_12748 = JSVerify.update (JSVerify.Obj JSVerify.global) "getWebsite" (JSVerify.mkFun<(Meta_tid 4)> "0,400" ((fun (x_0_12683:JSVerify.dyn) -> (fun (x_0_12684:JSVerify.dyn) -> 
let x_0_12686 = 
let x_0_12685 = JSVerify.alloc () in
 x_0_12685 in
 
let x_0_12688 = JSVerify.update x_0_12686 "node1" (JSVerify.select x_0_12684 "0") in
 
let x_0_12746 = 
let x_0_12690 = JSVerify.coerceBool (JSVerify.select x_0_12686 "node1") in
 if x_0_12690 then 
let x_0_12695 = JSVerify.update x_0_12686 "node" (JSVerify.apply (JSVerify.select (JSVerify.select x_0_12686 "node1") "getChild") (JSVerify.select x_0_12686 "node1") (
let x_0_12691 = JSVerify.alloc () in
 
let x_0_12693 = JSVerify.update x_0_12691 "0" (JSVerify.Num 0.000000) in
 x_0_12691)) in
 
let x_0_12744 = 
let x_0_12697 = JSVerify.coerceBool (JSVerify.select x_0_12686 "node") in
 if x_0_12697 then 
let x_0_12742 = 
let x_0_12699 = JSVerify.coerceBool (JSVerify.Bool (JSVerify.land (JSVerify.refEq (JSVerify.select (JSVerify.select x_0_12686 "node") "nodeType") (JSVerify.Num 3.000000)) (JSVerify.refEq (JSVerify.select (JSVerify.select x_0_12686 "node") "nodeValue") (JSVerify.Str "Website")))) in
 if x_0_12699 then 
let x_0_12701 = JSVerify.update x_0_12686 "node11" (JSVerify.select x_0_12686 "node") in
 
let x_0_12704 = JSVerify.update x_0_12686 "node2" (JSVerify.apply (JSVerify.select (JSVerify.select x_0_12686 "node11") "getParent") (JSVerify.select x_0_12686 "node11") (
let x_0_12702 = JSVerify.alloc () in
 x_0_12702)) in
 
let x_0_12726 = JSVerify.update x_0_12686 "path" (JSVerify.apply_hint<(Meta_tid 1)> (JSVerify.select (JSVerify.Obj JSVerify.global) "cons") (JSVerify.Obj JSVerify.global) (
let x_0_12705 = JSVerify.alloc () in
 
let x_0_12707 = JSVerify.update x_0_12705 "0" (JSVerify.Num 1.000000) in
 
let x_0_12724 = JSVerify.update x_0_12705 "1" (JSVerify.apply_hint<(Meta_tid 1)> (JSVerify.select (JSVerify.Obj JSVerify.global) "cons") (JSVerify.Obj JSVerify.global) (
let x_0_12708 = JSVerify.alloc () in
 
let x_0_12710 = JSVerify.update x_0_12708 "0" (JSVerify.Num 0.000000) in
 
let x_0_12722 = JSVerify.update x_0_12708 "1" (JSVerify.apply_hint<(Meta_tid 1)> (JSVerify.select (JSVerify.Obj JSVerify.global) "cons") (JSVerify.Obj JSVerify.global) (
let x_0_12711 = JSVerify.alloc () in
 
let x_0_12713 = JSVerify.update x_0_12711 "0" (JSVerify.Num 0.000000) in
 
let x_0_12720 = JSVerify.update x_0_12711 "1" (JSVerify.apply_hint<(Meta_tid 1)> (JSVerify.select (JSVerify.Obj JSVerify.global) "cons") (JSVerify.Obj JSVerify.global) (
let x_0_12714 = JSVerify.alloc () in
 
let x_0_12716 = JSVerify.update x_0_12714 "0" (JSVerify.Num 0.000000) in
 
let x_0_12718 = JSVerify.update x_0_12714 "1" JSVerify.Undef in
 x_0_12714)) in
 x_0_12711)) in
 x_0_12708)) in
 x_0_12705)) in
 
let x_0_12733 = JSVerify.update x_0_12686 "node3" (JSVerify.apply_hint<(Meta_tid 2)> (JSVerify.select (JSVerify.Obj JSVerify.global) "getPath") (JSVerify.Obj JSVerify.global) (
let x_0_12727 = JSVerify.alloc () in
 
let x_0_12729 = JSVerify.update x_0_12727 "0" (JSVerify.select x_0_12686 "node2") in
 
let x_0_12731 = JSVerify.update x_0_12727 "1" (JSVerify.select x_0_12686 "path") in
 x_0_12727)) in
 
let x_0_12740 = 
let x_0_12735 = JSVerify.coerceBool (JSVerify.select x_0_12686 "node3") in
 if x_0_12735 then JSVerify.apply (JSVerify.select (JSVerify.select x_0_12686 "node3") "getAttribute") (JSVerify.select x_0_12686 "node3") (
let x_0_12736 = JSVerify.alloc () in
 
let x_0_12738 = JSVerify.update x_0_12736 "0" (JSVerify.Str "href") in
 x_0_12736) 
 else JSVerify.Undef in
 JSVerify.Undef 
 else JSVerify.Undef in
 JSVerify.Undef 
 else JSVerify.Undef in
 JSVerify.Undef 
 else JSVerify.Undef in
 JSVerify.Undef)))) in
 
let x_0_12778 = JSVerify.update (JSVerify.Obj JSVerify.global) "findWebsiteHelp" (JSVerify.mkFun<(Meta_tid 5)> "1,477" ((fun (x_0_12749:JSVerify.dyn) -> (fun (x_0_12750:JSVerify.dyn) -> 
let x_0_12752 = 
let x_0_12751 = JSVerify.alloc () in
 x_0_12751 in
 
let x_0_12754 = JSVerify.update x_0_12752 "elts" (JSVerify.select x_0_12750 "0") in
 
let x_0_12757 = JSVerify.update x_0_12752 "elt" (JSVerify.apply (JSVerify.select (JSVerify.select x_0_12752 "elts") "Next") (JSVerify.select x_0_12752 "elts") (
let x_0_12755 = JSVerify.alloc () in
 x_0_12755)) in
 
let x_0_12759 = JSVerify.update x_0_12752 "result" JSVerify.Undef in
 
let x_0_12776 = 
let x_0_12760 = get () in
 JSVerify._while ((fun (x_0_12762:unit) -> (JSVerify.Bool (JSVerify.land (
let x_0_12764 = JSVerify.refEqBool (JSVerify.select x_0_12752 "elt") JSVerify.Undef in
 if x_0_12764 then (JSVerify.Bool false) 
 else (JSVerify.Bool true)) (JSVerify.refEq (JSVerify.select x_0_12752 "result") JSVerify.Undef))))) ((fun (x_0_12766:unit) -> 
let x_0_12771 = JSVerify.update x_0_12752 "result" (JSVerify.apply_hint<(Meta_tid 4)> (JSVerify.select (JSVerify.Obj JSVerify.global) "getWebsite") (JSVerify.Obj JSVerify.global) (
let x_0_12767 = JSVerify.alloc () in
 
let x_0_12769 = JSVerify.update x_0_12767 "0" (JSVerify.select x_0_12752 "elt") in
 x_0_12767)) in
 
let x_0_12774 = JSVerify.update x_0_12752 "elt" (JSVerify.apply (JSVerify.select (JSVerify.select x_0_12752 "elts") "Next") (JSVerify.select x_0_12752 "elts") (
let x_0_12772 = JSVerify.alloc () in
 x_0_12772)) in
 JSVerify.Undef)) in
 JSVerify.select x_0_12752 "result")))) in
 
let x_0_12790 = JSVerify.update (JSVerify.Obj JSVerify.global) "findWebsite" (JSVerify.mkFun<(Meta_tid 6)> "2,211" ((fun (x_0_12779:JSVerify.dyn) -> (fun (x_0_12780:JSVerify.dyn) -> 
let x_0_12782 = 
let x_0_12781 = JSVerify.alloc () in
 x_0_12781 in
 JSVerify.apply_hint<(Meta_tid 5)> (JSVerify.select (JSVerify.Obj JSVerify.global) "findWebsiteHelp") (JSVerify.Obj JSVerify.global) (
let x_0_12783 = JSVerify.alloc () in
 
let x_0_12788 = JSVerify.update x_0_12783 "0" (JSVerify.apply (JSVerify.select (JSVerify.select (JSVerify.Obj JSVerify.global) "document") "getElementsByClassName") (JSVerify.select (JSVerify.Obj JSVerify.global) "document") (
let x_0_12784 = JSVerify.alloc () in
 
let x_0_12786 = JSVerify.update x_0_12784 "0" (JSVerify.Str "label") in
 x_0_12784)) in
 x_0_12783))))) in
 
let x_0_12805 = JSVerify.update (JSVerify.Obj JSVerify.global) "saveWebsite" (JSVerify.mkFun<(Meta_tid 7)> "2,314" ((fun (x_0_12791:JSVerify.dyn) -> (fun (x_0_12792:JSVerify.dyn) -> 
let x_0_12794 = 
let x_0_12793 = JSVerify.alloc () in
 x_0_12793 in
 
let x_0_12796 = JSVerify.update x_0_12794 "friend" (JSVerify.select x_0_12792 "0") in
 
let x_0_12798 = JSVerify.update x_0_12794 "href" (JSVerify.select x_0_12792 "1") in
 
let x_0_12803 = JSVerify.apply (JSVerify.select (JSVerify.Obj JSVerify.global) "consoleLog") (JSVerify.Obj JSVerify.global) (
let x_0_12799 = JSVerify.alloc () in
 
let x_0_12801 = JSVerify.update x_0_12799 "0" (JSVerify.Str "saving website...") in
 x_0_12799) in
 JSVerify.Undef)))) in
 
let x_0_12853 = JSVerify.update (JSVerify.Obj JSVerify.global) "start" (JSVerify.mkFun<(Meta_tid 8)> "3,55" ((fun (x_0_12806:JSVerify.dyn) -> (fun (x_0_12807:JSVerify.dyn) -> 
let x_0_12809 = 
let x_0_12808 = JSVerify.alloc () in
 x_0_12808 in
 
let x_0_12815 = 
let x_0_12811 = JSVerify.Undef in
 
let x_0_12813 = JSVerify.Undef in
 JSVerify.Undef in
 
let x_0_12851 = 
let x_0_12817 = JSVerify.refEqBool (JSVerify.select (JSVerify.select (JSVerify.Obj JSVerify.global) "document") "domain") (JSVerify.Str "facebook.com") in
 if x_0_12817 then 
let x_0_12820 = JSVerify.update x_0_12809 "friendName" (JSVerify.apply_hint<(Meta_tid 3)> (JSVerify.select (JSVerify.Obj JSVerify.global) "findName") (JSVerify.Obj JSVerify.global) (
let x_0_12818 = JSVerify.alloc () in
 x_0_12818)) in
 
let x_0_12823 = JSVerify.update x_0_12809 "href" (JSVerify.apply_hint<(Meta_tid 6)> (JSVerify.select (JSVerify.Obj JSVerify.global) "findWebsite") (JSVerify.Obj JSVerify.global) (
let x_0_12821 = JSVerify.alloc () in
 x_0_12821)) in
 
let x_0_12849 = 
let x_0_12825 = JSVerify.coerceBool (JSVerify.select x_0_12809 "href") in
 if x_0_12825 then 
let x_0_12830 = JSVerify.apply (JSVerify.select (JSVerify.Obj JSVerify.global) "consoleLog") (JSVerify.Obj JSVerify.global) (
let x_0_12826 = JSVerify.alloc () in
 
let x_0_12828 = JSVerify.update x_0_12826 "0" (JSVerify.opAddition (JSVerify.Str "Website on ") (JSVerify.select x_0_12809 "href")) in
 x_0_12826) in
 
let x_0_12835 = JSVerify.apply (JSVerify.select (JSVerify.Obj JSVerify.global) "consoleLog") (JSVerify.Obj JSVerify.global) (
let x_0_12831 = JSVerify.alloc () in
 
let x_0_12833 = JSVerify.update x_0_12831 "0" (JSVerify.opAddition (JSVerify.Str "Name is ") (JSVerify.select x_0_12809 "friendName")) in
 x_0_12831) in
 
let x_0_12842 = JSVerify.apply_hint<(Meta_tid 7)> (JSVerify.select (JSVerify.Obj JSVerify.global) "saveWebsite") (JSVerify.Obj JSVerify.global) (
let x_0_12836 = JSVerify.alloc () in
 
let x_0_12838 = JSVerify.update x_0_12836 "0" (JSVerify.select x_0_12809 "friendName") in
 
let x_0_12840 = JSVerify.update x_0_12836 "1" (JSVerify.select x_0_12809 "href") in
 x_0_12836) in
 JSVerify.Undef 
 else 
let x_0_12847 = JSVerify.apply (JSVerify.select (JSVerify.select (JSVerify.Obj JSVerify.global) "console") "log") (JSVerify.select (JSVerify.Obj JSVerify.global) "console") (
let x_0_12843 = JSVerify.alloc () in
 
let x_0_12845 = JSVerify.update x_0_12843 "0" (JSVerify.opAddition (JSVerify.select x_0_12809 "friendName") (JSVerify.Str " does not have a website")) in
 x_0_12843) in
 JSVerify.Undef in
 JSVerify.Undef 
 else JSVerify.Undef in
 JSVerify.Undef)))) in
 
let x_0_12856 = JSVerify.apply_hint<(Meta_tid 8)> (JSVerify.select (JSVerify.Obj JSVerify.global) "start") (JSVerify.Obj JSVerify.global) (
let x_0_12854 = JSVerify.alloc () in
 x_0_12854) in
 JSVerify.Undef)

 