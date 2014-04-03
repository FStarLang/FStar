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
module Map

(* Static semantics  *)
type map
logic val DefaultVal : 'b:S -> 'b
logic val Emp : map
logic val Sel : 'a:S -> 'b:S -> map -> 'a -> 'b
logic val Concat : map -> map -> map
logic val Singleton : 'a:S -> 'b:S -> 'a -> 'b -> map
type In : 'a:S => map => 'a => E
type Equal : map => map => E
logic val Upd : 'a:S -> 'b:S -> map -> 'a -> 'b -> map
define Upd_def: forall ('a:S) ('b:S) (g:map) (x:'a) (t:'b). 
        Upd 'a 'b g x t = Concat g (Singleton 'a 'b x t)

assume InEmp: forall ('a:S) (a:'a).{:pattern (In 'a Emp a)} not(In 'a Emp a)
assume InSingleton: forall ('a:S) ('b:S) (x:'a) (t:'b).{:pattern (Singleton 'a 'b x t)}
              In 'a (Singleton 'a 'b x t) x
assume InSingletonInv: forall ('a:S) ('b:S) ('c:S) (x:'a) (t:'b) (y:'c).{:pattern (In 'c (Singleton 'a 'b x t) y)}
                          In 'c (Singleton 'a 'b x t) y <==> x=y
assume InConcat: forall ('a:S) g1 g2 (x:'a).{:pattern (In 'a (Concat g1 g2) x)}
                          In 'a (Concat g1 g2) x <==> In 'a g1 x \/ In 'a g2 x
assume InConcatL: forall ('a:S) g1 g2 (x:'a).{:pattern (Concat g1 g2); (In 'a g1 x)}
                          In 'a g1 x ==> In 'a (Concat g1 g2) x
assume InConcatR: forall ('a:S) g1 g2 (x:'a).{:pattern (Concat g1 g2); (In 'a g2 x)}
                          In 'a g2 x ==> In 'a (Concat g1 g2) x
assume ConcatEmp: forall g.{:pattern (Concat g Emp)} Concat g Emp = g
assume ConcatIdemL: forall a b.{:pattern (Concat (Concat a b) b)} Concat (Concat a b) b = Concat a b
assume ConcatIdemR: forall a b.{:pattern (Concat a (Concat a b))} Concat a (Concat a b) = Concat a b
assume ConcatAssocR: forall a b c.{:pattern (Concat (Concat a b) c)} Concat (Concat a b) c = Concat a (Concat b c)
assume SelSingleton: forall ('a:S) ('b:S) (x:'a) (t:'b).{:pattern (Sel 'a 'b (Singleton 'a 'b x t) x)} Sel 'a 'b (Singleton 'a 'b x t) x = t
assume SelConcatL: forall ('a:S) ('b:S) g1 g2 (x:'a).{:pattern (Sel 'a 'b (Concat g1 g2) x)} In 'a g2 x ==> Sel 'a 'b (Concat g1 g2) x = Sel 'a 'b g2 x
assume SelConcatR: forall ('a:S) ('b:S) g1 g2 (x:'a).{:pattern (Sel 'a 'b (Concat g1 g2) x)} not(In 'a g2 x) ==> Sel 'a 'b (Concat g1 g2) x = Sel 'a 'b g1 x
assume SelNotIn: forall ('a:S) ('b:S) g (x:'a).{:pattern (Sel 'a 'b g x)} not(In 'a g x) ==> Sel 'a 'b g x = DefaultVal 'b
assume MapEqualDef: forall g1 g2.{:pattern (Equal g1 g2)} (forall ('a:S) ('b:S) (x:'a). Sel 'a 'b g1 x = Sel 'a 'b g2 x) <==> Equal g1 g2
assume MapEqualExt: forall g1 g2.{:pattern (Equal g1 g2)} Equal g1 g2 ==> g1=g2

val contains: e:map -> x:'a -> b:bool{b=true <==> In 'a e x}
(* TODO *)

val fresh: g:map -> x:string{not(In string g x)}
(* TODO *)
