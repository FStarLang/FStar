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
module RefSet

type refset
logic val EmptySet : refset
logic val Singleton : ref 'a -> refset
logic val Union : refset -> refset -> refset
logic val Intersection : refset -> refset -> refset
logic val Difference: refset -> refset -> refset
logic val Complement: refset -> refset
type InSet : 'a:S => refset => ref 'a => E
type SetEqual : refset => refset => E
type Disjoint : refset => refset => E

assume InEmptySet: forall a.{:pattern (InSet EmptySet a)} not(InSet EmptySet a)
assume InSingleton: forall a.{:pattern (Singleton a)} InSet (Singleton a) a
assume InSingletonInv: forall a b.{:pattern (InSet (Singleton b) a)} 
                          InSet (Singleton b) a <==> (Eq2 a b)
assume InComplement: forall s a.{:pattern (InSet (Complement s) a)} InSet (Complement s) a <==> Not(InSet s a)
assume CompTwice: forall s.{:pattern (Complement (Complement s))} (Complement (Complement s) = s)
assume InUnion: forall s1 s2 a.{:pattern (InSet (Union s1 s2) a)}  
                          InSet (Union s1 s2) a <==> (InSet s1 a \/ InSet s2 a)
assume InUnionL: forall s1 s2 a.{:pattern (Union s1 s2); (InSet s1 a)}
                          InSet s1 a ==> InSet (Union s1 s2) a
assume InUnionR: forall s1 s2 a.{:pattern (Union s1 s2); (InSet s2 a)}
                         InSet s2 a ==> InSet (Union s1 s2) a
assume DisjointDiffUnion: forall a b.{:pattern (Union a b)} Disjoint a b 
             ==> (Difference (Union a b) a = b 
                  /\ Difference (Union a b) b = a)
assume InInter: forall a b o.{:pattern (InSet (Intersection a b) o)} 
                 (InSet (Intersection a b) o <==> (InSet a o /\ InSet b o))
assume UnionIdemL: forall a b.{:pattern (Union (Union a b) b)} (Union (Union a b) b = Union a b)
assume UnionIdemR: forall a b.{:pattern (Union a (Union a b))} (Union a (Union a b) = Union a b)
assume InterIdemL: forall a b.{:pattern (Intersection (Intersection a b) b)} (Intersection (Intersection a b) b = Intersection a b)
assume InterIdemR: forall a b.{:pattern (Intersection a (Intersection a b))} (Intersection a (Intersection a b) = Intersection a b)
assume InDiff: forall a b o.{:pattern (InSet (Difference a b) o)} (InSet (Difference a b) o <==> (InSet a o /\ not(InSet b o)))
assume InDiffInv: forall a b y.{:pattern (Difference a b); (InSet b y)} (InSet b y ==> not(InSet (Difference a b) y))
assume Disjoint_def: forall (a:refset) (b:refset).{:pattern (Disjoint a b)} 
                  (Disjoint a b <==> 
                     (forall ('a:S) (o:ref 'a). {:pattern (InSet a o); (InSet b o)} (not(InSet a o) \/ not(InSet b o))))
assume SetEqualDef: forall s1 s2.{:pattern (SetEqual s1 s2)} 
                  (SetEqual s1 s2 <==> 
                     (forall ('a:S) (a:ref 'a).{:pattern (InSet s1 a); (InSet s2 a)} InSet s1 a <==> InSet s2 a))
assume SetEqualExt: forall s1 s2.{:pattern (SetEqual s1 s2)} SetEqual s1 s2 ==> s1=s2 

