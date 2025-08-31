(*
   Copyright 2023 Microsoft Research

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

module UnificationVariableEscapes
#lang-pulse
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module US = FStar.SizeT
module R = Pulse.Lib.Reference


fn fill_array (#t:Type0) (a:A.array t) (l:(l:US.t { US.v l == A.length a })) (v:t)
              (#s:(s:Ghost.erased (Seq.seq t) { Seq.length s == A.length a }))
   requires (A.pts_to a s)
   ensures 
      exists* (s:Seq.seq t). (
         A.pts_to a s **
         pure (s `Seq.equal` Seq.create (US.v l) v)
      )
{
   let mut i = 0sz;
   while (let vi = !i; US.(vi <^ l))
   invariant exists* (s:Seq.seq t) (vi:US.t). ( 
      A.pts_to a s **
      R.pts_to i vi **
      pure (US.v vi <= US.v l /\
            Seq.length s == A.length a /\
            (forall (i:nat). i < US.v vi ==> Seq.index s i == v))
   )
   {
      let vi = !i; 
      (a.(vi) <- v);
      i := US.(vi +^ 1sz);
      ()
   };
   ()
}
