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

module Fibo32
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --fuel 2 --ifuel 2"


let rec fib (n:nat) : nat =
  if n <= 1 then 1
  else fib (n - 1) + fib (n - 2)

let rec fib_mono (n:nat) (m:nat { m <= n})
  : Lemma
    (ensures fib m <= fib n)
  = if n = m then ()
    else fib_mono (n - 1) m

open Pulse.Lib.BoundedIntegers

#push-options "--z3rlimit_factor 4"
```pulse
fn fibo32 (k:U32.t) (_:squash(0ul < k /\ fits #U32.t (fib (v k))))
  requires emp
  returns r:U32.t
  ensures pure (v r == fib (v k))
{
  let mut i = 1ul;
  let mut j = 1ul;
  let mut ctr = 1ul;
  while (let vctr = !ctr; (vctr < k))
  invariant b . exists* vi vj vctr. (
     pts_to i vi **
     pts_to j vj **
     pts_to ctr vctr **     
     pure (1ul <= vctr /\
           vctr <= k /\
           fib (v vctr - 1) == v vi/\
           fib (v vctr) == v vj /\
           b == (vctr < k))
  )
  {
     let vc = !ctr;
     let vi = !i;
     let vj = !j;
     ctr := vc + 1ul;
     i := vj;
     fib_mono (v k) (v vc + 1);
     j := vi + vj;
     ()
  };
  let r = !j;
  r
}
```

