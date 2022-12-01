module ContextPollution

let warmup (x:bool { x == true }) = assert x

//SNIPPET_START: context_test1$
module T = FStar.Tactics
module B = LowStar.Buffer
module SA = Steel.Array
open FStar.Seq

#push-options "--query_stats"
let warmup1 (x:bool { x == true }) = assert x

let test1 (a:Type) (s0 s1 s2: seq a)
  : Lemma (Seq.append (Seq.append s0 s1) s2 `Seq.equal`
           Seq.append s0 (Seq.append s1 s2))
  = ()
//SNIPPET_END: context_test1$


//SNIPPET_START: using_facts$
#push-options "--using_facts_from 'Prims FStar.Seq'"
let warmup2 (x:bool { x == true }) = assert x

let test2 (a:Type) (s0 s1 s2: seq a)
  : Lemma (Seq.append (Seq.append s0 s1) s2 `Seq.equal`
           Seq.append s0 (Seq.append s1 s2))
  = ()
//SNIPPET_END: using_facts$  

