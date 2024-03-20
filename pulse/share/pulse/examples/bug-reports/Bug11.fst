module Bug11

open FStar.Seq
open Pulse.Lib.Pervasives

// Some proposition that is trivially provable using an SMTPat from FStar.Seq.Base
let tru: prop = Seq.seq_to_list (Seq.seq_of_list ([42])) == [42]
let tru_intro () : Lemma tru = ()

let f (n: nat{tru}) : nat = 42

// The postcondition of `g` now typechecks if we have facts from FStar.Seq.Base
```pulse
fn g () requires emp returns n:nat ensures pure (f n == 42) {
  42
}
```

#set-options "--using_facts_from '-FStar.Seq'"

let h' () = g () // works

```pulse
fn h ()
  requires emp
  returns n:nat
  ensures emp
{
  let n = g (); // used to fail because the postcondition of `g` didn't typecheck
  n
}
```
