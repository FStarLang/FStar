module PulseTutorial.Loops
open Pulse.Lib.Pervasives

```pulse //count_down$
fn count_down (x:ref nat)
requires pts_to x 'v
ensures pts_to x 0
{
    let mut keep_going = true;
    while (
        !keep_going
    )
    invariant b. 
      exists* v.
        pts_to keep_going b **
        pts_to x v **
        pure (b == false ==> v == 0)
    {
        let n = !x;
        if (n = 0) 
        {
            keep_going := false;
        } 
        else
        {
            x := n - 1;
        }
    }
}
```

```pulse //count_down2$
fn count_down2 (x:ref nat)
requires pts_to x 'v
ensures pts_to x 0
{
    while (
        let n = !x;
        if (n = 0)
        {
            false
        } 
        else
        {
            x := n - 1;
            true
        }
    )
    invariant b. 
      exists* v.
        pts_to x v **
        pure (b == false ==> v == 0)
    { () }
}
```

```pulse //count_down_loopy$
fn count_down_loopy (x:ref nat)
requires pts_to x 'v
ensures pts_to x 0
{
    while (
        let n = !x;
        if (n = 0)
        {
            false
        }
        else
        {
            x := n + 1;
            true
        }
    )
    invariant b. 
      exists* v.
        pts_to x v **
        pure (b == false ==> v == 0)
    { () }
}
```
open FStar.Mul

```pulse //multiply_by_repeated_addition$
fn multiply_by_repeated_addition (x y:nat)
    requires emp
    returns z:nat
    ensures pure (z == x * y)
{
    let mut ctr : nat = 0;
    let mut acc : nat = 0;
    while (
        let c = !ctr;
        (c < x)
    )
    invariant b.
    exists* c a.
        pts_to ctr c **
        pts_to acc a **
        pure (c <= x /\
              a == (c * y) /\
              b == (c < x))
    {
        let a = !acc;
        acc := a + y;
        let c = !ctr;
        ctr := c + 1;
    };
    !acc
}
```

//SNIPPET_START: sum$
let rec sum (n:nat)
: nat
= if n = 0 then 0 else n + sum (n - 1)

let rec sum_lemma (n:nat)
: Lemma (sum n == n * (n + 1) / 2)
= if n = 0 then ()
  else sum_lemma (n - 1)
//SNIPPET_END: sum$

//SNIPPET_START: isum$
#push-options "--z3cliopt 'smt.arith.nl=false'"
```pulse
fn isum (n:nat)
requires emp
returns z:nat
ensures pure ((n * (n + 1) / 2) == z)
{
    let mut acc : nat = 0;
    let mut ctr : nat = 0;
    while (
        let c = !ctr;
        (c < n)
    )
    invariant b.
    exists* c a.
        pts_to ctr c **
        pts_to acc a **
        pure (c <= n /\
              a == sum c /\
              b == (c < n))
    {
        let a = !acc;
        let c = !ctr;
        ctr := c + 1;
        acc := a + c + 1;
    };
    sum_lemma n; //call an F* lemma inside Pulse
    !acc;
}
```
#pop-options
//SNIPPET_END: isum$

let rec fib (n:nat) : nat =
  if n <= 1 then 1
  else fib (n - 1) + fib (n - 2)

let rec fib_mono (n:nat) (m:nat { m <= n})
  : Lemma
    (ensures fib m <= fib n)
  = if n = m then ()
    else fib_mono (n - 1) m

open FStar.UInt32
open Pulse.Lib.BoundedIntegers
module U32 = FStar.UInt32


```pulse
fn fibonacci32 (k:U32.t)
  requires pure (0ul < k /\ fib (v k) < pow2 32)
  returns r:U32.t
  ensures pure (v r == fib (v k))
{
  let mut i = 1ul;
  let mut j = 1ul;
  let mut ctr = 1ul;
  while (
    let c = !ctr;
    (c < k)
  )
  invariant b . 
    exists* vi vj vctr. 
     pts_to i vi **
     pts_to j vj **
     pts_to ctr vctr **
     pure (1ul <= vctr /\
           vctr <= k /\
           fib (v (vctr - 1ul)) == v vi/\
           fib (v vctr) == v vj /\
           b == (vctr < k))
  {
     let vi = !i;
     let vj = !j;
     let c = !ctr;
     fib_mono (v k) (v c + 1);
     ctr := c + 1ul;
     i := vj;
     j := vi + vj;
  };
  !j
}
```
