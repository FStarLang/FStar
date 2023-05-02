module CustomSyntax
module PM = Pulse.Main

```pulse
fn fibonacci(n:nat)
  requires emp
  returns  _ : nat
  ensures emp
 {
   let mut i0 = 1;
   let mut i1 = 1;
   let mut ctr = 1;   
   while (ctr < n) 
   invariant exists (n:pos). (pts_to ctr n * pts_to i1 (fib_spec n) * pts_to i0 (fib_spec (n - 1)))
   {
      let tmp = i0;
      i0 := i1;
      i1 := (tmp + i0);
      ctr := (ctr + 1)
   };
   i1
}
```

```pulse
fn add (x y: int)
  requires (pts_to x a * pts_to y b)
  returns r:int
  ensures (pts_to x a * pts_to y b * pure (r == a + b))
{
  (x + y)
}
```
