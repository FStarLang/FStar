module PulseTutorial.HigherOrder
open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
```pulse //apply$
fn apply (#a:Type0)
         (#b:a -> Type0)
         (#pre:a -> vprop)
         (#post: (x:a -> b x -> vprop))
         (f: (x:a -> stt (b x) (pre x) (fun y -> post x y)))
         (x:a)
requires pre x
returns y:b x
ensures post x y
{
  f x
}
```

```pulse //apply_ghost$
ghost
fn apply_ghost 
         (#a:Type0)
         (#b:a -> Type0)
         (#pre:a -> vprop)
         (#post: (x:a -> b x -> vprop))
         (f: (x:a -> stt_ghost (b x) emp_inames (pre x) (fun y -> post x y)))
         (x:a)
requires pre x
returns y:b x
ensures post x y
{
  f x
}
```

let id_t = (#a:Type0) -> x:a -> stt a emp (fun _ -> emp)

```pulse
fn id ()
: id_t 
= (#a:Type0) (x:a) { x }
```

let id_t_a (a:Type0) = x:a -> stt a emp (fun _ -> emp)

[@@expect_failure] //FIXME! This should work!
```pulse
fn id_a (a:Type0)
: id_t_a a 
= (x:a) { x }
```

```pulse
fn id_a (a:Type0)
requires emp
returns f:id_t_a a 
ensures emp
{
  fn aux (x:a)
  requires emp
  returns y:a
  ensures emp 
  { 
    x 
};
  aux
}
```


//ctr$
noeq
type ctr = {
    inv: int -> vprop;
    next: i:erased int -> stt int (inv i) (fun y -> inv (i + 1) ** pure (y == reveal i));
    destroy: i:erased int -> stt unit (inv i) (fun _ -> emp)
}
//ctr$
let next c = c.next
let destroy c = c.destroy

```pulse //new_counter$
fn new_counter ()
requires emp
returns c:ctr
ensures c.inv 0
{
    open Pulse.Lib.Box;
    let x = alloc 0;
    fn next (i:erased int)
    requires pts_to x i 
    returns j:int
    ensures pts_to x (i + 1) ** pure (j == reveal i)
    {
        let j = !x;
        x := j + 1;
        j
    };
    fn destroy (i:erased int)
    requires pts_to x i
    ensures emp
    {
       free x
    };
    let c = { inv = pts_to x; next; destroy };
    rewrite (pts_to x 0) as (c.inv 0);
    c
}
```

```pulse
fn return (#a:Type0) (x:a)
requires emp
returns y:a
ensures pure (x == y)
{
    x
}
```


```pulse //test_counter$
fn test_counter ()
requires emp
ensures emp
{
    let c = new_counter ();
    let x = next c _; //FIXME: Should be able to write c.next
    assert pure (x == 0);
    let x = next c _;
    assert pure (x == 1);
    destroy c _;
}
```