module Pulse.Lib.Deque

open Pulse
open FStar.List.Tot

new
val deque (t:Type0) : Type0

val is_deque #t (x:deque t) (l:list t)
  : Tot slprop

```pulse
val
fn mk_empty (#t:Type) (_:unit)
  requires emp
  returns  p : deque t
  ensures  is_deque p []
```

```pulse
val
fn push_front (#t:Type) (l : deque t) (x : t)
  (#xs:erased (list t))
  requires is_deque l xs
  returns  l' : deque t
  ensures  is_deque l' (x::xs)
```

```pulse
val
fn pop_front (#t:Type) (l : deque t)
  (#x : erased t)
  (#xs : erased (list t))
  requires is_deque l (reveal x :: xs)
  returns  l'x : (deque t & t)
  ensures  is_deque (fst l'x) xs ** pure (snd l'x == x)
```

```pulse
val
fn push_back (#t:Type) (l : deque t) (x : t)
  (#xs:erased (list t))
  requires is_deque l xs
  returns  l' : deque t
  ensures  is_deque l' (xs @ [x])
```

```pulse
val
fn pop_back (#t:Type) (l : deque t)
  (#x : erased t)
  (#xs : erased (list t))
  requires is_deque l (xs @ [reveal x])
  returns  l'x : (deque t & t)
  ensures  is_deque (fst l'x) xs ** pure (snd l'x == x)
```
