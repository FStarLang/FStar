module Pulse.Lib.Primitives

let read_atomic (r:ref U32.t) (#n:erased U32.t) (#p:perm)
: stt_atomic U32.t emp_inames
    (pts_to r #p n)
    (fun x -> pts_to r #p n ** pure (reveal n == x))
= Pulse.Lib.Core.as_atomic _ _ ((let open Pulse.Lib.Reference in ( ! )) r #n #p)

let write_atomic (r:ref U32.t) (x:U32.t) (#n:erased U32.t)
= Pulse.Lib.Core.as_atomic _ _ ((let open Pulse.Lib.Reference in ( := )) r x #n)

```pulse
fn cas_impl
    (r:ref U32.t)
    (u v:U32.t)
    (#i:erased U32.t)
requires
  pts_to r i
returns b:bool
ensures
  cond b (pts_to r v ** pure (reveal i == u)) 
         (pts_to r i)
{
  let u' = !r;
  if (u = u')
  {
    r := v;
    fold (cond true (pts_to r v ** pure (reveal i == u)) (pts_to r i));
    true
  }
  else
  {
    fold cond false (pts_to r v ** pure (reveal i == u)) (pts_to r i);
    false
  }
}
```

let cas r u v #i = Pulse.Lib.Core.as_atomic _ _ (cas_impl r u v #i)
