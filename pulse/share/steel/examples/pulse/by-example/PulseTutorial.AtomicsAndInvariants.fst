module PulseTutorial.AtomicsAndInvariants
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32

//owns$
let owns (x:ref U32.t) = exists* v. pts_to x v
//owns$

```pulse //create_invariant$
fn create_invariant (r:ref U32.t) (v:erased U32.t)
requires pts_to r v
returns i:inv (owns r)
ensures emp
{
    fold owns;
    new_invariant (owns r)
}
```

let singleton #p (i:inv p) = add_inv emp_inames i

```pulse //update_ref_atomic$
atomic
fn update_ref_atomic (r:ref U32.t) (i:inv (owns r)) (v:U32.t)
requires emp
ensures emp
opens (singleton i)
{
  with_invariants i {    //owns r
     unfold owns;        //ghost step;  exists* u. pts_to r u
     write_atomic r v;   //atomic step; pts_to r v
     fold owns;          //ghost step;  owns r
  }
}
```

```pulse
ghost
fn pts_to_dup_impossible #a (x:ref a)
requires pts_to x 'v ** pts_to x 'u
ensures  pts_to x 'v ** pts_to x 'u ** pure False
{
    gather x;
    pts_to_perm_bound x;
    share x;    
}
```

//double_open_bad$
[@@expect_failure]
```pulse
fn double_open_bad (r:ref U32.t) (i:inv (owns r))
requires emp
ensures pure False
{
    with_invariants i {
      with_invariants i {
        unfold owns;
        unfold owns;
        pts_to_dup_impossible r;
        fold owns;
        fold owns
      }
    }
}
```
//double_open_bad$


```pulse //update_ref$
fn update_ref (r:ref U32.t) (i:inv (owns r)) (v:U32.t)
requires emp
ensures emp
{                    
  with_invariants i {    //owns r
     unfold owns;        //ghost step;  exists* u. pts_to r u
     write_atomic r v;   //atomic step; pts_to r v
     fold owns;          //ghost step;  owns r
  }
}
```

//update_ref_fail$
[@@expect_failure]
```pulse 
fn update_ref_fail (r:ref U32.t) (i:inv (owns r)) (v:U32.t)
requires emp
ensures emp
{
  with_invariants i {
    unfold owns;
    r := v; //not atomic
    fold owns;
  }
}
```
//update_ref_fail$



let readable (r:ref U32.t) = exists* p v. pts_to r #p v

```pulse //split_readable$
atomic
fn split_readable (r:ref U32.t) (i:inv (readable r))
requires emp
ensures readable r
opens (singleton i)
{
    with_invariants i {
        unfold readable;
        share r;
        fold readable;
        fold readable;
    };
}
```



