module Example.BreakReturnContinue
#lang-pulse
open Pulse
module SZ = FStar.SizeT

fn find_element (#a:eqtype) (x:array a) (len:SZ.t) (v:a) #p
preserves live x #p
requires pure (Seq.mem v (value_of x))
requires pure (length x == SZ.v len)
returns i:SZ.t
ensures pure (
  SZ.v i < Seq.length (value_of x) /\
  Seq.index (value_of x) (SZ.v i) == v /\
  value_of x == old (value_of x)
)
{
  pts_to_len x;
  let mut i = 0sz;
  while (SZ.(!i <^ len))
  invariant live i
  invariant pure (
    SZ.v !i <= Seq.length (value_of x) /\
    (forall (j:nat). j < SZ.v !i ==> Seq.index (value_of x) j =!= v)
  )
  { 
     if (x.(!i) = v) { return !i; };
     i := !i `SZ.add` 1sz;
  };
  Seq.mem_index v (value_of x); 
  unreachable();
}

fn find_element_out_return (#a:eqtype) (x:array a) (len:SZ.t) (v:a) (res:ref SZ.t) #p
preserves live x #p
preserves live res
requires pure (Seq.mem v (value_of x))
requires pure (length x == SZ.v len)
ensures pure (
  SZ.v !res < Seq.length (value_of x) /\
  Seq.index (value_of x) (SZ.v !res) == v /\
  value_of x == old (value_of x)
)
{
  pts_to_len x;
  let mut i = 0sz;
  while (SZ.(!i <^ len))
  invariant live i
  invariant pure (
    SZ.v !i <= Seq.length (value_of x) /\
    (forall (j:nat). j < SZ.v !i ==> Seq.index (value_of x) j =!= v)
  )
  { 
     if (x.(!i) = v) { res := !i; return; };
     i := !i `SZ.add` 1sz;
  };
  Seq.mem_index v (value_of x); 
  unreachable();
}

//In more explicit form:
fn find_element_out_return_explicit (#a:eqtype) (x:array a) (len:SZ.t) (v:a) (res:ref SZ.t) #p
preserves live x #p
preserves live res
requires pure (Seq.mem v (value_of x))
requires pure (length x == SZ.v len)
ensures pure (
  SZ.v !res < Seq.length (value_of x) /\
  Seq.index (value_of x) (SZ.v !res) == v /\
  value_of x == old (value_of x)
)
{
  pts_to_len x;
  let vres = value_of res;
  let mut i = 0sz;
  while (SZ.(!i <^ len))
  invariant live i
  invariant res |-> vres //note the invariant says that the res is unchanged
  invariant pure (
    SZ.v !i <= Seq.length (value_of x) /\
    (forall (j:nat). j < SZ.v !i ==> Seq.index (value_of x) j =!= v)
  )
  { 
     if (x.(!i) = v) { 
      res := !i;
      //but at the return we only need to prove the postcondition of the entire function
      //so we can mutate res and break the invariant
      return; 
    };
     i := !i `SZ.add` 1sz;
  };
  Seq.mem_index v (value_of x); 
  unreachable();
}

fn find_element_out_with_break (#a:eqtype) (x:array a) (len:SZ.t) (v:a) (res:ref SZ.t) (#p:perm)
preserves live x #p
preserves live res
requires pure (Seq.mem v (value_of x))
requires pure (length x == SZ.v len)
ensures pure (
  SZ.v !res < Seq.length (value_of x) /\
  Seq.index (value_of x) (SZ.v !res) == v /\
  value_of x == old (value_of x)
)
{
  pts_to_len x;
  let mut i = 0sz;
  while (SZ.(!i <^ len))
  invariant live i
  //we need to add `live res` to the invariant to give us permission to change it
  //without it, you get a mysterious error message at the break
  invariant live res 
  invariant pure (
    SZ.v !i <= Seq.length (value_of x) /\
    (forall (j:nat). j < SZ.v !i ==> Seq.index (value_of x) j =!= v)
  )
  ensures (SZ.v !res < Seq.length (value_of x) /\ Seq.index (value_of x) (SZ.v !res) == v)
  { 
    if (x.(!i) = v) { 
      res := !i;
      //because at the break, we still have to prove the invariant
      //and the ensures clause
      break;
    };
     i := !i `SZ.add` 1sz;
  };
  Seq.mem_index v (value_of x);
  assert pure (SZ.v !i < SZ.v len); //exclude the normal loop exit
}

fn sum_non_neg (x:array int) (len:SZ.t)
preserves live x
requires pure (length x == SZ.v len)
returns i:nat
ensures pure (
  value_of x == old (value_of x)
)
{
  pts_to_len x;
  let mut i = 0sz;
  let mut acc : nat = 0;
  while (SZ.(!i <^ len))
  invariant live i
  invariant live acc
  invariant pure (SZ.v !i <= Seq.length (value_of x))
  { 
     let vi = !i;
     i := !i `SZ.add` 1sz;
     if (x.(vi) < 0) { continue; };
     acc := !acc + x.(vi);
  };
  !acc;
}