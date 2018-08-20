module Bug606

////////////////////////////////////////////////////////////////////////////////
//minimalistic
////////////////////////////////////////////////////////////////////////////////
let t (a:nat) = int
let test (x:t 0) : t 1 = x


////////////////////////////////////////////////////////////////////////////////
//A slightly larger example
////////////////////////////////////////////////////////////////////////////////
open FStar.UInt

#set-options "--print_universes --log_types"

(*
 In FStar.UInt: 
 type uint_t (n:pos) = x:int{size x n}

 In FStar.UInt64:
 val v        : t -> Tot (uint_t n)
 val uint_to_t: uint_t n -> Pure t
 *)

let n:pos = 32

val uint64_to_uint32: m:UInt64.t{fits (UInt64.v m) n} -> Tot FStar.UInt32.t
let uint64_to_uint32 m =
  let m': x:int{size x n} = UInt64.v m in
  UInt32.uint_to_t m'

//With this uncommented, uint64_to_uint32' below typechecks 
//type uint_t (n:pos) = x:int{size x n}

val uint64_to_uint32': m:UInt64.t{fits (UInt64.v m) n} -> Tot FStar.UInt32.t
let uint64_to_uint32' m =
  cut (uint_t n == x:int{size x n});
  cut (forall (p:uint_t n). p:(x:int{size x n}));
  let m':uint_t n = UInt64.v m in // This fails, even if the above is provable
  UInt32.uint_to_t m'
