module Pulse.Class.BoundedIntegers

module TC = FStar.Tactics.Typeclasses

let fits_t (fits:int -> prop) = x:int { fits x }

class bounded_int (t:eqtype) = {
    fits: int -> prop;
    v : t -> GTot int;
    u : fits_t fits -> GTot t;
    ( + ) : (x:t -> y:t -> Pure t (requires fits (v x + v y)) (ensures fun z -> v z == v x + v y));
    op_Subtraction : (x:t -> y:t -> Pure t (requires fits (v x - v y)) (ensures fun z -> v z == v x - v y));
    ( < ) : (x:t -> y:t -> b:bool { b = (v x < v y)});
    ( <= ) : (x:t -> y:t -> b:bool { b = (v x <= v y)});
    ( % ) : (x:t -> y:t -> Pure t (requires v y > 0 /\ fits (v x % v y)) (ensures fun z -> v z == v x % v y));
    [@@@TC.no_method]
    properties: squash (
      (forall (x:t). {:pattern v x} fits (v x)) 
    )
    (* ...todo, add other ops **)
}



instance bounded_int_int : bounded_int int = {
    fits = (fun _ -> True);
    v = id;
    u = id;
    ( + ) = (fun x y -> Prims.op_Addition x y);
    op_Subtraction = (fun x y -> Prims.op_Subtraction x y);
    ( < ) = (fun x y -> Prims.op_LessThan x y);
    ( <= ) = (fun x y -> Prims.op_LessThanOrEqual x y);
    ( % ) = (fun x y -> Prims.op_Modulus x y);
    properties = ()
}


class bounded_unsigned (t:eqtype) = {
  [@@@TC.no_method]
  base:bounded_int t;
  max_bound:t;
  [@@@TC.no_method]  
  static_max_bound: bool;
  [@@@TC.no_method]
  properties: squash (
    (forall (x:t). v x >= 0 /\ (static_max_bound ==> v x <= v max_bound)) /\
    (forall (x:nat). x <= v max_bound ==> fits #t x)
  )
}


instance bounded_from_bounded_unsigned (t:eqtype) (c:bounded_unsigned t) : bounded_int t = c.base

let safe_add (#t:eqtype) {| c: bounded_unsigned t |} (x y : t)
  : o:option t { Some? o ==> v (Some?.v o) == v x + v y } 
  = if c.static_max_bound
    then (
      assert ( x <= max_bound);
      if (y <= max_bound - x) 
      then Some (x + y)
      else None
    )
    else (
      if x <= max_bound
      then (
        if (y <= max_bound - x)
        then Some (x + y)
        else None
      )
      else None
    )

let safe_mod (#t:eqtype) {| c: bounded_unsigned t |} (x : t) (y : t)
  : Pure (option t)
         (requires v y > 0)
         (ensures fun o -> Some? o ==> v (Some?.v o) == v x % v y)
  = if c.static_max_bound
    then Some (x % y)
    else (
      if y <= max_bound
      then Some (x % y)
      else None
    )

let ok (#t:eqtype) {| c:bounded_int t |} (op: int -> int -> int) (x y:t) =
    c.fits (op (v x) (v y))

let add (#t:eqtype) {| bounded_int t |} (x:t) (y:t { ok (+) x y }) = x + y

let add3 (#t:eqtype) {| bounded_int t |} (x:t) (y:t) (z:t { ok (+) x y /\ ok (+) z (x + y)}) = x + y + z

//Writing the signature of bounded_int.(+) using Pure
//allows this to work, since the type of (x+y) is not refined
let add3_alt (#t:eqtype) {| bounded_int t |} (x:t) (y:t) (z:t { ok (+) x y /\ ok (+) (x + y) z}) = x + y + z

instance bounded_int_u32 : bounded_int FStar.UInt32.t = {
    fits = (fun x -> 0 <= x /\ x < 4294967296);
    v = (fun x -> FStar.UInt32.v x);
    u = FStar.UInt32.uint_to_t;
    ( + ) = (fun x y -> FStar.UInt32.add x y);
    op_Subtraction = (fun x y -> FStar.UInt32.sub x y);
    ( < ) = FStar.UInt32.(fun x y -> x <^ y);
    ( <= ) = FStar.UInt32.(fun x y -> x <=^ y);
    ( % ) = FStar.UInt32.(fun x y -> x %^ y);
    properties = ()
}

instance bounded_unsigned_u32 : bounded_unsigned FStar.UInt32.t = {
  base = TC.solve;
  max_bound = 0xfffffffful;
  static_max_bound = true;
  properties = ()
}

instance bounded_int_u64 : bounded_int FStar.UInt64.t = {
    fits = (fun x -> 0 <= x /\ x <= 0xffffffffffffffff);
    v = (fun x -> FStar.UInt64.v x);
    u = FStar.UInt64.uint_to_t;
    ( + ) = (fun x y -> FStar.UInt64.add x y);
    op_Subtraction = (fun x y -> FStar.UInt64.sub x y);
    ( < ) = FStar.UInt64.(fun x y -> x <^ y);
    ( <= ) = FStar.UInt64.(fun x y -> x <=^ y);
    ( % ) = FStar.UInt64.(fun x y -> x %^ y);
    properties = ()
}

instance bounded_unsigned_u64 : bounded_unsigned FStar.UInt64.t = {
  base = TC.solve;
  max_bound = 0xffffffffffffffffuL;
  static_max_bound = true;
  properties = ()
}

let test (t:eqtype) {| _ : bounded_unsigned t |} (x:t) = v x

let add_u32 (x:FStar.UInt32.t) (y:FStar.UInt32.t { ok (+) x y }) = x + y

//Again, parser doesn't allow using (-)
let sub_u32 (x:FStar.UInt32.t) (y:FStar.UInt32.t { ok op_Subtraction x y}) = x - y

//this work and resolved to int, because of the 1
let add_nat_1 (x:nat) = x + 1

//But, to add two nats, this fails, since typeclass resolution doesn't consider subtyping
[@@expect_failure]
let add_nat (x y:nat) = x + y

let nat_as_int (x:nat) : int = x

instance bounded_int_nat : bounded_int nat = {
    fits = (fun x -> x >= 0);
    v = nat_as_int;
    u = (fun x -> x);
    ( + ) = (fun x y -> Prims.op_Addition x y);
    op_Subtraction = (fun x y -> Prims.op_Subtraction x y); //can't write ( - ), it doesn't parse
    ( < ) = (fun x y -> Prims.op_LessThan x y);
    ( <= ) = (fun x y -> Prims.op_LessThanOrEqual x y);
    ( % ) = (fun x y -> Prims.op_Modulus x y);
    properties = ()
}
//with an instance for nat this works
let add_nat (x y:nat) = x + y
//but we should find a way to make it work with refinement, otherwise we'll need instances for pos etc. too

let pos_as_int (x:pos) : int = x

instance bounded_int_pos : bounded_int pos = {
    fits = (fun x -> x > 0);
    v = pos_as_int;
    u = (fun x -> x);
    ( + ) = (fun x y -> Prims.op_Addition x y);
    op_Subtraction = (fun x y -> Prims.op_Subtraction x y); //can't write ( - ), it doesn't parse
    ( < ) = (fun x y -> Prims.op_LessThan x y);
    ( <= ) = (fun x y -> Prims.op_LessThanOrEqual x y);
    ( % ) = (fun x y -> Prims.op_Modulus x y);
    properties = ()
}

// Using a fits predicate as the bounds check allows this class to also accomodate SizeT
open FStar.SizeT
instance bounded_int_size_t : bounded_int FStar.SizeT.t = {
    fits = (fun x -> x >= 0 /\ FStar.SizeT.fits x);
    v = (fun x -> FStar.SizeT.v x);
    u = (fun x -> FStar.SizeT.uint_to_t x);
    ( + ) = (fun x y -> FStar.SizeT.add x y);
    op_Subtraction = (fun x y -> FStar.SizeT.sub x y);
    ( < ) = (fun x y -> FStar.SizeT.(x <^ y));
    ( <= ) = (fun x y -> FStar.SizeT.(x <=^ y));
    ( % ) = (fun x y -> FStar.SizeT.(x %^ y));
    properties = ();
}

instance bounded_unsigned_size_t : bounded_unsigned FStar.SizeT.t = {
  base = TC.solve;
  max_bound = 0xffffsz;
  static_max_bound = false;
  properties = ()
}

//we know that size_t can hold at least 2^16
let size_t_plus_one (x:FStar.SizeT.t { x < 1024sz }) = x + 1sz
