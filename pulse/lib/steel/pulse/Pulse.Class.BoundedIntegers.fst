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
    properties = ()
}


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
    properties = ()
}

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
    properties = ()
}
//with an instance for nat this works
let add_nat (x y:nat) = x + y
//but we should find a way to make it work with refinement, otherwise we'll need instances for pos etc. too

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
    properties = ();
}

//we know that size_t can hold at least 2^16
let size_t_plus_one (x:FStar.SizeT.t { x < 1024sz }) = x + 1sz
