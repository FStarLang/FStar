module BorrowsExample
open Pulse
open FStar.Seq
open Pulse.Lib.Borrow
open Pulse.Lib.Shift
open Pulse.Lib.Trade
open Pulse.Lib.Array
open Pulse.Lib.WithPure
#lang-pulse

// A read-only array reference bounded by the lifetime a
let array_bpts_to #t (a: lifetime) (x: array t) (y: seq t) : slprop =
  exists* p. a >:> x |-> Frac p y

fn dup_array_bpts_to u#t (#t: Type u#t) a x y () : duplicable_f (array_bpts_to #t a x y) = {
  unfold array_bpts_to a x y; with p. _;
  intro (shift (pts_to x #p y) ((pts_to x #(p/.2.0R) y) ** (pts_to x #(p/.2.0R) y) **
        trade ((pts_to x #(p/.2.0R) y) ** (pts_to x #(p/.2.0R) y)) (pts_to x #p y))) fn _ {
    share x;
    intro (trade ((pts_to x #(p/.2.0R) y) ** (pts_to x #(p/.2.0R) y)) (pts_to x #p y)) fn _ {
      gather x;
    }
  };
  share_borrow (x |-> Frac p y) (x |-> Frac (p/.2.0R) y) (x |-> Frac (p/.2.0R) y);
  fold array_bpts_to a x y;
  fold array_bpts_to a x y;
}
instance duplicable_array_bpts_to #t a x y : duplicable (array_bpts_to #t a x y) = { dup_f = dup_array_bpts_to #t a x y }

inline_for_extraction noextract
unobservable fn array_slice u#t (#t: Type u#t) #a (x: array t) (#y: erased (seq t)) i j
  preserves lifetime_alive a
  requires array_bpts_to a x y
  requires with_pure (SizeT.v i <= SizeT.v j /\ SizeT.v j < Seq.length y)
  returns x': array t
  ensures array_bpts_to a x' (slice y (SizeT.v i) (SizeT.v j))
{
  unfold array_bpts_to a x y; with p. _;
  open_lifetime a;
  use_borrow a (x |-> Frac p y);
  to_mask x;
  with y_. assert pts_to_mask x #p y_ (fun _ -> True);
  let x' = sub x i (SizeT.v j);
  with y'. assert pure (y' == slice y (SizeT.v i) (SizeT.v j));
  intro (trade (x' |-> Frac p y') (x |-> Frac p y))
      #(pts_to_mask x #p y_ (fun k -> l_True /\ ~(SizeT.v i <= k /\ k < SizeT.v j))) fn _ {
    to_mask x';
    return_sub x;
    from_mask x;
    with y''. assert pts_to x #p y'' ** pure (Seq.equal y y'');
  };
  weaken_opened (x |-> Frac p y) (x' |-> Frac p y');
  from_mask x';
  with y''. assert pts_to (gsub x (SizeT.v i) (SizeT.v j)) #p y'' ** pure (Seq.equal y' y'');
  end_use_borrow a (x' |-> Frac p y');
  close_lifetime a;
  fold array_bpts_to a x' y';
  x'
}

inline_for_extraction noextract
fn op_Array_Access u#t (#t: Type u#t) #a (x: array t) (#y: erased (seq t)) (i: SizeT.t)
  preserves lifetime_alive a
  preserves array_bpts_to a x y
  requires with_pure (SizeT.v i < Seq.length y)
  returns r: t
  ensures pure (Seq.index y (SizeT.v i) == r)
{
  unfold array_bpts_to a x y; with p. _;
  open_lifetime a;
  use_borrow a (x |-> Frac p y);
  let r = x.(i);
  end_use_borrow a (x |-> Frac p y);
  close_lifetime a;
  fold array_bpts_to a x y;
  r
}

fn demo () returns r: (r: bool {r}) {
  let mut arr = [| 0uy; 10sz |];
  assert live arr; pts_to_len arr; // forget value

  let a = begin_lifetime ();

  with varr. assert arr |-> varr;
  borrow a (pts_to arr varr);
  fold array_bpts_to a arr varr;

  dup (array_bpts_to a arr varr) ();
  let arr1 = array_slice arr 5sz 8sz;

  dup (array_bpts_to a arr varr) ();
  let arr2 = array_slice arr 6sz 9sz;

  // Now we have read-only permission to arr1 and arr2, two overlapping slices of arr.
  let x = arr1.(1sz);
  let y = arr2.(0sz);
  let r = (x = y);

  end_lifetime a;
  end_borrow a (arr |-> varr);
  // And now we have arr back.

  drop_ (lifetime_dead a);
  drop_ (array_bpts_to a arr2 (slice varr 6 9));
  drop_ (array_bpts_to a arr varr);
  drop_ (array_bpts_to a arr1 (slice varr 5 8));

  r
}