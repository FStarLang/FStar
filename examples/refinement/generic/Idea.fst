module Idea 

open Lens
open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer
open LowStar.BufferOps
open LowStar.Modifies
open Mem_eq
open Relations
open FStar.UInt32

module H = FStar.Monotonic.Heap
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module U32 = FStar.UInt32
module Map = FStar.Map
module M = LowStar.Modifies


class lh lstate (#l:low_state lstate) state (#p: state_lens lstate state) a (wp : hwp_mon #state a) = {
  hc  : high a wp;
  lc  : low #lstate #l #state #p a wp hc }


instance ret #lstate (#l:low_state lstate) #state (#p: state_lens lstate state) #a (x : a) : lh lstate #l state #p a (return_wp x) = {
  hc = return_elab x;
  lc = lreturn x
}

instance bind #lstate (#l:low_state lstate) #state (#p: state_lens lstate state) #a #b 
   (#wp:hwp_mon #state a) (#fwp:(a -> hwp_mon #state b))
   (m : lh lstate #l state #p a wp)
   (f : (x:a) -> lh lstate #l state #p b (fwp x)) : lh lstate #l state #p b (bind_wp wp fwp) = {
  hc = bind_elab (hc #lstate #l #state #p #a #wp #m) (fun x -> hc #lstate #l #state #p #b #(fwp x) #(f x));
  lc = lbind (lc #lstate #l #state #p #a #wp #m) (fun x -> lc #lstate #l #state #p #b #(fwp x) #(f x))
}

instance get_comp #lstate (#l:low_state lstate) #state (#p: state_lens lstate state) 
         (#a:Type) (#l1:lens state a) (l2:state_lens lstate a) (#c:commutes p l1 l2) (_ : unit) 
: lh lstate #l state #p a (read_comp_wp l1) = {
  hc = read_comp l1 ();
  lc = lread_comp #lstate #l #state #p #a #l1 l2 #c ()
}

instance put_comp #lstate (#l:low_state lstate) #state (#p: state_lens lstate state) 
           (#a:Type) (#l1:lens state a) (l2:state_lens lstate a) (#c:commutes p l1 l2) (x : a) 
  : lh lstate #l state #p unit (write_comp_wp l1 x) = {
    hc = write_comp l1 x;
    lc = lwrite_comp #lstate #l #state #p #a #l1 l2 #c x
}


instance get #lstate (#l:low_state lstate) #state (#p: state_lens lstate state) (_ : unit) 
: lh lstate #l state #p state read_wp = {
    hc = read_elab ();
    lc = lread ()
}

instance put #lstate (#l:low_state lstate) #state (#p: state_lens lstate state) (x : state) 
: lh lstate #l state #p unit (write_wp x) = {
  hc = write_elab x;
  lc = lwrite x
}
