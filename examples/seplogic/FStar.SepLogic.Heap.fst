module FStar.SepLogic.Heap

include FStar.Heap

type addr = ref int

abstract let restrict (h:heap) (r:addr) :heap
  = admit ()

abstract let minus (h:heap) (r:addr) :heap
  = admit ()

abstract let join (h1:heap) (h2:heap) :heap
  = admit ()

abstract let points_to (r:addr) (x:int) :heap
  = admit ()

abstract let sel (h:heap) (r:addr) :Tot int
  = admit ()

let lemma_join_restrict_minus (r:addr) (h:heap)
  :Lemma (requires True)
         (ensures  (join (restrict h r) (minus h r) == h))
	 [SMTPat (join (restrict h r) (minus h r))]
  = admit ()

let lemma_join_is_comm (h1:heap) (h2:heap)
  :Lemma (requires True)
         (ensures (join h1 h2) == (join h2 h1))
	 [SMTPat (join h1 h2)]
  = admit ()

let lemma_join_h_emp (h:heap)
  :Lemma (requires True)
         (ensures (join h emp) == h)
	 [SMTPat (join h emp)]
  = admit ()

let lemma_restrict_eq_points_to (r:addr) (h:heap)
  :Lemma (requires True)
         (ensures (restrict h r) == (points_to r (sel h r)))
	 [SMTPat (restrict h r)]
  = admit ()

let lemma_points_to_is_injective (r:addr) (x:int) (y:int)
  :Lemma (requires (points_to r x == points_to r y))
         (ensures  (x == y))
	 [SMTPat (points_to r x); SMTPat (points_to r y)]
  = admit ()

let lemma_sel_r_from_points_to_join_h (r:addr) (x:int) (h1:heap)
  :Lemma (requires True)
         (ensures sel (join (points_to r x) h1) r == x)
	 [SMTPat (sel (join (points_to r x) h1) r)]
  = admit ()

let lemma_sel_r1_from_points_to_join_h (r:addr) (r1:addr{addr_of r1 <> addr_of r}) (x:int) (h1:heap)
  :Lemma (requires True)
         (ensures sel (join (points_to r x) h1) r1 == sel h1 r1)
	 [SMTPat (sel (join (points_to r x) h1) r1)]
  = admit ()

let lemma_sel_r_from_minus (r:addr) (r1:addr{addr_of r1 <> addr_of r})(h:heap)
  :Lemma (requires True)
         (ensures sel (minus h r1) r == sel h r)
         [SMTPat (sel (minus h r1) r)]
  = admit ()

let lemma_restrict_points_to_join_h_to_r (r:addr) (x:int) (h1:heap)
  :Lemma (requires True)
         (ensures restrict (join (points_to r x) h1) r == (points_to r x))
         [SMTPat (restrict (join (points_to r x) h1) r)]
  = admit ()

let lemma_restrict_points_to_join_h_to_r1 (r:addr) (r1:addr{addr_of r1 <> addr_of r})(x:int) (h1:heap)
  :Lemma (requires True)
         (ensures restrict (join (points_to r x) h1) r1 == restrict h1 r1)
	 [SMTPat (restrict (join (points_to r x) h1) r1)]
  = admit ()

let lemma_restrict_r1_from_minus (r:addr) (r1:addr{addr_of r1 <> addr_of r}) (h:heap)
  :Lemma (requires True)
         (ensures restrict (minus h r) r1 == restrict h r1)
	 [SMTPat (restrict (minus h r) r1)]
  = admit ()


