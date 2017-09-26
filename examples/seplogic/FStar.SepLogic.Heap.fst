module FStar.SepLogic.Heap

include FStar.Heap

type addr = ref int

abstract let restrict (h:heap) (r:addr) :heap
  = admit ()

abstract let minus (h:heap) (r:addr) :heap
  = admit ()

abstract let disjoint_from (h1:heap) (h2:heap) :Type0
  = admit ()

abstract let join (h1:heap) (h2:heap) :heap
  = admit ()

abstract let points_to (r:addr) (x:int) :heap
  = admit ()

abstract let sel (h:heap) (r:addr) :Tot int
  = admit ()

let lemma0 (r:addr) (h:heap)
  :Lemma (requires True)
         (ensures  (join (restrict h r) (minus h r) == h))
	 [SMTPat ((h `restrict` r) `join` (h `minus` r))]
  = admit ()

let lemma2 (h1:heap) (h2:heap)
  :Lemma (requires True)
         (ensures (h1 `join` h2) == (h2 `join` h1))
	 [SMTPat (h1 `join` h2)]
  = admit ()

let lemma3 (h1:heap) (h2:heap)
  :Lemma (requires True)
         (ensures (h1 `disjoint_from` h2) == (h2 `disjoint_from` h1))
	 [SMTPat (h1 `disjoint_from` h2)]
  = admit ()

let lemma4 (r:addr) (x:int) (h1:heap)
  :Lemma (requires True)
         (ensures sel ((r `points_to` x) `join` h1) r == x)
	 [SMTPat (sel ((r `points_to` x) `join` h1) r)]
  = admit ()

let lemma5 (r:addr) (r1:addr{addr_of r1 <> addr_of r}) (x:int) (h1:heap)
  :Lemma (requires True)
         (ensures sel ((r `points_to` x) `join` h1) r1 == sel h1 r1)
	 [SMTPat (sel ((r `points_to` x) `join` h1) r1)]
  = admit ()

let lemma6 (h:heap)
  :Lemma (requires True)
         (ensures h `join` emp == h)
	 [SMTPat (h `join` emp)]
  = admit ()

let lemma6' (h:heap)
  :Lemma (requires True)
         (ensures emp `join` h == h)
  = admit ()
  
let lemma7 (r:addr) (h:heap)
  :Lemma (requires True)
         (ensures (h `restrict` r) == (r `points_to` (sel h r)))
	 [SMTPat (h `restrict` r)]
  = admit ()

let lemma8 (r:addr) (x:int) (y:int)
  :Lemma (requires (points_to r x == points_to r y))
         (ensures  (x == y))
	 [SMTPat (points_to r x); SMTPat (points_to r y)]
  = admit ()

let lemma9 (r:addr) (r1:addr{addr_of r1 <> addr_of r})(h:heap)
  :Lemma (requires True)
         (ensures sel (minus h r1) r == sel h r)
         [SMTPat (sel (minus h r1) r)]
  = admit ()
