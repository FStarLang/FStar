module FStar.SGX

open FStar.Heap

(* SGXRegMemory type (In Progress)

 Basic Idea: 
	1. An 8-byte array of 7 different memory regions. Additionally also includes the set of registers (rax, rbx,..rbp, rsp)
		a. Read/Write Bitmap
		b. U Stack
		c. U Heap
		d. U Code
		e. V Stack
		f. V Heap
		g. V code
		h. Register set

		Memory Sketch
				 ____________________
				| 8-bytes /64-bits   |
				+____________________+
		bitmapstart->	|bbbbbbb.......bbbbb |
				|		     |
				+____________________+
		U Code start->	|bbbbbbb.......bbbbb |
				|  	    	     |
				+____________________+
		U Stack	start->	|bbbbbbb.......bbbbb |
				|  	    	     |
				+____________________+
		U Heap start->	|bbbbbbb.......bbbbb |
				|  	    	     |
				+____________________+
		V Heap start->	|bbbbbbb.......bbbbb |
				|  	    	     |
				+____________________+
		V Stack start->	|bbbbbbb.......bbbbb |
				|  	    	     |
				+____________________+
		V Code start->	|bbbbbbb.......bbbbb |
				|  	    	     |
				+____________________+

	2. Bitmap and Stack layout as shown below
	
			   Bitmap layout
			  ==============
					 ____________________
					| 8-bytes /64-bits   |
					+____________________+
			bitmapstart->	|bbbbbbb.......bbbbb |
					+____________________+
			bitmapoffset->	|bbbbbbb.......bbbbb |
					|  |    	     |
					|  idx    	     |
					+____________________+

			 Each entry is 8 bytes long and each bit represents if the corresponding 64-bytes at an 
			 address(computed by the formula below) is writable.
			Each offset represents the bit array for 64 64-bit addresses.
			 
			 To obtain address represented index 'idx' at 'bitmapoffset' is given as:
				address = ((bitmapoffset * 64) + idx) + enclave_start_address

			 To check if 'addr' is writable, compute the index 'idx' as follows:
				bitmapoffset  = (addr - enclave_start_address) / 64
				idx 	      = (addr - enclave_start_address) % 64

			 Stack Layout
			 ============
					 ____________________
					| 8-bytes /64-bits   |
					+____________________+___
			framepointer->	|bbbbbbb.......bbbbb |   |
					+____________________+   |
					|bbbbbbb.......bbbbb |   |--> current stack frame
					|____________________|   | stackpointer < framepointer
					|bbbbbbb.......bbbbb |   |
			stackpointer->	+____________________+___|

			rbp = frame pointer
			rsp = stack pointer


	3. Invariant to be maintained: 'U code' can read/write to only U stack or heap  /\ any such read/write is protected by bitmap
*)


(* Very sketchy framework. Does not type check, fill in the details 
   The idea to construct sgxmem as an inductive type containing the sub-memories
   instead of using hyperheaps.

   Skipping code sections for now. Add later if required
*)

noeq type bitmapmem
 | MkBitmapmem: ? -> bitmapmem

noeq type uheapmem
 | MkUheapmem: ? -> uheapmem

noeq type ustackmem
 | MkUstackmem: ? -> ustackmem

noeq type vheapmem
 | MkVheapmem: ? -> vheapmem

noeq type vstackmem
 | MkVstackmem: ? -> vstackmem


(* Construct a sgxmem type. It contains all sub-memories *)
noeq type sgxmem =
  | MkSGXMem :  bitmapmem -> uheapmem -> ustackmem -> vheapmem -> vstackmem-> sgxmem

(* Construct a reference to sgxmem
   It should contain the subregion it belongs to. How??

  One idea is to assign rids as follows:

  rid  memory
  ===========
  0   bitmapmem
  1   uheapmem
  2   ustackmem
  3   vheapmem
  4   vstackmem
  ...
  Below code  borrowed from HyperHeaps
*)
abstract let rid = list int
abstract let rref (id:rid) (a:Type) = Heap.ref a

noeq type sgxref (a:Type) =
  | MkSGXRef : id:rid -> ref:rref id a -> sgxref a


////////////////////////////////////////////////////////////////

//if the corresponding address is protected in bitmap 
assume	val isbitmapset:#a:Type-> h0:sgxmem->addr:sgxref a->bool	

