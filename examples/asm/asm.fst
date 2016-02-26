module Asm

type reg = int

let asm_pre = st_pre_h reg
let asm_post a = st_post_h reg a
let asm_wp a = st_wp_h reg a

new_effect ASM_ = STATE_h reg //the effect ASM is very primitive, we won't use it much in specs
sub_effect
  DIV   ~> ASM_ = fun (a:Type) (wp:pure_wp a) (p:asm_post a) (r:reg) -> wp (fun a -> p a r)


effect ASM (a:Type) (wp:asm_wp a) = ASM_ a wp wp  //we'll use this one instead
effect Asm (a:Type) (pre:asm_pre) (post: (reg -> Tot (asm_post a))) = //and this one, which is more like a Hoare triple
       ASM_ a
             (fun (p:asm_post a) (h:reg) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WP *)
             (fun (p:asm_post a) (h:reg) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WP *)
             (* (fun (p:asm_post a) (h:reg) -> (forall a h1. (pre h /\ post h a h1) ==> p a h1))         (\* WLP *\) *)


type instr =
  | Add : int -> instr
  | Sub : int -> instr

val eval : instr -> reg -> Tot reg
let eval i r = match i with
  | Add j -> r + j
  | Sub j -> r - j


type prog = list instr

val finished : unit -> ASM prog  (fun post r0 -> post [] r0)
let finished _ = []

val nop : unit -> ASM prog  (fun post r0 -> post [] r0)
let nop _ = []


type ASMComp wp = unit -> ASM prog wp
type AsmComp pre post = = unit -> Asm prog pre post

assume val op_Hat_Hat : #wp:asm_wp prog
	       -> i:instr
	       -> =f:ASMComp wp
	       -> Tot (ASMComp (fun post r0 -> 
			      wp (fun p r1 -> post (i::p) r1) (eval i r0)))

val add_2: AsmComp (requires (fun r -> True))
		  (ensures (fun r_0 p r_1 -> r_1 = r_0 + 2))
let add_2 =  //^^ associates the wrong way, unfortunately
       (Add 1
    ^^ (Add 1
    ^^ finished))

assume val append : list 'a -> list 'a -> Tot (list 'a)

//we could define an operator that sequences in the other direction, a snoc instead of a cons 
assume val op_Hat_Bar : #wp:asm_wp prog
	       -> =f:ASMComp wp
      	       -> i:instr
	       -> Tot (ASMComp (fun post r0 -> 
			      wp (fun p r1 -> post (append p [i]) (eval i r1)) r0))
val add_3: AsmComp (requires (fun r -> True))
		  (ensures (fun r_0 p r_1 -> r_1 = r_0 + 3))
let add_3 = nop
    ^| (Add 1)
    ^| (Add 1)
    ^| (Add 1)


val add_4: AsmComp
  (requires (fun r -> True))
  (ensures (fun r_0 p r_1 -> r_1 = r_0 + 4))
let add_4 = nop
  ^| (Add 2)
  ^| (Add 2)
  ^| (Add 2)
  ^| (Sub 2)

(* Composing two basic blocks in sequence *)
assume val op_Hat_Hat_Hat :
          #wp1:asm_wp prog
	-> #wp2:asm_wp prog
        -> =f:ASMComp wp1
	-> =g:ASMComp wp2
	-> Tot (ASMComp (fun (post:asm_post prog) (r0:reg) ->
	       wp1 (fun p1 r1 ->
	       wp2 (fun p2 r2 -> post (append p1 p2) r2) r1) r0))
val add_4': AsmComp
  (requires (fun r -> True))
  (ensures (fun r_0 p r_1 -> r_1 = r_0 + 4))
let add_4' = add_2 ^^^ add_2
