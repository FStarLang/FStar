module Asm

type reg = int

kind ASM_Pre = STPre_h reg
kind ASM_Post (a:Type) = STPost_h reg a
kind ASM_WP (a:Type) = STWP_h reg a

new_effect ASM_ = STATE_h reg //the effect ASM is very primitive, we won't use it much in specs
sub_effect
  DIV   ~> ASM_ = fun (a:Type) (wp:PureWP a) (p:ASM_Post a) (r:reg) -> wp (fun a -> p a r)


effect ASM (a:Type) (wp:ASM_WP a) = ASM_ a wp wp  //we'll use this one instead
effect Asm (a:Type) (pre:ASM_Pre) (post: (reg -> ASM_Post a)) = //and this one, which is more like a Hoare triple
       ASM_ a
             (fun (p:ASM_Post a) (h:reg) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WP *)
             (fun (p:ASM_Post a) (h:reg) -> (forall a h1. (pre h /\ post h a h1) ==> p a h1))         (* WLP *)


type instr = 
  | Add : int -> instr
  | Sub : int -> instr

val eval : instr -> reg -> Tot reg
let eval i r = match i with 
  | Add j -> r + j
  | Sub j -> r - j


type prog = list instr

val finished : unit -> ASM prog  (fun (post:ASM_Post prog) (r0:reg) -> post [] r0)
let finished _ = []


type ASMComp (wp:ASM_WP prog) = unit -> ASM prog wp
type AsmComp (pre:ASM_Pre) (post:reg -> ASM_Post prog) = unit -> Asm prog pre post

assume val op_Hat_Hat : #wp:ASM_WP prog
	       -> i:instr 
	       -> =f:ASMComp wp
	       -> Tot (ASMComp (fun (post:ASM_Post prog) (r0:reg) -> 
			      wp (fun p r1 -> post (i::p) r1) (eval i r0)))

val add_2: AsmComp (requires (fun r -> True))
		  (ensures (fun r_0 p r_1 -> r_1 = r_0 + 2))
let add_2 =  //regardless of the associativity of  >>, you currently need the parenthesis because of the precedence of function application
       Add 1  
   ^^ (Add 1
   ^^ finished)

val add_4: AsmComp 
  (requires (fun r -> True))
  (ensures (fun r_0 p r_1 -> r_1 = r_0 + 4))
let add_4 = 
      Add 2
  ^^ (Add 2
  ^^ (Add 2 
  ^^ (Sub 2
  ^^  finished)))

(* This is just a placeholder for the List.append that we'd really use*)
assume val append: list 'a -> list 'a -> Tot (list 'a)

(* Composing two basic blocks in sequence *)
assume val op_Hat_Hat_Hat : 
          #wp1:ASM_WP prog
	-> #wp2:ASM_WP prog
        -> =f:ASMComp wp1
	-> =g:ASMComp wp2
	-> Tot (ASMComp (fun (post:ASM_Post prog) (r0:reg) -> 
	       wp1 (fun p1 r1 -> 
	       wp2 (fun p2 r2 -> post (append p1 p2) r2) r1) r0))

val add_4': AsmComp 
  (requires (fun r -> True))
  (ensures (fun r_0 p r_1 -> r_1 = r_0 + 4))
(* let add_4' = add_2 ^^^ add_2 //NS: type inference for this one doesn't quite work for some silly reason ... it will once I fix it. *)
