module Buffers

module Seq = FStar.Seq

open FStar.Integers

open FStar.HyperStack.ST

module HS = FStar.HyperStack

module B = LowStar.Buffer


type u8 = uint_8
type u32 = uint_32

type pre_t (#n1 #n2:nat) = (Seq.lseq u8 n1 & Seq.lseq u8 n2) -> Type0
type post_t (#n1 #n2:nat) (a:Type) = a -> (Seq.lseq u8 n1 & Seq.lseq u8 n2) -> Type0
type wp_t (#n1 #n2:nat) (a:Type) = wp:(post_t #n1 #n2 a -> pre_t #n1 #n2){
  forall p q. (forall x s. p x s ==> q x s) ==> (forall s. wp p s ==> wp q s)
}


let len (b:B.buffer u8) : GTot nat = B.length b

type repr (a:Type) (b1 b2:B.buffer u8) (wp:wp_t #(len b1) #(len b2) a) =
  unit -> STATE a (fun p h0 ->
    B.disjoint b1 b2 /\ B.live h0 b1 /\ B.live h0 b2 /\
    wp
      (fun x s1 ->
       forall h1. (s1 == (B.as_seq h1 b1, B.as_seq h1 b2) /\
              B.(modifies (loc_union (loc_buffer b1) (loc_buffer b2)) h0 h1) /\
              equal_domains h0 h1 /\
              B.live h1 b1 /\ B.live h1 b2) ==> p x h1)
      (B.as_seq h0 b1, B.as_seq h0 b2)
  )


let return (a:Type) (b1 b2:B.buffer u8) (x:a)
: repr a b1 b2 (fun p s -> p x s)
= fun _ -> x

let bind (a:Type) (b:Type)
  (b1 b2:B.buffer u8) (wp_f:wp_t #(len b1) #(len b2) a) (wp_g:a -> wp_t #(len b1) #(len b2) b)
  (f:repr a b1 b2 wp_f) (g:(x:a -> repr b b1 b2 (wp_g x)))
: repr b b1 b2
  (fun p -> wp_f (fun x -> (wp_g x) p))
= fun _ ->
  let x = f () in
  (g x) ()

let stronger (a:Type)
  (b1 b2:B.buffer u8) (wp_f:wp_t #(len b1) #(len b2) a) (wp_g:wp_t #(len b1) #(len b2) a)
  (f:repr a b1 b2 wp_f)
: Pure (repr a b1 b2 wp_g)
  (requires forall p s. wp_g p s ==> wp_f p s)
  (ensures fun _ -> True)
= f

let conjunction (a:Type)
  (b1 b2:B.buffer u8) (wp_f:wp_t #(len b1) #(len b2) a) (wp_g:wp_t #(len b1) #(len b2) a)
  (f:repr a b1 b2 wp_f) (g:repr a b1 b2 wp_g)
  (p:Type0)
: Type
= repr a b1 b2
  (fun post s ->
    (p ==> wp_f post s) /\
    ((~ p) ==> wp_g post s))


reifiable reflectable
layered_effect {
  CHACHA : a:Type -> b1:B.buffer u8 -> b2:B.buffer u8 -> wp_t #(len b1) #(len b2) a -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  stronger = stronger;
  conjunction = conjunction
}


let lift_div_chacha (a:Type)
  (b1 b2:B.buffer u8) (wp:pure_wp a{forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)})
  (f:unit -> DIV a wp)
: repr a b1 b2 (fun p s -> wp (fun x -> p x s))
= fun _ -> f ()


sub_effect DIV ~> CHACHA = lift_div_chacha

effect Chacha (a:Type)
  (b1 b2:B.buffer u8)
  (pre:(Seq.lseq u8 (len b1) & Seq.lseq u8 (len b2)) -> Type0)
  (post:(Seq.lseq u8 (len b1) & Seq.lseq u8 (len b2)) -> a -> (Seq.lseq u8 (len b1) & Seq.lseq u8 (len b2)) -> Type0)
= CHACHA a b1 b2 (fun p s -> pre s /\ (forall x s1. post s x s1 ==> p x s1))

let read1_ (b1 b2:B.buffer u8) (i:u32)
: repr u8 b1 b2
  (fun p s -> i < B.len b1 /\ (i < B.len b1 ==> p (Seq.index (fst s) (v i)) s))
= fun _ -> B.index b1 i

let read2_ (b1 b2:B.buffer u8) (i:u32)
: repr u8 b1 b2
  (fun p s -> i < B.len b2 /\ (i < B.len b2 ==> p (Seq.index (snd s) (v i)) s))
= fun _ -> B.index b2 i

let write1_ (b1 b2:B.buffer u8) (i:u32) (x:u8)
: repr unit b1 b2
  (fun p s ->
    i < B.len b1 /\ (i < B.len b1 ==> p () (Seq.upd (fst s) (v i) x, snd s)))
= fun _ -> B.upd b1 i x

let write2_ (b1 b2:B.buffer u8) (i:u32) (x:u8)
: repr unit b1 b2
  (fun p s ->
    i < B.len b2 /\ (i < B.len b2 ==> p () (fst s, Seq.upd (snd s) (v i) x)))
= fun _ -> B.upd b2 i x


let read1 (#b1 #b2:B.buffer u8) (i:u32)
: Chacha u8 b1 b2
  (requires fun _ -> i < B.len b1)
  (ensures fun s0 x s1 -> i < B.len b1 /\ x == Seq.index (fst s0) (v i) /\ s1 == s0)
= CHACHA?.reflect (read1_ b1 b2 i)

let read2 (#b1 #b2:B.buffer u8) (i:u32)
: Chacha u8 b1 b2
  (requires fun _ -> i < B.len b2)
  (ensures fun s0 x s1 -> i < B.len b2 /\ x == Seq.index (snd s0) (v i) /\ s1 == s0)
= CHACHA?.reflect (read2_ b1 b2 i)

let write1 (#b1 #b2:B.buffer u8) (i:u32) (x:u8)
: Chacha unit b1 b2
  (requires fun _ -> i < B.len b1)
  (ensures fun s0 _ s1 -> i < B.len b1 /\ s1 == (Seq.upd (fst s0) (v i) x, snd s0))
= CHACHA?.reflect (write1_ b1 b2 i x)

let write2 (#b1 #b2:B.buffer u8) (i:u32) (x:u8)
: Chacha unit b1 b2
  (requires fun _ -> i < B.len b2)
  (ensures fun s0 _ s1 -> i < B.len b2 /\ s1 == (fst s0, Seq.upd (snd s0) (v i) x))
= CHACHA?.reflect (write2_ b1 b2 i x)


#set-options "--using_facts_from '* -LowStar.Buffer -FStar.HyperStack'"
let copy (b1 b2:B.buffer u8)
: Chacha unit b1 b2
  (requires fun _ -> B.length b1 == 16 /\ B.length b2 == 16)
  (ensures fun s0 _ s1 -> Seq.equal (fst s1) (fst s0) /\ Seq.equal (snd s1) (fst s0))
= let x = read1 0ul in
  write2 0ul x;
  let x = read1 1ul in
  write2 1ul x;
  let x = read1 2ul in
  write2 2ul x;
  let x = read1 3ul in
  write2 3ul x;
  let x = read1 4ul in
  write2 4ul x;
  let x = read1 5ul in
  write2 5ul x;
  let x = read1 6ul in
  write2 6ul x;
  let x = read1 7ul in
  write2 7ul x;
  let x = read1 8ul in
  write2 8ul x;
  let x = read1 9ul in
  write2 9ul x;
  let x = read1 10ul in
  write2 10ul x;
  let x = read1 11ul in
  write2 11ul x;
  let x = read1 12ul in
  write2 12ul x;
  let x = read1 13ul in
  write2 13ul x;
  let x = read1 14ul in
  write2 14ul x;
  let x = read1 15ul in
  write2 15ul x


#reset-options
let copy_st (b1 b2:B.buffer u8)
: ST unit
  (requires fun h -> B.live h b1 /\ B.live h b2 /\ B.length b1 == 16 /\ B.length b2 == 16 /\ B.disjoint b1 b2)
  (ensures fun h0 _ h1 ->
    Seq.equal (B.as_seq h1 b1) (B.as_seq h0 b1) /\
    Seq.equal (B.as_seq h1 b2) (B.as_seq h0 b1) /\
    B.(modifies (loc_union (loc_buffer b1) (loc_buffer b2)) h0 h1))
= reify (copy b1 b2) ()
