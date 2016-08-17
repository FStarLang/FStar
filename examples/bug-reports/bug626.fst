module Bug626

(* Works *)
val lemma: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [SMTPat (x + y);SMTPat (y + x)]
let lemma x y = ()

val lemma2: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [SMTPatOr [
      [SMTPat (x + y)]];
   SMTPatOr [
       [SMTPat (y + x)]]]
(* Fails *)
(* let lemma2 x y = () *)

(* Works *)
val lemma3: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [SMTPatOr [
      [SMTPat (x + y);
       SMTPat (y + x)]]]
let lemma3 x y = ()

val lemma4: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [SMTPatOr [
      [SMTPat (x + y);
       SMTPat (y + x)]];
   SMTPat (x + y)]
(* Fails *)
(* let lemma4 x y = () *)

(* Works *)
val lemma5: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [SMTPat [SMTPatOr [
      [SMTPat (x + y);
       SMTPat (y + x)]]];
   SMTPat [SMTPat (x + y)]]
let lemma5 x y = ()
