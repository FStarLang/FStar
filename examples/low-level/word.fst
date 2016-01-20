(*--build-config
    other-files:FStar.FunctionalExtensionality.fst FStar.Set.fsi
  --*)
module MachineWord

(*copied fro examples/maths/bijection.fst, because that file doesn't compile*)
type inverseLR (#a:Type) (#b:Type) (fab:(a -> Tot b)) (fba:(b -> Tot a)) =
       (forall (x:a). fba (fab x) = x) /\ (forall (y:b). fab (fba y) = y)

let bitsize:nat = 32

assume val nexp : nat -> nat -> Tot nat


type wordNat = (n:int{0 < n /\ n < (nexp bitsize bitsize)})

(*0 is the LSB*)
type word = (n:nat{n<bitsize}) -> Tot bool

assume val toNat : word -> Tot wordNat
assume val fromNat : f:(wordNat -> Tot word){inverseLR f toNat}

(*when compiled, it will be mapped to a SINGLE CPU instruction.
  This definition is for reasoning purposes, if any*)
val complement : word -> Tot word
let complement w = (fun n -> (not (w n)))

val xor : bool -> bool -> Tot bool
let xor a b = (a || b) && ((not a) || (not b))

val bitwiseXOR : word -> word ->  Tot word
let bitwiseXOR w1 w2 = (fun n -> (xor (w1 n) (w2 n)))

val bitwiseAnd : word -> word -> Tot word
let bitwiseAnd w1 w2 = (fun n -> ((w1 n) && (w2 n)))

val bitwiseOr : word -> word -> Tot word
let bitwiseOr w1 w2 = (fun n -> ((w1 n) || (w2 n)))

val bitwiseXOR3 : word -> word -> word -> Tot word
let bitwiseXOR3 w1 w2 w3 = bitwiseXOR (bitwiseXOR w1 w2) w3

assume val fromHex : string -> Tot word

assume val modAddNat : wordNat -> wordNat -> Tot wordNat

val wmodAdd : word -> word -> Tot word
let wmodAdd w1 w2 =  fromNat (modAddNat (toNat w1) (toNat w2))

(*machine primitive operation*)
val rightshift : nat -> word -> Tot word
let rightshift  sh w =
  fun ind ->
    let newInd = ind + sh in
    if (newInd < bitsize)
    then w newInd
    else false
(*false stands for the bit 0*)

(*machine primitive operation*)
val leftshift : nat -> word -> Tot word
let leftshift  sh w =
  fun ind ->
    let newInd = ind - sh in
    if (0< newInd)
    then w newInd
    else false

val leftrotate : (n:nat{n<bitsize}) -> word -> Tot word
let leftrotate n w = bitwiseOr (leftshift n w) (rightshift (bitsize - n) w)

val rightrotate : (n:nat{n<bitsize}) -> word -> Tot word
let rightrotate n w = bitwiseOr (rightshift n w) (leftshift (bitsize - n) w)

val w0 : word
let w0 x = false
 
