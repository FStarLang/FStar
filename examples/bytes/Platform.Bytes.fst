module Platform.Bytes
open FStar
open FStar.List
open FStar.List.Tot

val repr_bytes : nat -> GTot (n:nat{n>0})
let repr_bytes n =
    if n < 256 then 1
    else if n < 65536 then 2
    else if n < 16777216 then 3
    else if n < 4294967296 then 4
    else if n < 1099511627776 then 5
    else if n < 281474976710656 then 6
    else if n < 72057594037927936 then 7
    else if n < 18446744073709551616 then 8
    else 9

val lemma_repr_bytes_values: n:nat ->
  Lemma (   ( n < 256 <==> repr_bytes n = 1 )
         /\ ( (n >= 256 /\ n < 65536) <==> repr_bytes n = 2 )
         /\ ( (n >= 65536 /\ n < 16777216) <==> repr_bytes n = 3 )
         /\ ( (n >= 16777216 /\ n < 4294967296) <==> repr_bytes n = 4 )
         /\ ( (n >= 4294967296 /\ n < 1099511627776) <==> repr_bytes n = 5 )
         /\ ( (n >= 1099511627776 /\ n < 281474976710656) <==> repr_bytes n = 6 )
         /\ ( (n >= 281474976710656 /\ n < 72057594037927936) <==> repr_bytes n = 7 )
         /\ ( (n >= 72057594037927936 /\ n < 18446744073709551616) <==> repr_bytes n = 8 ) )
let lemma_repr_bytes_values n = ()

type byte = Char.char
type cbytes = string

(* let add_nat (a : nat) (b : nat) : nat = a + b *)

(* val sum : list nat -> Tot nat *)
(* let sum ls = fold_leftT add_nat 0 ls *)

val sum_length : list string -> Tot nat
(* let sum_length ls = sum (mapT String.length ls) *)
let rec sum_length ls =
  match ls with
  | [] -> 0
  | h :: t -> String.length h + sum_length t

type proto_bytes = {
       (*  A series of strings whose total concatenated length is [max]. *)
       bl: list cbytes;
       max: nat;
       (* The length of the subset. *)
       length: nat;
       (* The start index of the subset. *)
       index: nat
}

type good_bytes (b:proto_bytes) = b.max = sum_length b.bl /\ b.index <= b.max /\ b.index + b.length <= b.max

type bytes = b:proto_bytes{good_bytes b}

(* type bytes =  *)
(*   | MkBytes :  *)
(*        (\*  A series of strings whose total concatenated length is [max]. *\) *)
(*        bl: list cbytes -> *)
(*        max: nat -> *)
(*        (\* The length of the subset. *\) *)
(*        length: nat -> *)
(*        (\* The start index of the subset. *\) *)
(*        index: nat{max = sum_length bl /\ index <= max /\ index + length <= max} -> *)
(*        bytes *)

assume val substringT: s:string -> start:nat -> len:nat{let l = String.length s in start <= l && start + len <= l} -> Tot (res:string{String.length res = len})
assume val string_length_append: a:string -> b:string -> Lemma 
  (requires True)
  (ensures String.length (a ^ b) = String.length a + String.length b)
  [SMTPat (String.length (a ^ b))]
assume val string_length_empty: unit -> Lemma 
  (requires True)
  (ensures String.length "" = 0)
  [SMTPat (String.length "")]
assume val append_empty : s:string -> Lemma 
  (requires True)
  (ensures s ^ "" = s)
  [SMTPat (s ^ "")]
assume val empty_append : s:string -> Lemma 
  (requires True)
  (ensures "" ^ s = s)
  [SMTPat ("" ^ s)]
assume val append_assoc : a:string -> b:string -> c:string -> Lemma 
  (requires True)
  (ensures (a ^ (b ^ c)) = ((a ^ b) ^ c))
  [SMTPat (a ^ (b ^ c))]

(* val sum_length_le : i:nat -> h:cbytes -> t:list cbytes -> Lemma (i <= sum_length (h::t) ==> i - String.length h <= sum_length t) *)
(* let sum_length_le i h t = () *)

(* val sum_length_cons : h:cbytes -> t:list cbytes -> Lemma (sum_length (h::t) = String.length h + sum_length t) (decreases t) *)
(* let rec sum_length_cons h t =  *)
(*   match t with *)
(*    | [] -> () *)
(*    | h' :: t' -> sum_length_cons h' t' *)

val exfalso : #a:Type -> u:unit{False} -> Tot a
let rec exfalso #a _ = exfalso ()

val string_concat : ls:list string -> Tot (r:string{String.length r = sum_length ls})
let rec string_concat ls =
  match ls with
  | [] -> ""
  | x :: xs -> x ^ string_concat xs

val sum_length_append : a:list string -> b:list string -> Lemma 
  (requires True)
  (ensures (sum_length (a @ b) = sum_length a + sum_length b))
  [SMTPat (sum_length (a @ b))]
let rec sum_length_append a b =
  match a with
    | [] -> ()
    | x :: a' -> sum_length_append a' b

val concat_append : a:list string -> b:list string -> Lemma 
  (requires True)
  (ensures (string_concat (a @ b) = (string_concat a ^ string_concat b)))
  [SMTPat (string_concat (a @ b))]
let rec concat_append a b =
  match a with
    | [] -> ()
    | x :: xs -> 
      concat_append xs b


assume val length_0_empty : s:string -> Lemma 
  (requires String.length s = 0)
  (ensures s = "")
  [SMTPat (String.length s = 0)]


val getBytes : bl:list cbytes -> i:nat{i <= sum_length bl} -> n:nat{i+n <= sum_length bl} -> Tot (b:cbytes{String.length b = n})
let rec getBytes (bl: list cbytes) i n  =
    match bl with
    | [] -> 
      if n = 0
      then ""
      else exfalso ()
    | h::t ->
        if i >= (String.length h)
        then getBytes t (i- (String.length h)) n
        else let curr = (String.length h) - i in
             if curr >= n
             then substringT h i n
             else 
               substringT h i curr ^ getBytes t 0 (n-curr)


val lemma_getBytes: ls1:list cbytes -> ls2:list cbytes -> i:nat{i <= sum_length ls1} -> n:nat{sum_length ls1 <= i + n /\ i + n <= sum_length ls1 + sum_length ls2} -> Lemma
  (requires True)
  (ensures getBytes (ls1 @ ls2) i n = (getBytes ls1 i (sum_length ls1 - i) ^ getBytes ls2 0 (i + n - sum_length ls1)))
  [SMTPat (getBytes (ls1 @ ls2) i n)]


let rec lemma_getBytes ls1 ls2 i n = 
  match ls1 with
  | [] ->
    ()
  | h :: t ->
    if String.length h <= i then
      lemma_getBytes t ls2 (i - String.length h) n
    else
      let curr = (String.length h) - i in
      if n <= curr then 
        let _ = assert (i + n - sum_length ls1 = 0) in
        ()
      else 
        let _ = lemma_getBytes t ls2 0 (n - curr) in
        if sum_length ls1 - i <= curr then
          let _ = assert (sum_length t = 0) in
          ()
        else
          ()
        

val lemma_getBytes_2 : ls:list cbytes -> Lemma
  (requires True)
  (ensures getBytes ls 0 (sum_length ls) = string_concat ls)
  [SMTPat (getBytes ls 0 (sum_length ls))]


val sum_length_0_concat_empty : ls:list string -> Lemma 
  (requires sum_length ls = 0)
  (ensures string_concat ls = "")
  [SMTPat (sum_length ls = 0)]


let rec sum_length_0_concat_empty ls =
  match ls with
  | [] -> ()
  | x :: xs ->
    let _ = assert (String.length x = 0) in
    sum_length_0_concat_empty xs


assume val substring_full : s:string -> Lemma
  (requires True)
  (ensures substringT s 0 (String.length s) = s)
  [SMTPat (substringT s 0 (String.length s))]


let rec lemma_getBytes_2 ls = 
  match ls with
  | [] ->
    ()
  | h :: t ->
    if String.length h <= 0 then
      let _ = assert (String.length h = 0) in
      lemma_getBytes_2 t 
    else
      let curr = String.length h in
      if sum_length ls <= curr then
        let _ = assert (sum_length t = 0) in
        ()
      else
        let _ = lemma_getBytes_2 t in
        ()
          

val get_cbytes : b:bytes -> Tot (r:cbytes{String.length r = b.length})
let get_cbytes (b:bytes) =
    if b.length = b.max && b.index = 0 then
      string_concat b.bl
    else
      getBytes b.bl b.index b.length

val op_At_Bar: bytes -> bytes -> Tot bytes
let op_At_Bar (a:bytes) (b:bytes) =
    if a.length + a.index = a.max && b.index = 0 then
      {bl = (a.bl @ b.bl);
       length = a.length + b.length;
       index = a.index;
       max = a.max + b.max}
    else
      {bl = [get_cbytes a ^ get_cbytes b];
       length = a.length + b.length;
       index = 0;
       max = a.length + b.length}
(* let op_AtBar = op_At_Bar *)


(* a version of get_cbytes that doesn't have the [string_concat] part so it's easier to reason about *)
val get_cbytes' : b:bytes -> Tot (r:cbytes{String.length r = b.length})
let get_cbytes' (b:bytes) =
      getBytes b.bl b.index b.length


val get_cbytes'_ok : b : bytes -> Lemma
  (requires True)
  (ensures get_cbytes b = get_cbytes' b)
  [SMTPat (get_cbytes b)]


let get_cbytes'_ok b = ()


val lemma_op_At_Bar : a:bytes -> b:bytes -> Lemma 
  (requires True)
  (ensures get_cbytes (a @| b) = (get_cbytes a ^ get_cbytes b))
  [SMTPat (get_cbytes (a @| b))]
let lemma_op_At_Bar a b = ()


let length (d:bytes) = d.length


val split: b:bytes -> n:nat{n <= length b} ->
  Tot (x:(bytes * bytes) {length (fst (x))= n /\ length (snd (x)) == (length b) - n }) 


let split b i =
    {bl = b.bl;
     length = i;
     index = b.index;
     max = b.max},
    {bl = b.bl;
     length = b.length - i;
     index = b.index + i;
     max = b.max}


val lemma_split_1 : b:bytes -> i:nat{i <= length b} -> Lemma (let x = split b i in length (fst x) = i && length (snd x) = length b - i)
let lemma_split_1 b i = ()


(* getBytes on sub-range *)
val lemma_getBytes_3: ls:list cbytes -> i:nat{i <= sum_length ls} -> n:nat{i + n <= sum_length ls} -> i2:nat{i <= i2 /\ i2 <= i+n} -> n2:nat{i2+n2<=i+n} -> Lemma
  (requires True)
  (ensures getBytes ls i2 n2 = substringT (getBytes ls i n) (i2 - i) n2)
  [SMTPat (getBytes ls i2 n2)]
  

let lemma_getBytes_3 ls i n i2 n2 = 
  admit ()


val splitTwo : s : string -> i:nat{i <= String.length s} -> Tot ((a:string{String.length a = i}) * (b:string{String.length b = String.length s - i}))
let splitTwo s i = (substringT s 0 i, substringT s i (String.length s - i))


val lemma_split_2 : b:bytes -> i:nat{i <= length b} -> Lemma 
  (let p = split b i in 
   let ap = splitTwo (get_cbytes b) i in
   get_cbytes (fst p) = fst ap /\
   get_cbytes (snd p) = snd ap)


let lemma_split_2 b i =
  let _ = lemma_getBytes_3 b.bl b.index b.length b.index i in
  let _ = lemma_getBytes_3 b.bl b.index b.length (b.index+i) (b.length-i) in
  let _ = assert (get_cbytes (snd (split b i)) = snd (splitTwo (get_cbytes b) i)) in
  ()


type bytes_eq (a:bytes) (b:bytes) = (get_cbytes a = get_cbytes b)


assume val split_append : s:string -> i:nat{i <= String.length s} -> Lemma
  (requires True)
  (ensures 
    (let p = splitTwo s i in 
    fst p ^ snd p = s))
  

val lemma_split_3 : b:bytes -> i:nat{i <= length b} -> Lemma 
  (let p = split b i in 
   bytes_eq (fst p @| snd p) b)


let lemma_split_3 b i =
  let _ = lemma_split_2 b i in
  let _ = split_append (get_cbytes b) i in
  ()


assume val bytes_extensionality: a:bytes -> b:bytes -> Lemma
  (requires bytes_eq a b)
  (ensures a = b)
  [SMTPat (bytes_eq a b)]


val lemma_split : s:bytes -> i:nat{(0 <= i /\ i <= length s)} -> Lemma
  (ensures ((fst (split s i)) @| (snd (split s i)) = s))
let lemma_split s i = lemma_split_3 s i

  
val split_eq: s:bytes -> i:nat{(0 <= i /\ i <= length s)} -> Pure
  (x:(bytes * bytes){length (fst x) = i && length (snd x) = length s - i})
  (requires True)
  (ensures (fun x -> ((fst x) @| (snd x) = s)))


let split_eq s i =
  let _ = lemma_split s i in
  split s i
  

let abytes (ba:cbytes) =
    {bl = [ba]; length = String.length ba; index = 0; max = String.length ba}

(* let rec for_ first last init f = *)
(*   if first > last then *)
(*     init *)
(*   else *)
(*     for_ (first + 1) last (f init first) f *)

let abytes_max (ba:cbytes) (max:int) =
  let len = String.length ba in
  if len <= max then
    let arr = ba ^ String.make (max-len) (Char.char_of_int 0) in
    {bl = [arr]; length = len; index = 0; max = len}
  else
    failwith "abytes_max: length exceeds max"

let abyte (ba:byte) =
    {bl = [String.make 1 ba]; length = 1; index = 0; max = 1}

let abyte2 (ba1,ba2) =
    let s = String.make 1 ba1 ^ String.make 1 ba2 in
    {bl = [s]; length = 2; index = 0; max = 2}

val getByte : list cbytes -> int -> Char.char
let rec getByte (bl:list cbytes) (i:int) =
  match bl with
    | [] -> failwith "getByte: array out of bounds"
    | h::t -> 
      if i >= String.length h then 
        getByte t (i-String.length h)
      else 
        String.get h i

val getByte2 : list cbytes -> int -> byte * byte
let rec getByte2 (bl: list cbytes) i =
    match bl with
   | [] -> failwith "array out of bounds"
   | h::t -> 
     if i >= String.length h then 
       getByte2 t (i - String.length h)
     else if (String.length h) - i >= 2 then 
       (String.get h i, String.get h (i+1))
     else 
     match bl with
     | h1::h2::t ->
       if (String.length h1) - i = 1 && (String.length h2) > 0 then 
         (String.get h1 i, String.get h2 0)
       else failwith "getByte2: array out of bounds"
     | _ -> failwith "getByte2: array out of bounds"

let cbyte (b:bytes) =
  if b.length = 1 then
    let b1 = getByte b.bl b.index in b1
  else failwith "cbyte: expected an array of length 1"

let cbyte2 (b:bytes) =
    if b.length = 2 then
      let (b1,b2) = getByte2 b.bl b.index in b1,b2
    else failwith "cbyte2: expected an array of length 2"

assume val getT: s:string -> i:int{i < String.length s} -> Char.char

let index (b:bytes) i =
  if b.length > i then
    let s = getBytes b.bl b.index b.length in
    getT s i
  else failwith "index: index out of range"

