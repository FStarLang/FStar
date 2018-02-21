module Platform.Bytes

(* A verified implementation of lazy byte sequences, with constant-time split and other efficient
 * operations. *)

open FStar
open FStar.List
open FStar.List.Tot

assume val substringT: s:string -> start:nat -> len:nat{let l = String.length s in start <= l && start + len <= l} -> Tot (res:string{String.length res = len})
assume val string_length_append: a:string -> b:string -> Lemma 
  (requires True)
  (ensures String.length (a ^ b) = String.length a + String.length b)
  [SMTPat (String.length (a ^ b))]
assume val string_length_empty: squash (String.length "" = 0)
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
assume val length_0_empty : s:string -> Lemma 
  (requires String.length s = 0)
  (ensures s = "")
  [SMTPat (String.length s)]
assume val substring_full : s:string -> Lemma
  (requires True)
  (ensures substringT s 0 (String.length s) = s)
  [SMTPat (substringT s 0 (String.length s))]
val splitTwo : s : string -> i:nat{i <= String.length s} -> Tot ((a:string{String.length a = i}) * (b:string{String.length b = String.length s - i}))
let splitTwo s i = (substringT s 0 i, substringT s i (String.length s - i))
assume val split_append : s:string -> i:nat{i <= String.length s} -> Lemma
  (requires True)
  (ensures 
    (let p = splitTwo s i in 
    fst p ^ snd p = s))
assume val substring_sub_range: s:string -> i:nat{i <= String.length s} -> n:nat{i + n <= String.length s} -> i2:nat{i <= i2 /\ i2 <= i+n} -> n2:nat{i2+n2<=i+n} -> Lemma
  (requires True)
  (ensures substringT s i2 n2 = substringT (substringT s i n) (i2 - i) n2)
assume val substring_prefix: prefix:string -> s:string -> i:nat{i <= String.length s} -> n:nat{i + n <= String.length s} -> Lemma 
  (substringT (prefix ^ s) (String.length prefix + i) n = substringT s i n)
assume val substring_suffix: s:string -> i:nat{i <= String.length s} -> n:nat{i + n <= String.length s} -> suffix:string -> Lemma 
  (substringT (s ^ suffix) i n = substringT s i n)
assume val substring_append: s1:string -> i1:nat{i1 <= String.length s1} -> s2:string -> n2:nat{n2 <= String.length s2} -> Lemma
  (substringT s1 i1 (String.length s1 - i1) ^ substringT s2 0 n2 = substringT (s1 ^ s2) i1 (String.length s1 - i1 + n2))
assume val make_length : n:nat -> c:Char.char -> Lemma
  (requires True)
  (ensures String.length (String.make n c) = n)
  [SMTPat (String.length (String.make n c))]
assume val getT : s:string -> i:nat{i < String.length s} -> Tot Char.char
assume val compare_eq : a:string -> b:string -> Lemma
 (requires True)
 (ensures String.compare a b = 0 <==> a = b)
 (* (ensures (String.compare a b = 0 ==> a = b) /\ (String.compare a b <> 0 ==> a <> b)) *)
 (* [SMTPat (String.compare a b = 0)] *)
val concatT : sep:string -> ls:list string -> Tot string
let rec concatT sep ls =
  match ls with
  | [] -> ""
  | x :: xs -> 
    match xs with
    | [] -> x
    | _ -> x ^ sep ^ concatT sep xs
assume val concat_concatT : sep:string -> ls:list string -> Lemma
  (String.concat sep ls = concatT sep ls)
assume val string_append_inj: s1:string -> s2:string -> t1:string -> t2:string {String.length s1 = String.length t1 \/ String.length s2 = String.length t2} ->
  Lemma (requires ((s1 ^ s2) = (t1 ^ t2)))
        (ensures (s1 = t1 /\ s2 = t2))


assume val string_xor : l:nat -> a:string{String.length a = l} -> b:string{String.length b = l} -> Tot (s:string{String.length s = l})

// This is just [ceil (log2 n / 8)]. Why don't we use this instead and let the normalizer handle it?
// This is fairly unreadable!
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


(* Takes a natural number [n] whose binary representation fits in [l] bytes; returns a [string]
 * of length [l] whose first bytes are the little-endian machine representation of integer [n]. *)
assume val string_of_int : l:nat -> n:nat{repr_bytes n <= l} -> Tot (r:string {String.length r = l})
assume val int_of_string : s:string ->
    Tot (n:nat{repr_bytes n <= String.length s /\
             (String.length s = 1 ==> n < 256) /\
             s = string_of_int (String.length s) n})
assume val int_of_string_of_int : l:nat -> n:nat{repr_bytes n <= l} -> Lemma 
  (requires True)
  (ensures n = int_of_string (string_of_int l n))
  [SMTPat (int_of_string (string_of_int l n))]
assume val string_of_hex: string -> Tot string
assume val hex_of_string: string -> Tot string

type byte = Char.char
type cbytes = string

val sum_length : list string -> Tot nat
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

abstract type bytes = b:proto_bytes{good_bytes b}


(* don't have these two, since bytes is not Seq *)
(* val seq_of_bytes: b:bytes -> GTot (Seq.seq byte) *)
(* let seq_of_bytes b = b *)


val exfalso : #a:Type -> u:unit{False} -> Tot a
let rec exfalso #a _ = exfalso ()


val sum_length_append : a:list string -> b:list string -> Lemma 
  (requires True)
  (ensures (sum_length (a @ b) = sum_length a + sum_length b))
  [SMTPat (sum_length (a @ b))]
let rec sum_length_append a b =
  match a with
    | [] -> ()
    | x :: a' -> sum_length_append a' b


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


#reset-options "--z3rlimit 20"

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
      let curr = String.length h - i in
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
#reset-options "--z3rlimit 5"

val concatT_empty : ls:list string -> Tot (r:string{String.length r = sum_length ls})
let rec concatT_empty ls =
  match ls with
  | [] -> ""
  | x :: xs -> x ^ concatT_empty xs
val concat_append : a:list string -> b:list string -> Lemma 
  (requires True)
  (ensures (concatT_empty (a @ b) = (concatT_empty a ^ concatT_empty b)))
  [SMTPat (concatT_empty (a @ b))]
let rec concat_append a b =
  match a with
    | [] -> ()
    | x :: xs -> 
      concat_append xs b
val sum_length_0_concat_empty : ls:list string -> Lemma 
  (requires sum_length ls = 0)
  (ensures concatT_empty ls = "")
  [SMTPat (sum_length ls = 0)]
let rec sum_length_0_concat_empty ls =
  match ls with
  | [] -> ()
  | x :: xs ->
    let _ = assert (String.length x = 0) in
    sum_length_0_concat_empty xs


val lemma_getBytes_2 : ls:list cbytes -> Lemma
  (requires True)
  (ensures getBytes ls 0 (sum_length ls) = concatT_empty ls)
  [SMTPat (getBytes ls 0 (sum_length ls))]
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
          

(* getBytes on sub-range *)
val lemma_getBytes_3: ls:list cbytes -> i:nat{i <= sum_length ls} -> n:nat{i + n <= sum_length ls} -> i2:nat{i <= i2 /\ i2 <= i+n} -> n2:nat{i2+n2<=i+n} -> Lemma
  (requires True)
  (ensures getBytes ls i2 n2 = substringT (getBytes ls i n) (i2 - i) n2)
  // [SMTPat (getBytes ls i2 n2)]
let rec lemma_getBytes_3 ls i n i2 n2 = 
  match ls with
  | [] ->
    ()
  | h :: t ->
    if String.length h <= i then
      lemma_getBytes_3 t (i - String.length h) n (i2 - String.length h) n2
    else
      let curr = String.length h - i in
      if String.length h <= i2 then
        let _ = lemma_getBytes_3 t 0 (n-curr) (i2-String.length h) n2 in
        if n <= curr then
          let _ = assert (n2 = 0) in
          ()
        else
          let _ = substring_prefix (substringT h i curr) (getBytes t 0 (n-curr)) (i2-String.length h) n2 in
          ()
      else
        if n <= curr then
          let _ = substring_sub_range h i n i2 n2 in
          ()
        else
          if i2 + n2 <= String.length h then
            let _ = substring_sub_range h i curr i2 n2 in
            let _ = substring_suffix (substringT h i curr) (i2-i) n2 (getBytes t 0 (n-curr)) in
            ()
          else
            let _ = lemma_getBytes_3 t 0 (n-curr) 0 (i2+n2-String.length h) in
            let _ = substring_sub_range h i curr i2 (String.length h - i2) in
            let _ = substring_append (substringT h i curr) (i2-i) (getBytes t 0 (n-curr)) (i2+n2-String.length h) in
            ()
        

private val get_cbytes : (bytes -> Tot cbytes)
(* val get_cbytes : b:bytes -> Tot (r:cbytes{String.length r = b.length}) *)
let get_cbytes (b:bytes) =
    if b.length = b.max && b.index = 0 then
      (* concatT_empty b.bl *)
      String.concat "" b.bl
    else
      getBytes b.bl b.index b.length


(* a version of get_cbytes that doesn't have the [concatT_empty] part so it's easier to reason about *)
private val get_cbytes' : b:bytes -> Tot (r:cbytes{String.length r = b.length})
let get_cbytes' (b:bytes) =
      getBytes b.bl b.index b.length


val concatT_empty_concatT : ls:list string -> Lemma
  (requires True)
  (ensures concatT "" ls = concatT_empty ls)
  [SMTPat (concatT "" ls)]
let rec concatT_empty_concatT ls =
  match ls with
  | [] -> ()
  | x :: xs ->
    match xs with
    | [] -> ()
    | _ -> concatT_empty_concatT xs


val get_cbytes'_ok : b : bytes -> Lemma
  (requires True)
  (ensures get_cbytes b = get_cbytes' b)
  [SMTPat (get_cbytes b)]
let get_cbytes'_ok b =
  let _ = concat_concatT "" b.bl in
  ()


type bytes_eq (a:bytes) (b:bytes) = (get_cbytes a = get_cbytes b)
assume val bytes_extensionality: a:bytes -> b:bytes -> Lemma
  (requires True)
  (ensures bytes_eq a b <==> a = b)
  (* [SMTPat (bytes_eq a b)] *)


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


val length : bytes -> Tot nat
let length (d:bytes) = d.length


type lbytes (l:nat) = b:bytes{length b = l}


val empty_bytes : lbytes 0
let empty_bytes = 
      {bl = [];
       length = 0;
       index = 0;
       max = 0}


val abytes : (cbytes -> Tot bytes)
let abytes (ba:cbytes) =
    {bl = [ba]; length = String.length ba; index = 0; max = String.length ba}


val createBytes : nat -> byte -> Tot bytes
let createBytes n b = 
    {bl = [String.make n b]; 
    length = n; 
    index = 0; 
    max = n}


val abyte : (byte -> Tot bytes)
let abyte (b:byte) =
    createBytes 1 b


val abyte2 : (byte * byte) -> Tot bytes
let abyte2 (ba1,ba2) =
    let s = String.make 1 ba1 ^ String.make 1 ba2 in
    {bl = [s]; length = 2; index = 0; max = 2}


val cbyte : b:bytes{length b > 0} -> Tot byte
(* let cbyte (b:bytes) = *)
(*   if b.length = 1 then *)
(*     let b1 = getByte b.bl b.index in b1 *)
(*   else failwith "cbyte: expected an array of length 1" *)
let cbyte b =
  let s = getBytes b.bl b.index 1 in
  getT s 0
  

val cbyte2 : b:bytes{length b >= 2} -> Tot (byte * byte)
(* let cbyte2 (b:bytes) = *)
(*     if b.length = 2 then *)
(*       let (b1,b2) = getByte2 b.bl b.index in b1,b2 *)
(*     else failwith "cbyte2: expected an array of length 2" *)
let cbyte2 b =
  let s = getBytes b.bl b.index 2 in
  (getT s 0, getT s 1)


val index : b:bytes -> i:nat{length b > i} -> Tot byte
(* let index (b:bytes) i = *)
(*   if b.length > i then *)
(*     let s = getBytes b.bl b.index b.length in *)
(*     getT s i *)
(*   else failwith "index: index out of range" *)
let index b i =
  let s = getBytes b.bl (b.index + i) 1 in
  getT s 0


val equalBytes : b1:bytes -> b2:bytes -> Tot (b:bool{b = (b1=b2)})
let equalBytes a b =
  let _ = bytes_extensionality a b in
  let _ = compare_eq (get_cbytes a) (get_cbytes b) in
  String.compare (get_cbytes a) (get_cbytes b) = 0 


val xor: l:nat -> lbytes l -> lbytes l -> Tot (lbytes l)
let xor len s1 s2 =
  let s1 = get_cbytes s1 in
  let s2 = get_cbytes s2 in
  let res = string_xor len s1 s2 in
  abytes res


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


val lemma_op_At_Bar : a:bytes -> b:bytes -> Lemma 
  (requires True)
  (ensures get_cbytes (a @| b) = (get_cbytes a ^ get_cbytes b))
  [SMTPat (get_cbytes (a @| b))]
let lemma_op_At_Bar a b = ()


val lemma_split_1 : b:bytes -> i:nat{i <= length b} -> Lemma (let x = split b i in length (fst x) = i && length (snd x) = length b - i)
let lemma_split_1 b i = ()


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


val lemma_split_3 : b:bytes -> i:nat{i <= length b} -> Lemma 
  (let p = split b i in 
   bytes_eq (fst p @| snd p) b)
let lemma_split_3 b i =
  let _ = lemma_split_2 b i in
  let _ = split_append (get_cbytes b) i in
  ()


val lemma_split : s:bytes -> i:nat{(0 <= i /\ i <= length s)} -> Lemma
  (ensures ((fst (split s i)) @| (snd (split s i)) = s))
let lemma_split s i = 
  let _ = lemma_split_3 s i in
  let _ = bytes_extensionality ((fst (split s i)) @| (snd (split s i))) s in
  ()

  
val split_eq: s:bytes -> i:nat{(0 <= i /\ i <= length s)} -> Pure
  (x:(bytes * bytes){length (fst x) = i && length (snd x) = length s - i})
  (requires True)
  (ensures (fun x -> ((fst x) @| (snd x) = s)))
let split_eq s i =
  let _ = lemma_split s i in
  split s i
  

val lemma_append_inj: s1:bytes -> s2:bytes -> t1:bytes -> t2:bytes {length s1 = length t1 \/ length s2 = length t2} ->
  Lemma (requires ((s1 @| s2) = (t1 @| t2)))
        (ensures (s1 = t1 /\ s2 = t2))
let lemma_append_inj s1 s2 t1 t2 = 
  let _ = assert (get_cbytes (s1 @| s2) = get_cbytes (t1 @| t2)) in
  let _ = string_append_inj (get_cbytes s1) (get_cbytes s2) (get_cbytes t1) (get_cbytes t2) in
  let _ = bytes_extensionality s1 t1 in
  let _ = bytes_extensionality s2 t2 in
  ()


val split2 : b:bytes -> n1:nat{n1 <= length b} -> n2:nat{n1 + n2 <= length b} -> Tot (lbytes n1 * lbytes n2 * lbytes (length b - n1 - n2))


let split2 bs n1 n2 =
  let (a, bc) = split bs n1 in
  let (b, c) = split bc n2 in
  (a, b, c)
  

val bytes_of_int : l:nat -> n:nat{repr_bytes n <= l} -> Tot (lbytes l)
let bytes_of_int l n =
  let s = string_of_int l n in
  abytes s


val int_of_bytes : b:bytes ->
    Tot (n:nat{repr_bytes n <= length b /\
             (length b = 1 ==> n < 256) /\
             b=bytes_of_int (length b) n})
             

let int_of_bytes (b:bytes) =
  let c = get_cbytes b in
  let n = int_of_string c in
  let _ = bytes_extensionality b (bytes_of_int (length b) n) in
  n


val abytes_get_cbytes : s:string -> Lemma
  (requires True)
  (ensures get_cbytes (abytes s) = s)
  [SMTPat (get_cbytes (abytes s))]
let abytes_get_cbytes s =
  ()


val int_of_bytes_of_int : l:nat -> n:nat{repr_bytes n <= l} ->
    Lemma (n = int_of_bytes (bytes_of_int l n))
let int_of_bytes_of_int l n =
  ()
  

val byte_of_int: n:nat{n < 256} -> Tot byte
let byte_of_int n =
  lemma_repr_bytes_values n;
  index (bytes_of_int 1 n) 0


val utf8 : string -> Tot bytes
let utf8 (x:string) : bytes = abytes x (* TODO: use Camomile *)


val iutf8_opt : bytes -> Tot (option string)
let iutf8_opt (x:bytes) : option string = Some (get_cbytes x)


val get_cbytes_abytes : b:bytes -> Lemma
  (requires True)
  (ensures abytes (get_cbytes b) = b)
  [SMTPat (abytes (get_cbytes b))]
let get_cbytes_abytes b =
  let _ = bytes_extensionality (abytes (get_cbytes b)) b in
  ()


val iutf8 : m:bytes -> s:string{utf8 s == m}
let iutf8 (x:bytes) = 
  get_cbytes x (* TODO: use Camomile *)


// Pretty printing of bytes for debugging
assume val debug_print_string: string -> Tot string
val print_bytes: bytes -> Tot string
let print_bytes (x:bytes) : string =
  let s = get_cbytes x in
  debug_print_string s


val bytes_of_hex: string -> Tot bytes
let bytes_of_hex s =
  abytes (string_of_hex s)
  

val hex_of_bytes: bytes -> Tot string
let hex_of_bytes b =
  hex_of_string (get_cbytes b)
