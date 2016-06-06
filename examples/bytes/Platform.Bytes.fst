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
assume val string_length_append: a:string -> b:string -> Lemma (String.length (a ^ b) = String.length a + String.length b)
assume val string_length_empty: unit -> Lemma (String.length "" = 0)

val string_append : a:string -> b:string -> Tot (res:string{String.length res = String.length a + String.length b})
let string_append a b = 
  let _ = string_length_append a b in 
  a ^ b
val empty_string : s:string{String.length s = 0}
let empty_string = 
  let _ = string_length_empty () in
  ""

(* val sum_length_le : i:nat -> h:cbytes -> t:list cbytes -> Lemma (i <= sum_length (h::t) ==> i - String.length h <= sum_length t) *)
(* let sum_length_le i h t = () *)

(* val sum_length_cons : h:cbytes -> t:list cbytes -> Lemma (sum_length (h::t) = String.length h + sum_length t) (decreases t) *)
(* let rec sum_length_cons h t =  *)
(*   match t with *)
(*    | [] -> () *)
(*    | h' :: t' -> sum_length_cons h' t' *)

val exfalso : #a:Type -> u:unit{False} -> Tot a
let rec exfalso #a _ = exfalso ()

val getBytes : bl:list cbytes -> i:nat{i <= sum_length bl} -> n:nat{i+n <= sum_length bl} -> Tot (b:cbytes{String.length b = n})
let rec getBytes (bl: list cbytes) i n  =
    match bl with
    | [] -> 
      if n = 0
      then empty_string
      else exfalso ()
    | h::t ->
        if i >= (String.length h)
        then getBytes t (i- (String.length h)) n
        else let curr = (String.length h) - i in
             if curr >= n
             then substringT h i n
             else 
             string_append (substringT h i curr) (getBytes t 0 (n-curr))

val string_concat : ls:list string -> Tot (r:string{String.length r = sum_length ls})
let rec string_concat ls =
  match ls with
  | [] -> empty_string
  | x :: xs -> string_append x (string_concat xs)

val get_cbytes : b:bytes -> Tot (r:cbytes{String.length r = b.length})
let get_cbytes (b:bytes) =
    if b.length = b.max && b.index = 0 then
      string_concat b.bl
    else
      getBytes b.bl b.index b.length

val sum_length_append : a:list string -> b:list string -> Lemma (sum_length (a @ b) = sum_length a + sum_length b)
let rec sum_length_append a b =
  match a with
    | [] -> ()
    | x :: a' -> sum_length_append a' b

val op_At_Bar: bytes -> bytes -> Tot bytes
let op_At_Bar (a:bytes) (b:bytes) =
    if a.length + a.index = a.max && b.index = 0 then
      let _ = sum_length_append a.bl b.bl in
      {bl = (a.bl @ b.bl);
       length = a.length + b.length;
       index = a.index;
       max = a.max + b.max}
    else
      {bl = [string_append (get_cbytes a) (get_cbytes b)];
       length = a.length + b.length;
       index = 0;
       max = a.length + b.length}

let op_AtBar = op_At_Bar

val lemma_op_At_Bar : a:bytes -> b:bytes -> Lemma (get_cbytes (a @| b) = (get_cbytes a ^ get_cbytes b))

assume val append_empty : unit -> Lemma (forall s. s ^ "" = s)
assume Append_empty : forall s. s ^ "" = s
assume val empty_append : unit -> Lemma (forall s. ("" ^ s) = s)
assume Empty_append: forall s. "" ^ s = s
assume val append_assoc : unit -> Lemma (forall a b c. (a ^ (b ^ c)) = ((a ^ b) ^ c))
assume Append_assoc : forall a b c. (a ^ (b ^ c)) = ((a ^ b) ^ c)

val concat_append : a:list string -> b:list string -> Lemma (string_concat (a @ b) = (string_concat a ^ string_concat b))
let rec concat_append a b =
  match a with
    | [] -> 
    let _ = empty_append () in
    ()
    | x :: xs -> 
    let _ = append_assoc () in
    let _ = concat_append xs b in
    ()

let lemma_op_At_Bar a b =
  let c = a @| b in
  if a.length + a.index = a.max && b.index = 0 then
    if a.index = 0 then
      ()
    else
      admit ()
  else
    if c.length = c.max && c.index = 0 then
      let _ = append_empty (string_append (get_cbytes a) (get_cbytes b)) in
      ()
    else
      exfalso ()
    
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

let length (d:bytes) = d.length

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

type bytes_eq (a:bytes) (b:bytes) = (get_cbytes a = get_cbytes b)

val split : s:bytes -> i:nat{i <= length s} -> Tot (bytes * bytes)
let split b i =
    {bl = b.bl;
     length = i;
     index = b.index;
     max = b.max},
    {bl = b.bl;
     length = b.length - i;
     index = b.index + i;
     max = b.max}

val lemma_split_1 : s:bytes -> i:nat{i <= length s} -> Lemma (let x = split s i in length (fst x) = i && length (snd x) = length s - i)
let lemma_split_1 s i = ()

val lemma_split2 : s:bytes -> i:nat{i <= length s} -> Lemma (let x = split s i in bytes_eq ((fst x) @| (snd x)) s)
let lemma_split2 s i = ()

val split_eq : s:bytes -> i:nat{i <= length s} -> Tot (x:(bytes * bytes){length (fst x) = i && length (snd x) = length s - i /\ bytes_eq ((fst x) @| (snd x)) s})
let split_eq = 
  split

(* val split_eq: s:bytes -> i:nat{(0 <= i /\ i <= length s)} -> Pure *)
(*   (x:(bytes * bytes){length (fst x) = i && length (snd x) = length s - i}) *)
(*   (requires True) *)
(*   (ensures (fun x -> ((fst x) @| (snd x) = s))) *)

