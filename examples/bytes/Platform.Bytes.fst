module Platform.Bytes
open FStar

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

let rec getByte (bl:list cbytes) (i:int) =
  match bl with
    | Nil -> failwith "getByte: array out of bounds"
    | h::t -> 
      if i >= String.length h then 
        getByte t (i-String.length h)
      else 
        String.get h i

let rec getByte2 (bl: list cbytes) i : byte * byte =
    match bl with
   | Nil -> failwith "array out of bounds"
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

let rec getBytes (bl: list cbytes) i n  =
    match bl with
    | Nil -> if n > 0 then failwith "getBytes: array out of bounds" else ""
    | h::t ->
        if i >= (String.length h)
        then getBytes t (i- (String.length h)) n
        else let curr = (String.length h) - i in
             if curr >= n
             then String.substring h i n
             else (String.substring h i curr) ^ (getBytes t 0 (n-curr))

type bytes = {
       (*  A series of strings whose total concatenated length is [max]. *)
       bl: list cbytes;
       max: nat;
       (* The length of the subset. *)
       length: nat;
       (* The start index of the subset. *)
       index: nat;
       }
  
