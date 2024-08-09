#r "../../../bin/ulibfs.dll"
#r "bin/Debug/net6.0/Huffman.dll"
open Huffman

let t = huffman (List.map (fun (c,n) -> (c, Prims.of_int n))
  [('A',2); ('E',5); ('F',1); ('H',1); ('I',1); ('L',1);
   ('N',1); ('R',1); ('S',2); ('T',3); ('U',1); (' ',2)]);;
int (Huffman.__proj__Node__item__w t);;
let ss = Seq.toList "THE ESSENTIAL FEATURE";;
let e = match (encode t ss) with | FStar_Pervasives_Native.Some e -> e | _ -> failwith "Failed to encode data";;
let d = match (decode t e) with | FStar_Pervasives_Native.Some d -> d | _ -> failwith "Failed to decode data";;
printf "%s" ((System.String(Array.ofList d)) + "\n");;
