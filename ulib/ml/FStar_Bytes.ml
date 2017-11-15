module FStar_Bytes = struct

  type byte = int
  type nat = int
  type cbytes = string
  type bytes = string

  let lemma_repr_bytes_values n = ()

  let cbyte (b:bytes) =
    try int_of_char (String.get b 0)
    with _ -> failwith "cbyte: called on empty string"

  let cbyte2 (b:bytes) =
    try (int_of_char (String.get b 0), int_of_char (String.get b 1))
    with _ -> failwith "cbyte2: need at least length 2"

  let index (b:bytes) i =
    try int_of_char (String.get b (Z.to_int i))
    with _ -> failwith "index: called out of bound"

  let get_cbytes (b:bytes) = b
  let abytes (ba:cbytes) = ba
  let abyte (ba:byte) = String.make 1 (char_of_int ba)
  let abyte2 (ba1,ba2) =
    String.init 2 (fun i -> if i = 0 then char_of_int ba1 else char_of_int ba2)

  let (@|) (a:bytes) (b:bytes) = a ^ b
  let op_At_Bar a b = a @| b
  let op_AtBar a b = a @| b

  let split (b:bytes) i : bytes * bytes =
    try
      let i = Z.to_int i in
      let b1 = String.sub b 0 i in
      let b2 = String.sub b i (String.length b - i) in
      (b1, b2)
    with _ -> failwith "split: out of bound"
  let split_eq = split
  let length (b:bytes) = Z.of_int (String.length b)

  let empty_bytes = ""
  let createBytes len (value:int) : bytes =
      let len = Z.to_int len in
      try abytes (String.make len (char_of_int value))
      with _ -> failwith "Default integer for createBytes was greater than max_value"

  let initBytes len f : bytes =
      let len = Z.to_int len in
      try abytes (String.init len (fun i -> char_of_int (f (Z.of_int i))))
      with _ -> failwith "Platform.Bytes.initBytes: invalid char returned"

  type 'a lbytes = bytes

  let bytes_of_int nb i =
    let nb = Z.to_int nb in
    let i = Z.to_int64 i in
    if Int64.compare i Int64.zero < 0 then failwith "Negative 64bit.";
    let rec put_bytes bb lb n =
      if lb = 0 then failwith "not enough bytes"
      else
        begin
          let lown = Int64.logand n (Int64.of_int 255) in
          Bytes.set bb (lb-1) (char_of_int (Int64.to_int lown));
          let ns = Int64.div n (Int64.of_int 256) in
          if Int64.compare ns Int64.zero > 0 then
            put_bytes bb (lb-1) ns
          else bb
        end
    in
    let b = Bytes.make nb (char_of_int 0) in
    Bytes.to_string (put_bytes b nb i)

  let int_of_bytes (b:bytes) =
      let x = ref 0 in
      let len = String.length b in
      for y = 0 to len-1 do
          x := 256 * !x + (int_of_char (String.get b y))
      done;
      Z.of_int !x

  let equalBytes (b1:bytes) (b2:bytes) = b1 = b2

  let xor len s1 s2 =
      let len = Z.to_int len in
      let init i = char_of_int ((int_of_char s1.[i]) lxor (int_of_char s2.[i])) in
      String.init len init

  let split2 (b:bytes) i j : bytes * bytes * bytes =
    let b1, b2 = split b i in
    let b2a, b2b = split b2 j in
    (b1, b2a, b2b)

  let utf8 (x:string) : bytes = x (* TODO: use Camomile *)
  let iutf8 (x:bytes) : string = x (* TODO: use Camomile *)
  let iutf8_opt (x:bytes) : string option = Some (x)

  let print_bytes (s:bytes) : string =
    let res = ref "" in
    for i = 0 to String.length s - 1 do
      res := !res ^ (Printf.sprintf "%02X" (int_of_char s.[i]));
    done; !res

  let byte_of_int i = Z.to_int i

  (* Some helpers to deal with the conversation from hex literals to bytes and
   * conversely. Mostly for tests. *)

  let digit_to_int c = match c with
    | '0'..'9' -> Char.code c - Char.code '0'
    | 'a'..'f' -> 10 + Char.code c - Char.code 'a'
    | _ -> failwith "hex_to_char: invalid hex digit"

  let hex_to_char a b =
    Char.chr ((digit_to_int a) lsl 4 + digit_to_int b)

  let char_to_hex c =
    let n = Char.code c in
    let digits = "0123456789abcdef" in
    digits.[n lsr 4], digits.[n land 0x0f]

  let hex_of_string s =
    let n = String.length s in
    let buf = Buffer.create n in
    for i = 0 to n - 1 do
      let d1,d2 = char_to_hex s.[i] in
      Buffer.add_char buf d1;
      Buffer.add_char buf d2;
    done;
    Buffer.contents buf

  let string_of_hex s =
    let n = String.length s in
    if n mod 2 <> 0 then
      failwith "string_of_hex: invalid length"
    else
      let res = Bytes.create (n/2) in
      let rec aux i =
        if i >= n then ()
        else (
          Bytes.set res (i/2) (hex_to_char s.[i] s.[i+1]);
          aux (i+2)
        )
      in
      aux 0;
      res

  let string_of_bytes b = b
  let bytes_of_string s = s

  let bytes_of_hex s = string_of_hex s
  let hex_of_bytes b = hex_of_string b

end
