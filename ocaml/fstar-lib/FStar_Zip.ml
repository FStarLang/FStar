let zip = Ezgzip.compress
let unzip s = Result.get_ok (Ezgzip.decompress s)

let output_zipped_value (c : out_channel) (x:'a) : unit =
  let str = Marshal.to_string x [] in
  let zstr = zip str in
  let zlen = String.length zstr in
  let b = Bytes.create 8 in
  (* save zlen *)
  Bytes.set_int64_be b 0 (Int64.of_int zlen);
  output c b 0 8;
  (* save ztr *)
  output_string c zstr

let input_zipped_value (c : in_channel) : 'a =
  (* read zlen *)
  let lenbuf = Bytes.create 8 in
  really_input c lenbuf 0 8;
  let zlen = Int64.to_int (Bytes.get_int64_be lenbuf 0) in
  (* read and decode *)
  let zstr = really_input_string c zlen in
  let str = unzip zstr in
  Marshal.from_string str 0
