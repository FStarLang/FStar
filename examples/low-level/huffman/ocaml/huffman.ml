(**********)
(* BASICS *)
(**********)

type symbol_type = int

(* maximum value in input stream *)
let symbol_value_bound = 257;;

(* bits needed to represent symbols up to the bound *)
let bits_per_symbol =
  let rec aux n b =
    let n' = n lsr 1 in
    if n' = 0 then b
    else aux n' (b+1) in
  aux (symbol_value_bound-1) 1

(* bytes needed to represent symbols up to the bound *)
let bytes_per_symbol = 
  if (bits_per_symbol mod 8) = 0 then bits_per_symbol / 8 
  else (bits_per_symbol / 8) + 1

(***************)
(* ENCODING *)
(***************)

(* main data structure. A node is part of a Huffman tree, and it's what is in the histogram.
   The algorithm will construct a histogram of nodes, then construct a tree out of these, 
   and using this tree will set the "code" of each node, which is used in the final encoding. *)
type node =
    { mutable frequency: int; 
      mutable next: node;
      zero_child: node;
      one_child: node; 
      symbol: symbol_type;
      mutable code: string;
    };;

(* dummy "null" node, so that we don't have to use option types. *)

let rec null_node = 
  { frequency = -1;
    next = null_node;
    zero_child = null_node;
    one_child = null_node;
    symbol = 0;
    code = "" } 

let is_null n =
  match n with
      { frequency = -1 } -> true
    | _ -> false 
      
(* Maintains a mutable list of nodes, sorted by the node.frequency field *)

module type NODE_LIST =
  sig
    type node_list
    val new_list : unit -> node_list
    val is_empty : node_list -> bool
    val is_singleton : node_list -> bool
    val pop_two : node_list -> node*node
    val contents : node_list -> node
    val insert_in_ordered_list : node -> node_list -> unit
    val print_list_nodes : node_list -> bool -> unit
  end

module NodeList : NODE_LIST = 
  struct 
    type node_list = node ref
    let is_empty l = is_null !l
    let new_list () = ref null_node
    let contents l = !l
    (* Insert by mutation. The order is according to the frequency field. *)
    let rec insert_in_ordered_list (the_node:node) (the_list:node_list) =
      if is_null !the_list then 
	the_list := the_node
      else
	  if the_node.frequency <= (!the_list).frequency then
	    (the_node.next <- !the_list; 
	     the_list := the_node)
	  else 
	    (let rec aux l =
	      if is_null l.next then
		(the_node.next <- null_node;
		 l.next <- the_node)
	      else
		  if the_node.frequency <= l.next.frequency then
		    (the_node.next <- l.next;
		     l.next <- the_node)
		  else
		    aux l.next in
	     aux !the_list)
    let is_singleton l = (not (is_empty l)) && (is_null (!l).next)
    (* removes the first two elements of the list (with the smallest frequencies) *)
    let pop_two l =
      let res = (!l,(!l).next) in
      l := (!l).next.next;
      res
    (* DEBUG: prints list of nodes (for histogram) *)
    let print_list_nodes l flag =
      let rec aux tree flag =
	if flag then
	  Printf.printf "Symbol Histogram: \n";
	if is_null tree then 
	  print_endline ""
	else
	  (Printf.printf "%04x: %d  " tree.symbol tree.frequency;
	   aux tree.next false) in
      aux !l flag
  end

(* Computes a histogram (modifying the [histogram] argument in place) of 
   the symbol_type values (integers) appearing in [symbol_stream]. Assumes that 
   no symbol_type value exceeds [symbol_value_bound] (a global) and that 
   [histogram] is at least that size. *)
let compute_histogram
    (symbol_stream: symbol_type array)
    (histogram: node option array) : unit =
  let symbol_stream_length = Array.length symbol_stream in
  for i = 0 to (symbol_stream_length-1) do
    let sym = symbol_stream.(i) in
    let the_leaf = histogram.(sym)  in (* index into histogram from symbol *)
    match the_leaf with
	None ->
	  let the_leaf = 
	    { frequency = 1;
	      next = null_node;
	      zero_child = null_node;
	      one_child = null_node;
	      symbol = sym;
	      code = "" } in
	  histogram.(sym) <- Some the_leaf
      | Some nd ->
	nd.frequency <- nd.frequency + 1
  done;
  ()

(* called by build_huffman_tree: recursively computes and stores the codes in each leaf of the tree *)
let rec compute_code_strings 
    (tree:node)
    (code_string:bytes)
    (code_string_pos:int) =
  let zc_nd = tree.zero_child in
  let one_nd = tree.one_child in
  if is_null zc_nd then
    tree.code <- Bytes.unsafe_to_string (Bytes.sub code_string 0 code_string_pos)
  else
    (Bytes.set code_string code_string_pos '0';
     compute_code_strings zc_nd code_string (code_string_pos+1);
     Bytes.set code_string code_string_pos '1';
     compute_code_strings one_nd code_string (code_string_pos+1))
;;

(* Builds a huffman tree. Does this by making a sorted list of all of the elements in
   the histogram, according to frequency. Then it iteratively builds up the tree by
   pulling pairs of elements from the front of the list, until none remain. At the end,
   it uses the tree to set the code fields of the leaves of the tree, which are the nodes
   that were already in the histogram. That way, when we go through the histogram 
   later, the nodes will have the codes we need. *)
let build_huffman_tree
    (histogram:node option array): node =
  (* make ordered list, sorted by frequency *)
  let tree = NodeList.new_list () in
  for i = 0 to (symbol_value_bound-1) do
    match histogram.(i) with
	Some nd -> NodeList.insert_in_ordered_list nd tree
      | None -> ()
  done;
  (* debug *)
  NodeList.print_list_nodes tree true;
  (* Build the tree recursively combining the first two (lowest freq) nodes *)
  while not (NodeList.is_singleton tree) do
    let (n1,n2) = NodeList.pop_two tree in
    let new_nd = 
      { frequency = n1.frequency + n2.frequency;
	zero_child = n1;
	one_child = n2;
	next = null_node;
	symbol = -1; (* don't care *)
	code = "" (* don't care *) } in
    NodeList.insert_in_ordered_list new_nd tree
  done;
  (* compute codes *)
  let tree' = NodeList.contents tree in
  let temp_code = Bytes.create symbol_value_bound in
  compute_code_strings tree' temp_code 0;
  tree'

(* Encodes/compresses the input stream using the given histogram.The symbol stream is the input to encode;
   The histogram contains the frequencies of the symbols in the stream;
   The encoded_stream is modified in place; it should be at least as large as the input stream;
   Returns the number of bytes written to the encoded stream *)
let encode_stream
    (symbol_stream:symbol_type array)
    (histogram:node option array)
    (encoded_stream:bytes) =
  let symbol_stream_length = Array.length symbol_stream in
  Bytes.set encoded_stream 0 (Char.chr 0);
  let rec aux sym_idx ofs mask =
    if sym_idx = symbol_stream_length then ofs+1 (* length of the code string *)
    else
      let the_node' = histogram.(symbol_stream.(sym_idx)) in
      match the_node' with
	  None -> (Printf.printf "error in histogram!"; Pervasives.exit 1)
	| Some the_node -> 
	  (let the_code_string = the_node.code in
	  let the_code_string_length = String.length the_code_string in
	  let rec aux2 ofs cs_ofs mask =
	    if (cs_ofs = the_code_string_length) then (ofs,mask)
	    else 
	      (if (String.get the_code_string cs_ofs) = '1' then 
		  (let curr = Char.code (Bytes.get encoded_stream ofs) in
		  let nv = curr lor mask in
		  Bytes.set encoded_stream ofs (Char.chr nv));
	       let mask' = mask lsl 1 in
	       if (mask' <> 0 && mask' < 256) then
		 aux2 ofs (cs_ofs+1) mask' 
	       else
		 (Bytes.set encoded_stream (ofs+1) (Char.chr 0);
		  aux2 (ofs+1) (cs_ofs+1) 1)) in
	  let (ofs',mask') = aux2 ofs 0 mask in
	  aux (sym_idx+1) ofs' mask') in
  aux 0 0 1

(* DEBUG: Prints the stream encoded with the encode_stream function *)
let print_stream 
    (encoded_stream:bytes)
    (stream_len:int) =
  Printf.printf "Code: ";
  let rec aux i =
    if i = stream_len then ()
    else
      let b = Bytes.get encoded_stream i in
      let rec aux2 mask =
	if (mask <> 0 && mask < 256) then
	  (let b' = (Char.code b) land mask in
	   Printf.printf "%d " (if b' <> 0 then 1 else 0);
	   aux2 (mask lsl 1))
	else () in
      aux2 1;
      aux (i+1) in
  aux 0

(* Takes the given Huffman [tree], and packs it into the [packed_tree] bytearray
   (which should be preallocated with sufficient space), starting at offset [ofs]. *)
let rec pack_tree_iter (tree:node) (packed_tree:bytes) (ofs:int) : int =
  let rec write_sym sym nb sofs =
    if nb = 0 then sofs
    else
      (let the_sym = sym land 0xFF in
       Bytes.set packed_tree sofs (Char.chr the_sym);
       write_sym (sym lsr 8) (nb-1) (sofs+1)) in
  (* leaf tag *)
  if is_null tree.zero_child then 
    (Bytes.set packed_tree ofs (Char.chr 1);
     write_sym tree.symbol bytes_per_symbol (ofs+1))
  (* node tag *)
  else 
    (Bytes.set packed_tree ofs (Char.chr 0);
     let ofs' = pack_tree_iter tree.zero_child packed_tree (ofs+1) in
     pack_tree_iter tree.one_child packed_tree ofs')

(* Determines the "size" of the [tree], by counting its leaves. *)
let rec count_leaves (tree:node) :int =
  let ndzero = tree.zero_child in
  let ndone = tree.one_child in
  if is_null ndzero then 1
  else 
    let x = count_leaves ndzero in
    let y = count_leaves ndone in 
    x+y

(* Packs the given Huffman [tree] into a bytearray, which is returned,
   along with the length (which might be shorter than the physical
   length of the bytearray. *)
let pack_huffman_tree (tree:node) : bytes*int =
  let num_leaves = count_leaves tree in
  let packed_tree_sz = 2*num_leaves+bytes_per_symbol*num_leaves-1 in
  let packed_tree = Bytes.create packed_tree_sz in
  let len = pack_tree_iter tree packed_tree 0 in
  packed_tree,len

(* DEBUG: prints the packed huffman tree *)
let print_tree (packed_tree:bytes) (tree_size:int) =
  Printf.printf "\nTree (%d): " tree_size;
  let rec aux i =
    if i >= tree_size then ()
    else
      let b = Bytes.get packed_tree i in
      if (Char.code b) = 0 then
	(Printf.printf "%d " (Char.code b);
	 aux (i+1))
      else
	(let b1 = Bytes.get packed_tree (i+1) in
	let b2 = Bytes.get packed_tree (i+2) in
	Printf.printf "%d:%02x%02x " (Char.code b) (Char.code b1) (Char.code b2);
	aux (i+3)) in
  aux 0

(* Top-level routine to perform huffman coding:
   [symbol_stream] is an array of symbols that are to be compressed;
   [encoded_stream] is a bytearray in which to store the compressed stream
     (should be at least the same length as symbol_stream, in case there is
     no compression)
   Returns a triple containing the packed huffman tree (as a bytearray), 
     the length of valid data in the packed tree array,
     and the length of the valid data in the encoded stream
*)
let huffman_encode 
    (symbol_stream:symbol_type array)
    (encoded_stream:bytes) : bytes*int*int =
  let histogram = Array.make symbol_value_bound None in
  compute_histogram symbol_stream histogram;
  let tree = build_huffman_tree histogram in
  Printf.printf "leaves in tree = %d\n" (count_leaves tree);
  let encoded_len = encode_stream symbol_stream histogram encoded_stream in
  let packed_tree,packed_len = pack_huffman_tree tree in
  packed_tree,packed_len,encoded_len
;;

(***************)
(* DECODING *)
(***************)

type code_node = (* used for decoding *)
    { cn_zero_child : code_node;
      cn_one_child : code_node;
      cn_symbol : symbol_type }

let rec null_code_node = 
  { cn_zero_child = null_code_node;
    cn_one_child = null_code_node;
    cn_symbol = -1; }

let is_null_cn cn = cn.cn_symbol = (-1)

module Reader =
  struct
    type t = (bytes * int) ref (* bytearray and offset *)
    let make_reader arr = ref (arr,0)
    let read_byte x =
      let (arr,ofs) = !x in
      if (ofs >= Bytes.length arr) then failwith "no more data"
      else 
	(let b = Bytes.get arr ofs in
	 x := (arr,ofs + 1);
	 b)
    let get_ofs x = let (arr,ofs) = !x in ofs
  end

let rec read_huffman_tree (file:Reader.t) : code_node =
  let the_byte = Reader.read_byte file in
  (* Printf.printf "%d " (Char.code the_byte); *)
  if (Char.code the_byte) = 0 then
    let zero_child = read_huffman_tree file in
    let one_child = read_huffman_tree file in
    { cn_zero_child = zero_child;
      cn_one_child = one_child;
      cn_symbol = 0; }
  else if (Char.code the_byte) = 1 then
    (let rec read_sym sym nb exp =
      if nb = 0 then sym
      else
	(let the_byte = Reader.read_byte file in
	 let sym' = sym + (Char.code the_byte) * exp in
	 read_sym sym' (nb-1) (exp lsl 8)) in
     let sym = read_sym 0 bytes_per_symbol 1 in
     (* Printf.printf "%04x " sym; *)
     { cn_zero_child = null_code_node; 
       cn_one_child = null_code_node;
       cn_symbol = sym })
  else
    failwith "Error reading Huffman Tree!"

let read_and_huffman_decode
    (file:Reader.t) 
    (t:code_node)
    (symbol_stream:symbol_type array) =
  let rec find_sym tree mask (b:char) =
    if is_null_cn tree.cn_zero_child then (tree.cn_symbol,mask,b)
    else
      if (mask <> 0 && mask < 256) then
	(if (mask land (Char.code b)) <> 0 then
	  find_sym tree.cn_one_child (mask lsl 1) b
	else
	  find_sym tree.cn_zero_child (mask lsl 1) b)
      else
	find_sym tree 1 (Reader.read_byte file) in
  let count = Array.length symbol_stream in
  let rec iter i len mask (b:char) =
    if (i >= len) then ()
    else
      (let sym,mask',b' = find_sym t mask b in
       Array.set symbol_stream i sym;
       iter (i+1) count mask' b') in
  iter 0 count 0 '0';;

(* TEST *)

let print_int_arr arr =
  let len = Array.length arr in
  for i=0 to (len-1) do
    Printf.printf "%d " arr.(i)
  done;
  print_endline "";;

(* Encode it *)
let test_inp = [| 1;1;2;2;3;1;5;4;1;8 |];;
let test_len = Array.length test_inp;;
let test_oup = Bytes.create 10;;
let packed_tree,packed_len,encoded_len = huffman_encode test_inp test_oup;;
print_int_arr test_inp;;
print_stream test_oup encoded_len;;
print_tree packed_tree packed_len;;
print_endline "";;

(* Store it *)
let outbytes = Bytes.create (packed_len+encoded_len);;
Bytes.blit packed_tree 0 outbytes 0 packed_len;;
Bytes.blit test_oup 0 outbytes packed_len encoded_len;;

(* Decode it *)
let f = Reader.make_reader outbytes;;
let cn_tree = read_huffman_tree f;;
let test_res = Array.make test_len 0;;
read_and_huffman_decode f cn_tree test_res;;
print_int_arr test_res;;
