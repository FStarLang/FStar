type symbol_type = int
type code_type = char

let num_symbol_values = 10;;

type node =
    { mutable frequency: int; 
      mutable next: node;
      mutable children: (node*node);
      mutable symbol: symbol_type;
      mutable code: string;
    };;

let rec null_node = 
  { frequency = -1;
    next = null_node;
    children = (null_node, null_node);
    symbol = 0;
    code = "" } 

let is_null n =
  match n with
      { frequency = -1 } -> true
    | _ -> false 
      
module type NODE_LIST =
  sig
    type node_list
    val new_list : unit -> node_list
    val is_empty : node_list -> bool
    val is_singleton : node_list -> bool
    val pop_two : node_list -> node*node
    val contents : node_list -> node
    val print_list_nodes : node_list -> bool -> unit
    val insert_in_ordered_list : node -> node_list -> unit
  end

module NodeList : NODE_LIST = 
  struct 
    type node_list = node ref
    let is_empty l = is_null !l
    let new_list () = ref null_node
    let contents l = !l
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
    let pop_two l =
      let res = (!l,(!l).next) in
      l := (!l).next.next;
      res
  end

let rec count_leaves (tree:node) :int =
  match tree.children with
      (ndzero, ndone) ->
	if is_null ndzero then 1
	else 
	  let x = count_leaves ndzero in
	  let y = count_leaves ndone in 
	  x+y

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
	      children = (null_node,null_node);
	      symbol = sym;
	      code = "" } in
	  histogram.(sym) <- Some the_leaf
      | Some nd ->
	nd.frequency <- nd.frequency + 1
  done;
  ()

(* recursively computes and stores the codes in each leaf of the tree *)
let rec compute_code_strings 
    (tree:node)
    (code_string:bytes)
    (code_string_pos:int) =
  match (tree.children) with
      (zc_nd, one_nd) ->
	if is_null zc_nd then
	  tree.code <- Bytes.unsafe_to_string (Bytes.sub code_string 0 code_string_pos)
	else
	  (Bytes.set code_string code_string_pos '0';
	   compute_code_strings zc_nd code_string (code_string_pos+1);
	   Bytes.set code_string code_string_pos '1';
	   compute_code_strings one_nd code_string (code_string_pos+1))
;;

let build_huffman_tree
    (histogram:node option array): node =
  (* make ordered list, sorted by frequency *)
  let tree = NodeList.new_list () in
  for i = 0 to (num_symbol_values-1) do
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
	children = (n1,n2);
	next = null_node;
	symbol = -1; (* don't care *)
	code = "" (* don't care *) } in
    NodeList.insert_in_ordered_list new_nd tree
  done;
  (* compute codes *)
  let tree' = NodeList.contents tree in
  let temp_code = Bytes.create num_symbol_values in
  compute_code_strings tree' temp_code 0;
  tree'

(* The symbol stream is the input to encode;
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


let huffman_encode 
    (symbol_stream:symbol_type array)
    (encoded_stream:bytes) =
  (* XXX return packed tree too *)

  let histogram = Array.make num_symbol_values None in
  compute_histogram symbol_stream histogram;
  let tree = build_huffman_tree histogram in
  Printf.printf "leaves in tree = %d\n" (count_leaves tree);
  let encoded_len = encode_stream symbol_stream histogram encoded_stream in
  (encoded_len,tree,histogram)

let test_inp = [| 1;1;2;2;3;1;5;4;1;8 |];;
let test_oup = Bytes.create 10;;
let test_hist = Array.make num_symbol_values None;;
compute_histogram test_inp test_hist;;
let tree = build_huffman_tree test_hist;;
Printf.printf "leaves in tree = %d\n" (count_leaves tree);;
let encoded_len = encode_stream test_inp test_hist test_oup;;

(*    
int huffman_encode (SymbolType *symbol_stream, int symbol_stream_length, Byte **packed_huffman_tree, int *huffman_tree_size, CodeType *encoded_stream)
                            
                           
                                         /* to be malloced */
                         
                                         /* already malloced */
  {
  struct node *histogram[NUM_SYMBOL_VALUES];
  struct node *huffman_tree;
  int encoded_stream_length;
  register int i;
  
  /* initialize histogram */
  for (i=0; i<NUM_SYMBOL_VALUES; i++)  histogram[i] = (struct node * ) NULL;
  
  compute_histogram(symbol_stream, symbol_stream_length, histogram);
  build_huffman_tree(histogram, &huffman_tree);
  encoded_stream_length = 
    encode_stream(symbol_stream, symbol_stream_length, histogram, encoded_stream);
  *huffman_tree_size = pack_huffman_tree(huffman_tree, packed_huffman_tree);
  free_tree_nodes(huffman_tree);
  return (encoded_stream_length);
  }
					     *)
