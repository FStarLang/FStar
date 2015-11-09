(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi Ffibridge --admit_fsi FStar.Set --admit_fsi FStar.String --admit_fsi FStar.IO --admit_fsi Runtime --admit_fsi FStar.Seq;
    variables:CONTRIB=../../contrib;
    other-files:classical.fst ext.fst set.fsi heap.fst st.fst all.fst seq.fsi seqproperties.fst ghost.fst listTot.fst ordset.fsi ordmap.fsi list.fst io.fsti string.fsi prins.fst ast.fst ffibridge.fsi sem.fst $CONTRIB/Platform/fst/Bytes.fst runtime.fsi print.fst
 --*)

module Circuit

open Prins
open AST
open Semantics

open FStar.IO

open FStar.List

open FStar.OrdMap
open FStar.OrdSet

type wrange = int * int

type binop = | Gt | Eq

type celt =
  | Input     : prin -> wrange -> celt
  | Output    : prin -> wrange -> celt
  | BinOp     : binop -> wrange -> wrange -> wrange -> celt  //result, arg1, arg2
  | Const_nat : wrange -> nat -> celt
  | Const_bool: wrange -> bool -> celt
  | Mux       : wrange -> wrange -> wrange -> wrange -> celt  //result range, else branch range, then branch range, condition range

type ckt = list celt

val string_cmp: string -> string -> Tot bool
let string_cmp s1 s2 = if FStar.String.compare s1 s2 < 1 then true else false

val varname_cmp: varname -> varname -> Tot bool
let varname_cmp v1 v2 = string_cmp (name_of_var v1) (name_of_var v2)

assume String_cmp_is_total_order: total_order string string_cmp
assume Varname_cmp_is_total_order: total_order varname varname_cmp

type varset = ordset varname varname_cmp

val fvs: exp -> varset
val fvs_l: list exp -> varset
let rec fvs e = match e with
  | E_box e1 e2            -> union (fvs e1) (fvs e2)
  | E_unbox e'             -> fvs e'
  | E_const _              -> empty
  | E_var x                -> singleton x
  | E_let x e1 e2          -> union (fvs e1) (remove x (fvs e2))
  | E_ffi 'a 'b _ _ _ args _ -> fvs_l args
  | E_cond e e1 e2         -> union (fvs e) (union (fvs e1) (fvs e2))
  | _                      -> failwith "Expression form not supported"

and fvs_l = function
  | []   -> empty
  | a::tl -> union (fvs a) (fvs_l tl)

val is_nat: typ -> Tot bool
let is_nat t = match t with
  | T_cons s _ -> s = "Prims.int"
  | _          -> false

type inputmap = ordmap prin varset p_cmp

(*
 * Currently there is no support for things like boxes of boxes
 *)
val supported_box_content: typ -> Tot bool
let supported_box_content t = match t with
  | T_bool     -> true
  | T_cons _ _ -> is_nat t
  | _          -> false

val supported_input_type: typ -> Tot bool
let supported_input_type t = match t with
  | T_bool     -> true
  | T_cons _ _ -> is_nat t
  | T_box t'   -> supported_box_content t'
  | _ -> false

val assign_prin: prins -> varname -> env -> prin
let assign_prin ps v en =
  let Var s t = v in
  if supported_input_type t then
    match t with
      | T_bool     -> Some.v (choose ps)
      | T_cons _ _ -> Some.v (choose ps)
      | T_box t'  ->
    	let dv_opt = en v in
	if dv_opt = None then failwith "A free variable was not found in environment"
	else
	  let Some (D_v _ v') = dv_opt in
	  let p =
	    match v' with
	      | V_box ps' _ ->
		if subset ps' ps then Some.v (choose ps')
		else failwith "Values boxed for non-ps are not supported"
	      | _ -> failwith "Impossible: T_box for non V_box value!"
	  in
	  p
  else failwith "Input type not supported"

(*
 * we are going to assign each free variable as input of some party
 *)
val assign_inps: prins -> varset -> env -> inputmap
let rec assign_inps ps fvars en =
  if fvars = empty then OrdMap.empty
  else
    let Some v = choose fvars in
    let fvars' = remove v fvars in
    let p = assign_prin ps v en in
    print_string "Assigned "; print_string (Print.prin_to_string p); print_string " to "; print_string (name_of_var v); print_string "\n";
    let m = assign_inps ps fvars' en in
    if contains p m then
      let s = Some.v (select p m) in
      update p (union s (singleton v)) m
    else
      update p (singleton v) m

(* Counter for generating free wire ids *)
let ctr :ref int = alloc 1

let init_ctr (x:unit) = ctr := 1

val alloc_wires: n:int{n > 0} -> St wrange
let alloc_wires n =
  let r = (!ctr + 1, !ctr + n) in
  ctr := !ctr + n;
  r

type cktenv = string -> Tot (option wrange)

let natsize = 4

val size: typ -> (n:int{n > 0})
let rec size t = match t with
  | T_bool     -> 1
  | T_cons _ _ ->
    if is_nat t then natsize else failwith "Size does not support non-nat cons type"
  | T_box t'   ->
    if supported_box_content t' then size t'
    else failwith "Unsupported box content type in size function"
  | _          -> failwith "Unsupported type in the size function"

val range_to_string: wrange -> string
let range_to_string r =
  strcat "( " (strcat (string_of_int (fst r)) (strcat ", " (strcat (string_of_int (snd r)) ")")))

(*
 * GMW library needs all inputs of a party to be consecutive
 * so, go over the varset and assign wire ids to the inputs
 * also, populate the circuit env with the assigned ranges
 *)
val alloc_input_wires_for_prin: prin -> varset -> wrange -> cktenv -> (wrange * cktenv)
let rec alloc_input_wires_for_prin p vars r cen =
  if vars = empty then (r, cen)
  else
    let Some v = choose vars in
    let vars' = remove v vars in
    let Var s t = v in
    let r' = alloc_wires (size t) in
    print_string "Allocated "; print_string (range_to_string r'); print_string " for variable "; print_string (name_of_var v); print_string "\n";
    let cen' = fun s' -> if s' = s then Some r' else cen s' in
    alloc_input_wires_for_prin p vars' (fst r, snd r') cen'

open FStar.IO

(*
 * call per prin input assignment for all the prins
 *)
val alloc_input_wires: eprins -> inputmap -> ckt -> cktenv -> (ckt * cktenv)
let rec alloc_input_wires eps m cs cen =
  if eps = empty then (cs, cen)
  else
    let Some p = choose eps in
    let eps' = remove p eps in
    if contains p m then
      let Some vars = select p m in
      let (r, cen') = alloc_input_wires_for_prin p vars (!ctr + 1, !ctr) cen in
      print_string "Allocated "; print_string (range_to_string r); print_string " for "; print_string (Print.prin_to_string p); print_string "\n";
      alloc_input_wires eps' m (FStar.List.Tot.append cs [Input p r]) cen'
    else
      alloc_input_wires eps' m cs cen

val const_to_ckt: const -> (ckt * wrange * typ)
let const_to_ckt c = match c with
  | C_bool b       ->
    let r = alloc_wires (size (T_bool)) in
    [Const_bool r b], r, T_bool
  | C_opaque 'a v t ->
    if is_nat t then
      let r = alloc_wires (size t) in
      [Const_nat r (Ffibridge.nat_of_c_opaque c)], r, t
    else failwith "Non-nat opaque constant not supported"
  | _ -> failwith "Constant not supported"

val ffi_name_to_op: string -> (binop * typ)
let ffi_name_to_op s =
  if s = "Prims.(>)" then Gt, T_bool
  else if s = "Prims.op_Equality" then Eq, T_bool
  else failwith "FFI name not supported"

val unbox_t: typ -> typ
let unbox_t t = match t with
  | T_box t' -> t'
  | _ -> failwith "Unbox_t with a non T_box"

val exp_to_ckt: cktenv -> exp -> (ckt * wrange * typ)
let rec exp_to_ckt cen e = match e with
  | E_unbox e' ->
    let cs, r, t = exp_to_ckt cen e' in
    cs, r, unbox_t t
  | E_const c -> const_to_ckt c
  | E_var (Var s t) ->
    let r_opt = cen s in
    if is_None r_opt then failwith "Variable not found in cenv"
    else
      [], Some.v r_opt, t
  | E_let x e1 e2 ->
    let cs1, r1, _ = exp_to_ckt cen e1 in
    let cen' = fun s' -> if s' = name_of_var x then Some r1 else cen s' in
    let cs2, r2, t2 = exp_to_ckt cen' e2 in
    cs1 @ cs2, r2, t2
  | E_ffi 'a 'b _ fname _ args _ ->
    let op, t = ffi_name_to_op fname in
    let a1 = List.hd args in
    let a2 = List.hd (List.tl args) in
    let cs1, r1, _ = exp_to_ckt cen a1 in
    let cs2, r2, _ = exp_to_ckt cen a2 in
    let r3 = alloc_wires (size t) in
    cs1 @ cs2 @ [BinOp op r3 r1 r2], r3, t
  | E_cond e1 e2 e3 ->
    let cs1, r1, _ = exp_to_ckt cen e1 in
    let cs2, r2, t2 = exp_to_ckt cen e2 in
    let cs3, r3, t3 = exp_to_ckt cen e3 in
    let r = alloc_wires (size t2) in
    cs1 @ cs2 @ cs3 @ [Mux r r3 r2 r1], r, t2

  | _ -> failwith "Expression to circuit not supported"

val op_to_string : binop -> Tot string
let op_to_string = function
  | Gt -> "Gt"
  | Eq -> "Eq"

val celt_to_string: celt -> string
let celt_to_string = function
  | Input p r ->
    strcat "Input " (strcat (Print.prin_to_string p) (strcat " " (range_to_string r)))
  | Output p r ->
    strcat "Output " (strcat (Print.prin_to_string p) (strcat " " (range_to_string r)))
  | BinOp op r3 r1 r2 ->
    strcat "Binop " (strcat (op_to_string op) (strcat (range_to_string r3) (strcat " " (strcat (range_to_string r1) (strcat " " (range_to_string r2))))))
  | Const_nat r n ->
    strcat "Const_nat " (strcat (range_to_string r) (strcat " " (string_of_int n)))
  | Const_bool r n ->
    strcat "Const_bool " (strcat (range_to_string r) (strcat " " (string_of_bool n)))
  | Mux r r3 r2 r1 ->
    strcat "Mux " (strcat (range_to_string r) (strcat " " (strcat (range_to_string r3) (strcat " " (strcat (range_to_string r2) (strcat " " (range_to_string r1)))))))

val ckt_to_string: ckt -> string
let ckt_to_string l =
  List.fold_left (fun s celt -> strcat s (strcat "\n" (celt_to_string celt))) "" l

type booleancelt =
  | AND: int -> int -> int -> booleancelt
  | XOR: int -> int -> int -> booleancelt
  | INPUT: prin -> wrange -> booleancelt
  | OUTPUT: prin -> wrange -> booleancelt

type bckt = list booleancelt

val booleancelt_to_string: booleancelt -> string
let booleancelt_to_string = function
  | AND i1 i2 i3 ->
    strcat "AND " (strcat (string_of_int i1) (strcat " " (strcat (string_of_int i2) (strcat " " (string_of_int i3)))))
  | XOR i1 i2 i3 ->
    strcat "XOR " (strcat (string_of_int i1) (strcat " " (strcat (string_of_int i2) (strcat " " (string_of_int i3)))))
  | INPUT p r ->
    strcat "INPUT " (strcat (Print.prin_to_string p) (strcat " " (range_to_string r)))
  | OUTPUT p r ->
    strcat "OUTPUT " (strcat (Print.prin_to_string p) (strcat " " (range_to_string r)))

val bckt_to_string: bckt -> string
let bckt_to_string l =
  fold_left (fun s belt -> strcat s (strcat "\n" (booleancelt_to_string belt))) "" l

val flatten_range: wrange -> list int
let flatten_range r =
  let rec helper k l =
    if k = fst r then k::l
    else helper (k - 1) (k::l)
  in
  helper (snd r) []

(* i <- j *)
val copy: int -> int -> booleancelt
let copy i j = XOR i j 0

val nat_to_bin: nat -> list int
let nat_to_bin n =
  let rec helper n =
    if n / 2 = 0 then
      [n]
    else
      (n % 2)::(helper (n / 2))
  in
  let rec pad l =
    if List.length l > natsize then
      failwith "natsize not sufficient"
    else if List.length l = natsize then
      l
    else
      pad (l @ [0])
  in
  pad (helper n)

val celt_to_booleancelt: celt -> bckt
let celt_to_booleancelt celt = match celt with
  | Input p r -> [ INPUT p r ]
  | Output p r -> [ OUTPUT p r ]
  | Mux r3 r1 r2 r4 -> 
    let l1 = flatten_range r1 in
    let l2 = flatten_range r2 in
    let l3 = flatten_range r3 in

    let f (c, out) b1 b2 =
      let t1 = 1 in
      let (t2, _) = alloc_wires 1 in
      let g1 = XOR t2 t1 (fst r4) in
      let (t3, _) = alloc_wires 1 in
      let g2 = XOR t3 b1 b2 in
      let (t4, _) = alloc_wires 1 in
      let g3 = AND t4 t2 t3 in
      let (t5, _) = alloc_wires 1 in
      let g4 = XOR t5 t4 b2 in
      g4::g3::g2::g1::c, t5::out
    in

    let (rbckt, rout) = fold_left2 f ([], []) l1 l2 in
    let (bckt, out) = rev_append rbckt [], rev_append rout [] in
      
    let f ckt b1 b2 = (copy b1 b2)::ckt in
    rev_append (fold_left2 f bckt l3 out) []
  | BinOp op r3 r1 r2 ->
    if op = Gt then
      let l1 = flatten_range r1 in
      let l2 = flatten_range r2 in

      let f (ckt, c) b1 b2 =
	let (t1, _) = alloc_wires 1 in
	let g1 = XOR t1 b1 c in
	let (t2, _) = alloc_wires 1 in
	let g2 = XOR t2 b2 c in
	let (t3, _) = alloc_wires 1 in
	let g3 = AND t3 t1 t2 in
	let (c1, _) = alloc_wires 1 in
	let g4 = XOR c1 t3 b1 in
	g4::g3::g2::g1::ckt, c1
      in
      
      let (rbckt, c) = fold_left2 f ([], 0) l1 l2 in
      rev_append ((copy (fst r3) c)::rbckt) []
    else if op = Eq then
      let l1 = flatten_range r1 in
      let l2 = flatten_range r2 in

      let f (ckt, c) b1 b2 =
	let (t1, _) = alloc_wires 1 in
	let g1 = XOR t1 b1 b2 in
	let (t2, _) = alloc_wires 1 in
	let g2 = copy t2 1 in
	let (t3, _) = alloc_wires 1 in
	let g3 = XOR t3 t1 t2 in
	let (c1, _) = alloc_wires 1 in
	let g4 = AND c1 t3 c in
	g4::g3::g2::g1::ckt, c1
      in
      let (rbckt, c) = fold_left2 f ([], 1) l1 l2 in
      rev_append ((copy (fst r3) c)::rbckt) []
    else []
  | Const_nat r n ->
    let l1 = flatten_range r in
    let l2 = nat_to_bin n in
    rev_append (fold_left2 (fun c i1 i2 -> (copy i1 i2)::c) [] l1 l2) []
  | Const_bool r b ->
    let l1 = flatten_range r in
    let l2 = if b then [1] else [0] in
    rev_append (fold_left2 (fun c i1 i2 -> (copy i1 i2)::c) [] l1 l2) []

val assign_out: eprins -> wrange -> ckt
let rec assign_out eps r =
  if eps = empty then []
  else
    let Some p = choose eps in
    let eps' = remove p eps in
    (Output p r)::(assign_out eps' r)

val prin_to_id: prin -> nat
let prin_to_id p = match p with
  | Alice -> 0
  | Bob -> 1
  | Charlie -> 2
  | Dave -> 3
  | Evelyn -> 4
  | Fred -> 5

val int_cmp: int -> int -> Tot bool
let int_cmp n1 n2 = n1 <= n2

type aux_info = ordmap int (list int) int_cmp

val calc_auxinf: bckt -> aux_info
let calc_auxinf bckt =
  List.fold_left (fun (m:aux_info) belt ->
    match belt with
      | AND x y z
      | XOR x y z ->
	let ym =
	  if contains y m then Some.v (select y m)
	  else []
	in
	let zm =
	  if contains z m then Some.v (select z m)
	  else []
	in
	update y (x::ym) (update z (x::zm) m)
      | _ -> m
  ) (OrdMap.empty #int #(list int) #int_cmp) bckt

val dump_gmw: prins -> bckt -> fd_write -> unit
let dump_gmw prs bckt fd =
  let ps s = write_string fd s in
  let psi i = write_string fd (string_of_int i) in

  let inps = filter (fun bcelt -> is_INPUT bcelt) bckt in
  let outs = filter (fun bcelt -> is_OUTPUT bcelt) bckt in
  let ands = filter (fun bcelt -> is_AND bcelt) bckt in
  let xors = filter (fun bcelt -> is_XOR bcelt) bckt in
  let aux = calc_auxinf bckt in

  let last_inp_id = List.fold_left (fun id belt ->
    match belt with
      | INPUT _ (_, j) -> if id < j then j else id
      | _ -> failwith "Ah, wish it was refined to not have this case"
  ) 0 inps in

  ps "n "; psi (OrdSet.size prs); ps "\n"; //num of parties
  ps "d "; psi (!ctr + 1); ps " "; psi (last_inp_id + 1); ps " "; psi (List.length xors); ps "\n";

  List.iter (fun belt ->
    match belt with
      | INPUT p (i, j) ->
	ps "i "; psi (prin_to_id p); ps " "; psi i; ps " "; psi j; ps "\n"
      | _ -> failwith "Ah, wish it was refined to not have this case"
  ) inps;
  List.iter (fun belt ->
    match belt with
      | OUTPUT p (i, j) ->
	ps "o "; psi (prin_to_id p); ps " "; psi i; ps " "; psi j; ps "\n"
      | _ -> failwith "Ah, wish it was refined to not have this case"
  ) outs;
  // this is mysterious, why ?
  List.iter (fun belt ->
    match belt with
      | INPUT p _ ->
	ps "v "; psi (prin_to_id p); ps " 1"; ps "\n"
      | _ -> failwith "Ah, wish it was refined to not have this case"
  ) inps;

  ps "g 0 0 -1 -1 ";
  let l0 = if contains 0 aux then Some.v (select 0 aux) else [] in
  psi (List.length l0);
  List.iter (fun i -> ps " "; psi i) l0; ps "\n";

  ps "g 1 0 -1 -1 ";
  let l1 = if contains 1 aux then Some.v (select 1 aux) else [] in
  psi (List.length l1);
  List.iter (fun i -> ps " "; psi i) l1; ps "\n";

  List.iter (fun belt ->
    match belt with
      | INPUT _ r ->
	let l = flatten_range r in
	List.iter (fun i ->
	  ps "g "; psi i; ps " 0 -1 -1 ";
	  let l' = if contains i aux then Some.v (select i aux) else [] in
	  psi (List.length l');
	  List.iter (fun i' -> ps " "; psi i') l'; ps "\n"
	) l
      | AND x y z ->
	ps "g "; psi x; ps " 1 "; psi y; ps " "; psi z; ps " ";
	let l = if contains x aux then Some.v (select x aux) else [] in
	psi (List.length l);
	List.iter (fun i -> ps " "; psi i) l;
	ps "\n"
      | XOR x y z ->
	ps "g "; psi x; ps " 2 "; psi y; ps " "; psi z; ps " ";
	let l = if contains x aux then Some.v (select x aux) else [] in
	psi (List.length l);
	List.iter (fun i -> ps " "; psi i) l;
	ps "\n"
      | _ -> ()
  ) bckt;
  ()

val dump_val: #meta:v_meta -> v:value meta -> fd_write -> unit
let rec dump_val #meta v fd = match v with
  | V_box _ v'           -> dump_val v' fd
  | V_opaque 'a _ _ _ _ _ -> 
    let n = Ffibridge.nat_of_v_opaque v in
    let l = nat_to_bin n in
    List.iter (fun b -> write_string fd (string_of_int b); write_string fd " ") l
  | V_bool b             -> if b then write_string fd "1 " else write_string fd "0 "
  | _ -> failwith "Dumping of this value is not supported"

val dump_inps: varset -> env -> fd_write -> unit
let rec dump_inps vars en fd =
  if vars = empty then ()
  else
    //TODO: check that value type is nat or bool?
    let Some v = choose vars in
    let vars' = remove v vars in
    let Var _ t = v in
    if supported_input_type t then
      let dv_opt = en v in
      if is_None dv_opt then failwith "Input is not mapped in the env"
      else
	let Some (D_v _ v) = dv_opt in
	dump_val v fd;
	dump_inps vars' en fd
    else failwith "Dumpinps input type not supported"

(* GMW lib needs total input size for the party *)
val get_inp_size: prin -> bckt -> int
let rec get_inp_size p = function
  | [] -> 0
  | belt::tl ->
    let n =
      match belt with
	| INPUT p' r -> if p' = p then (snd r - fst r + 1) else 0
	| _ -> 0
    in
    if n = 0 then get_inp_size p tl else n

val ckt_fname: prin -> string
let ckt_fname p =
  let s = Print.prin_to_string p in
  let s' = FStar.String.substring s 0 1 in
  strcat "circuit_" (strcat s' ".txt")

val inp_fname: prin -> string
let inp_fname p =
  let s = Print.prin_to_string p in
  let s' = FStar.String.substring s 0 1 in
  strcat "input_" (strcat s' ".txt")

val out_fname: prin -> string
let out_fname p =
  let s = Print.prin_to_string p in
  let s' = FStar.String.substring s 0 1 in
  strcat "output_" (strcat s' ".txt")

val conf_fname: prin -> string
let conf_fname p =
  let s = Print.prin_to_string p in
  let s' = FStar.String.substring s 0 1 in
  strcat "config" (strcat s' ".txt")

val dump_conf: prin -> int -> fd_write -> unit
let dump_conf p n fd =
  let ps = write_string fd in
  ps "load-circuit "; ps (ckt_fname p); ps "\n";
  ps "input "; ps (inp_fname p); ps "\n";
  ps "output "; ps (out_fname p); ps "\n";
  ps "shinput foo.txt\n";  // TODO: Fix GMW lib so that these args are not mandatory
  ps "shoutput bar.txt\n";
  ps "num_input "; ps (string_of_int n); ps "\n"

val prin_to_gmwport: prin -> int
let prin_to_gmwport p = match p with
  | Alice -> 9000
  | Bob -> 9001
  | Charlie -> 9002
  | _ -> failwith "Sorry, I don't know you!"

val supported_output_type: typ -> Tot bool
let supported_output_type t = match t with
  | T_bool     -> true
  | T_cons _ _ -> is_nat t
  | _          -> false

let const_meta (u:unit) = Meta empty Can_b empty Can_w

val parse_output: list string -> typ -> dvalue
let parse_output l t = match t with
  | T_bool     ->
    if l = ["0"] then D_v (const_meta ()) (V_bool false)
    else if l = ["1"] then D_v (const_meta ()) (V_bool true)
    else failwith "Unexpected GMW output for boolean type"

  | T_cons _ _ ->
    if is_nat t then
      let n = Runtime.list_to_int l in
      D_v (const_meta ()) (V_opaque n (const_meta ()) slice_const compose_const slice_const_sps)
    else failwith "Unsupported output cons (should have been checked earlier)"

  | _ -> failwith "Unsupported output type (should have been checked earlier)"

val typ_to_string: typ -> string
val typ_l_to_string: list typ -> string
let rec typ_to_string t = match t with
  | T_prin -> "T_prin"
  | T_eprins -> "T_eprins"
  | T_unit -> "T_unit"
  | T_bool -> "T_bool"
  | T_cons s args -> strcat "T_cons " (strcat s (strcat " [" (strcat (typ_l_to_string args) " ]")))
  | T_box t' -> strcat "T_box " (typ_to_string t')
  | T_wire t' -> strcat "T_wire " (typ_to_string t')
  | T_fun t1 t2 -> strcat "T_fun " (strcat (typ_to_string t1) (strcat " " (typ_to_string t2)))
  | T_unknown -> "T_unknown"

and typ_l_to_string l = fold_left (fun s t -> strcat s (strcat "; " (typ_to_string t))) "" l

val rungmw: prin -> prins -> env -> cktenv -> exp -> dvalue
let rungmw p ps en cen e =
  init_ctr ();

  let m = assign_inps ps (fvs e) en in
  let cs_inp, cen = alloc_input_wires ps m [] cen in
  let cs_e, r, t = exp_to_ckt cen e in
  let cs_out = assign_out ps r in

  let _ =
    if supported_output_type t then ()
    else
      failwith (strcat "Output type not supported: " (typ_to_string t))
  in

  let final_ckt = cs_inp @ cs_e @ cs_out in
  print_string (ckt_to_string final_ckt);
  print_string "\n";
  let bckt = flatten (map (fun celt -> celt_to_booleancelt celt) final_ckt) in
  print_string (bckt_to_string bckt);
  print_string "\n";

  let conf_fname = conf_fname p in
  let ckt_fname = ckt_fname p in
  let inp_fname = inp_fname p in

  print_string "Dumping GMW:\n";
  let fd = open_write_file ckt_fname in
  dump_gmw ps bckt fd;
  close_write_file fd;

  print_string "Dumping inputs:\n";
  let fd = open_write_file inp_fname in
  let _ =
    if contains p m then dump_inps (Some.v (select p m)) en fd
    else ()
  in
  close_write_file fd;

  print_string "Dumping config:\n";
  let fd = open_write_file conf_fname in
  dump_conf p (get_inp_size p bckt) fd;
  close_write_file fd;

  let port = prin_to_gmwport p in
  let out_l = Runtime.rungmw conf_fname (out_fname p) port in
  parse_output out_l t
