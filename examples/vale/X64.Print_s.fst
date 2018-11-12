module X64.Print_s

// Trusted code for producing assembly code

open X64.Machine_s
open X64.Semantics_s
open FStar.IO

noeq type printer = {
  reg_prefix : unit -> string;
  mem_prefix : string -> string;
  maddr      : string -> option(string * string) -> string -> string;
  const      : int -> string;
  ins_name   : string -> list operand -> string;
  op_order   : string -> string -> string * string;
  align      : unit -> string;
  header     : unit -> string;
  footer     : unit -> string;
  proc_name  : string -> string;
  ret        : string -> string;
}

let print_reg (r:reg) (p:printer) =
  p.reg_prefix() ^
  (match r with
  | Rax -> "rax"
  | Rbx -> "rbx"
  | Rcx -> "rcx"
  | Rdx -> "rdx"
  | Rsi -> "rsi"
  | Rdi -> "rdi"
  | Rbp -> "rbp"
  | Rsp -> "rsp"
  | R8  -> "r8"
  | R9  -> "r9"
  | R10 -> "r10"
  | R11 -> "r11"
  | R12 -> "r12"
  | R13 -> "r13"
  | R14 -> "r14"
  | R15 -> "r15"
  )

let print_small_reg (r:reg) (p:printer) =
  p.reg_prefix() ^
  (match r with
  | Rax -> "al"
  | Rbx -> "bl"
  | Rcx -> "cl"
  | Rdx -> "dl"
  | _ -> " !!! INVALID small operand !!!  Expected al, bl, cl, or dl."
  )

let print_maddr (m:maddr) (ptr_type:string) (p:printer) =
  p.mem_prefix ptr_type ^
  (match m with
     | MConst n -> p.const n
     | MReg r offset -> p.maddr (print_reg r p) None (string_of_int offset)
     | MIndex base scale index offset ->
          p.maddr (print_reg base p)
          (Some (string_of_int scale, print_reg index p))
          (string_of_int offset)
   )
open FStar.UInt64

let print_operand (o:operand) (p:printer) =
  match o with
  | OConst n ->
      if 0 <= n && n < nat64_max then p.const n
      else "!!! INVALID constant: " ^ string_of_int n ^ " !!!"
  | OReg r -> print_reg r p
  | OMem m -> print_maddr m "qword" p

let print_small_operand (o:operand) (p:printer) =
  match o with
  | OConst n ->
      if n < 64 then p.const n
      else "!!! INVALID constant: " ^ string_of_int n ^ " !!!!"
  | OReg r -> print_small_reg r p
  | _ -> "!!! INVALID small operand !!! Expected al, bl, cl, or dl."

assume val print_any: 'a -> string

let print_shift_operand (o:operand) (p:printer) =
  match o with
  | OConst n ->
      if n < 64 then p.const n
      else "!!! INVALID shift operand: " ^ string_of_int n ^ " is too large !!!"
  | OReg Rcx -> print_small_reg (OReg?.r o) p
  | _ -> "!!! INVALID shift operand !!! Expected constant or cl."

let cmp_not(o:ocmp) : ocmp =
  match o with
  | OEq o1 o2 -> ONe o1 o2
  | ONe o1 o2 -> OEq o1 o2
  | OLe o1 o2 -> OGt o1 o2
  | OGe o1 o2 -> OLt o1 o2
  | OLt o1 o2 -> OGe o1 o2
  | OGt o1 o2 -> OLe o1 o2

// Sanity check
let _ = assert (forall o . o == cmp_not (cmp_not o))

let print_ins (ins:ins) (p:printer) =
  let print_pair (dst:operand) (src:operand) (print_dst:operand->printer->string) (print_src:operand->printer-> string) =
    let first, second = p.op_order (print_dst dst p) (print_src src p) in
      first ^ ", " ^ second ^ "\n"
  in
  let print_ops (dst:operand) (src:operand) =
    print_pair dst src print_operand print_operand
  in
  let print_shift (dst:operand) (amount:operand) =
    print_pair dst amount print_operand print_shift_operand
  in
  match ins with
  | Mov64 dst src -> p.ins_name "  mov" [dst; src] ^ print_ops dst src
  | Add64 dst src -> p.ins_name "  add" [dst; src] ^ print_ops dst src
  | AddLea64 dst src1 src2 -> let name = p.ins_name "  lea" [dst; src1; src2] in
                             if OReg? src1 && OConst? src2 then
                               name ^ print_maddr (MReg (OReg?.r src1) (OConst?.n src2)) "qword" p
                             else if OReg? src1 && OReg? src2 then
                               name ^ print_maddr (MIndex (OReg?.r src1) 1 (OReg?.r src2) 0) "qword" p
                             else
                               "!!! INVALID AddLea64 operands: " ^ print_any src1 ^ ", " ^ print_any src2 ^ "!!!"
  | AddCarry64 dst src -> p.ins_name "  adc" [dst; src] ^ print_ops dst src
  | Sub64 dst src -> p.ins_name "  sub" [dst; src] ^ print_ops dst src
  | Mul64 src -> p.ins_name "  mul" [src] ^ (print_operand src p)
  | IMul64 dst src -> p.ins_name "  imul" [dst; src] ^ print_ops dst src
  | Xor64 dst src -> p.ins_name "  xor" [dst; src] ^ print_ops dst src
  | And64 dst src -> p.ins_name "  and" [dst; src] ^ print_ops dst src
  | Shr64 dst amt -> p.ins_name "  shr" [dst; amt] ^ print_shift dst amt
  | Shl64 dst amt -> p.ins_name "  shl" [dst; amt] ^ print_shift dst amt

let print_cmp (c:ocmp) (counter:int) (p:printer) : string =
  let print_ops (o1:operand) (o2:operand) : string =
    let first, second = p.op_order (print_operand o1 p) (print_operand o2 p) in
    "  cmp " ^ first ^ ", " ^ second ^ "\n"
  in
  match c with
  | OEq o1 o2 -> print_ops o1 o2 ^ "  je " ^ "L" ^ string_of_int counter ^ "\n"
  | ONe o1 o2 -> print_ops o1 o2 ^ "  jne "^ "L" ^ string_of_int counter ^ "\n"
  | OLe o1 o2 -> print_ops o1 o2 ^ "  jbe "^ "L" ^ string_of_int counter ^ "\n"
  | OGe o1 o2 -> print_ops o1 o2 ^ "  jae "^ "L" ^ string_of_int counter ^ "\n"
  | OLt o1 o2 -> print_ops o1 o2 ^ "  jb " ^ "L" ^ string_of_int counter ^ "\n"
  | OGt o1 o2 -> print_ops o1 o2 ^ "  ja " ^ "L" ^ string_of_int counter ^ "\n"

let rec print_block (b:codes) (n:int) (p:printer) : string * int =
  match b with
  | Nil -> "", n
  | head :: tail ->
    let head_str, n' = print_code head n p in
    let rest, n'' = print_block tail n' p in
    head_str ^ rest, n''
and print_code (c:code) (n:int) (p:printer) : string * int =
  match c with
  | Ins ins -> print_ins ins p, n
  | Block b -> print_block b n p
  | IfElse cond true_code false_code ->
    let n1 = n in
    let n2 = n + 1 in
    let cmp = print_cmp (cmp_not cond) n1 p in
    let true_str, n' = print_code true_code (n + 2) p in
    let jmp = "  jmp L" ^ string_of_int n2 ^ "\n" in
    let label1 = "L" ^ string_of_int n1 ^ ":\n" in
    let false_str, n' = print_code false_code n' p in
    let label2 = "L" ^ string_of_int n2 ^ ":\n" in
    cmp ^ true_str ^ jmp ^ label1 ^ false_str ^ label2, n'
  | While cond body ->
    let n1 = n in
    let n2 = n + 1 in
    let jmp = "  jmp L" ^ string_of_int n2 ^ "\n" in
    let label1 = p.align() ^ " 16\nL" ^ string_of_int n1 ^ "\n" in
    let body_str, n' = print_code body (n + 2) p in
    let label2 = p.align() ^ " 16\nL" ^ string_of_int n2 ^ "\n" in
    let cmp = print_cmp cond n1 p in
    jmp ^ label1 ^ body_str ^ label2 ^ cmp, n'

let print_header (p:printer) =
  print_string (p.header())

let print_proc (name:string) (code:code) (label:int) (p:printer) =
  let proc = p.proc_name name in
  let code_str, _ = print_code code label p in
  let ret = p.ret name in
  print_string (proc ^ code_str ^ ret)

let print_footer (p:printer) =
  print_string (p.footer())


(* Concrete printers for MASM and GCC syntax *)
let masm : printer =
  let reg_prefix unit = "" in
  let mem_prefix (ptr_type:string) = ptr_type ^ " ptr " in
  let maddr (base:string) (adj:option(string * string)) (offset:string) =
    match adj with
    | None -> "[" ^ base ^ " + " ^ offset ^ "]"
    | Some (scale, index) -> "[" ^ base ^ " + " ^ scale ^ " * " ^ index ^ " + " ^ offset ^ "]"
  in
  let const (n:int) = string_of_int n in
  let ins_name (name:string) (ops:list operand) : string = name ^ " " in
  let op_order dst src = dst, src in
  let align() = "ALIGN" in
  let header() = ".code\n" in
  let footer() = "end\n" in
  let proc_name (name:string) = "ALIGN 16\n" ^ name ^ " proc\n" in
  let ret (name:string) = "  ret\n" ^ name ^ " endp\n" in
  {
  reg_prefix = reg_prefix;
  mem_prefix = mem_prefix;
  maddr      = maddr;
  const      = const;
  ins_name   = ins_name;
  op_order   = op_order;
  align      = align;
  header     = header;
  footer     = footer;
  proc_name  = proc_name;
  ret        = ret;
  }

let gcc : printer =
  let reg_prefix unit = "%" in
  let mem_prefix (ptr_type:string) = "" in
  let maddr (base:string) (adj:option(string * string)) (offset:string) =
    match adj with
    | None -> offset ^ "(" ^ base ^ ")"
    | Some (scale, index) -> offset ^ " (" ^ base ^ ", " ^ scale ^ ", " ^ index ^ ")"
  in
  let const (n:int) = "$" ^ string_of_int n in
  let rec ins_name (name:string) (ops:list operand) : string =
    match ops with
    | Nil -> name ^ " "
    | OMem _ :: _ -> name ^ "q "
    | _ :: tail -> ins_name name tail
  in
  let op_order dst src = src, dst in
  let align() = ".align" in
  let header() = ".text\n" in
  let footer() = "\n" in
  let proc_name (name:string) = ".global " ^ name ^ "\n" in
  let ret (name:string) = "  ret\n\n" in
  {
  reg_prefix = reg_prefix;
  mem_prefix = mem_prefix;
  maddr      = maddr;
  const      = const;
  ins_name   = ins_name;
  op_order   = op_order;
  align      = align;
  header     = header;
  footer     = footer;
  proc_name  = proc_name;
  ret        = ret;
  }
