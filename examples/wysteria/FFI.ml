open AST

open FStar_OrdSet

exception FFI_error of string

let meta = Meta (FStar_OrdSet.empty (), Can_b, FStar_OrdSet.empty (), Can_w)

let get_nat ((D_v (_, v)):dvalue) :int = match v with
  | V_const c -> begin
    match c with
      | C_nat n -> n
      | _ -> raise (FFI_error "Constant not a nat")
    end

  | _ -> raise (FFI_error "Value not a constant(nat)")

let get_bool ((D_v (_, v)):dvalue) :bool = match v with
  | V_const c -> begin
    match c with
      | C_bool b -> b
      | _ -> raise (FFI_error "Constant not a bool")
    end

  | _ -> raise (FFI_error "Value not a constant(bool)")

let get_ps ((D_v (_, v)):dvalue) :prins = match v with
  | V_const c -> begin
    match c with
      | C_prins ps -> ps
      | _ -> raise (FFI_error "Constant not a prins")
    end

  | _ -> raise (FFI_error "Value not a constant(ps)")

let get_p ((D_v (_, v)):dvalue) :prin = match v with
  | V_const c -> begin
    match c with
      | C_prin p -> p
      | _ -> raise (FFI_error "Constant not a prin")
    end

  | _ -> raise (FFI_error "Value not a constant(p)")

let get_two_values (l:dvalue list) :(dvalue * dvalue) = List.hd l, List.hd (List.tl l)

let print_ps (ps:prins) :string =
  FStar_OrdSet.fold () (fun p s -> s ^ (string_of_int p) ^ "; ") ps ""

let rec print_value (v:unit value) :string = match v with
  | V_const c -> begin
    match c with
      | C_nat n -> "nat: " ^ (string_of_int n)
      | C_bool b -> "bool: " ^ (string_of_bool b)
      | C_prin p -> "prin: " ^ (string_of_int p)
      | C_prins ps -> "prins constant: " ^ print_ps ps
      | C_unit -> "unit"
    end

  | V_box (_, ps, v) -> "boxed value: " ^ print_ps ps ^ " " ^ print_value v

  | _ -> raise (FFI_error "Value print not implemented")

let exec_ffi (s:string) (l:dvalue list) =
  let l = List.rev l in
  match s with
    | "op_Addition" ->
      let (v1, v2) = get_two_values l in
      let (n1, n2) = get_nat v1, get_nat v2 in
      D_v (meta, V_const (C_nat (n1 + n2)))

    | "op_Subtraction" ->
      let (v1, v2) = get_two_values l in
      let (n1, n2) = get_nat v1, get_nat v2 in
      D_v (meta, V_const (C_nat (n1 - n2)))

    | "op_Multiply" ->
      let (v1, v2) = get_two_values l in
      let (n1, n2) = get_nat v1, get_nat v2 in
      D_v (meta, V_const (C_nat (n1 * n2)))

    | "op_Division" ->
      let (v1, v2) = get_two_values l in
      let (n1, n2) = get_nat v1, get_nat v2 in
      D_v (meta, V_const (C_nat (n1 / n2)))

    | "op_Equality" ->
      let (v1, v2) = get_two_values l in
      D_v (meta, V_const (C_bool (v1 = v2)))

    | "op_disEquality" ->
      let (v1, v2) = get_two_values l in
      D_v (meta, V_const (C_bool (not (v1 = v2))))

    | "op_AmpAmp" ->
      let (v1, v2) = get_two_values l in
      let (n1, n2) = get_bool v1, get_bool v2 in
      D_v (meta, V_const (C_bool (n1 && n2)))

    | "op_BarBar" ->
      let (v1, v2) = get_two_values l in
      let (n1, n2) = get_bool v1, get_bool v2 in
      D_v (meta, V_const (C_bool (n1 || n2)))

    | "op_LessThanOrEqual" ->
      let (v1, v2) = get_two_values l in
      let (n1, n2) = get_nat v1, get_nat v2 in
      D_v (meta, V_const (C_bool (n1 <= n2)))

    | "op_GreaterThanOrEqual" ->
      let (v1, v2) = get_two_values l in
      let (n1, n2) = get_nat v1, get_nat v2 in
      D_v (meta, V_const (C_bool (n1 >= n2)))

    | "op_LessThan" ->
      let (v1, v2) = get_two_values l in
      let (n1, n2) = get_nat v1, get_nat v2 in
      D_v (meta, V_const (C_bool (n1 < n2)))

    | "op_GreaterThan" ->
      let (v1, v2) = get_two_values l in
      let (n1, n2) = get_nat v1, get_nat v2 in
      D_v (meta, V_const (C_bool (n1 > n2)))

    | "op_Modulus" ->
      let (v1, v2) = get_two_values l in
      let (n1, n2) = get_nat v1, get_nat v2 in
      D_v (meta, V_const (C_nat (n1 mod n2)))

    | "mem" ->
      let (v1, v2) = get_two_values l in
      let p, ps = get_p v1, get_ps v2 in
      D_v (meta, V_const (C_bool (FStar_OrdSet.mem () p ps)))

    | "singleton" ->
      let v = List.hd l in
      let p = get_p v in
      D_v (meta, V_const (C_prins (FStar_OrdSet.singleton () p)))

    | "subset" ->
      let (v1, v2) = get_two_values l in
      let ps1, ps2 = get_ps v1, get_ps v2 in
      D_v (meta, V_const (C_bool (FStar_OrdSet.subset () ps1 ps2)))

    | "union" ->
      let (v1, v2) = get_two_values l in
      let ps1, ps2 = get_ps v1, get_ps v2 in
      D_v (meta, V_const (C_prins (FStar_OrdSet.union () ps1 ps2)))

    | "size" ->
      let v = List.hd l in
      let ps = get_ps v in
      D_v (meta, V_const (C_nat (FStar_OrdSet.size () ps)))

    | "choose" ->
      let v = List.hd l in
      let ps = get_ps v in
      let p_opt = FStar_OrdSet.choose () ps in
      let p =
        match p_opt with
          | None -> raise (FFI_error ("choose FFI returns None breaking typing"))
          | Some p -> p
      in
      D_v (meta, V_const (C_prin p))

    | "remove" ->
      let (v1, v2) = get_two_values l in
      let p, ps = get_p v1, get_ps v2 in
      let ps' = FStar_OrdSet.remove () p ps in
      D_v (meta, V_const (C_prins ps'))

    | "read" ->
      let n = read_int () in
      D_v (meta, V_const (C_nat n))

    | "wprint" ->
      let (D_v (_, v)) = List.hd l in
      print_string (print_value v);
      D_v (meta, V_const C_unit)

    | _ -> raise (FFI_error ("FFI " ^ s ^ " not implemented"))
