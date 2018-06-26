module Bug1319f

let n_reg_t : pos = 2

type reg_t = n:nat{n < n_reg_t}

let n_regtype (_: reg_t) : n:nat{0 < n} = 16

type regtyp (t:reg_t) = n:nat{n < n_regtype t}

let regval (_:reg_t) : Type0 = int

type regmap = t:reg_t -> regtyp t -> regval t

noeq type operand 'val 'op = {
  eval_operand   : 'op -> regmap -> 'val
}

[@(fail [54])]
let operandReg64 : operand int (regtyp 0) = {
  eval_operand  = (fun op regs -> regs op ) // types don't really match here
}
