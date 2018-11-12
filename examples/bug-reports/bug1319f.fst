(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
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

[@(expect_failure [54])]
let operandReg64 : operand int (regtyp 0) = {
  eval_operand  = (fun op regs -> regs op ) // types don't really match here
}
