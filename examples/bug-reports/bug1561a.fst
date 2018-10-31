module Bug1561a

class validator_cls = {  bidon: nat  }

type validator' (v : validator_cls) (k: nat) : Type0 = | C

let validator [| cls: validator_cls |] k = validator' cls k

let validate_nat [| d : validator_cls |] (p: bool) : Tot (validator 18) = C
