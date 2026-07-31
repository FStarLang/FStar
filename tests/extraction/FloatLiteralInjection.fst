module FloatLiteralInjection

let bad : FStar.Float64.t =
  FStar.Float64.of_literal "0.0); KRML_HOST_EXIT(0); /*"
