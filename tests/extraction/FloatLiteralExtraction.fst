module FloatLiteralExtraction

let f64 : FStar.Float64.t =
  FStar.Float64.of_literal "-1.25e+3"

let f32 : FStar.Float32.t =
  FStar.Float32.of_literal ".5"
