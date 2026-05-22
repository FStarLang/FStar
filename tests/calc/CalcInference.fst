module CalcInference

let lem () : (2 == 1 + 1) = ()

let test1 () : (2 == 1 + 1) =
  calc (==) {
    2;
  == { lem () }
    _;
  }

let test2 () : (2 == 1 + 1) =
  calc (==) {
    _;
  == { lem () }
    1 + 1;
  }

let test3 () : (2 == 1 + 1) =
  calc (==) {
    _;
  == { lem () }
    _;
  }
