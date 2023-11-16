module PulseLambdas
open Pulse.Lib.Pervasives

let stt_trivial a = stt a emp (fun _ -> emp)

[@@expect_failure]
```pulse
fn test_trivial_function (x:int)
: stt_trivial int
= { //should allow nullary "lambdas"
    (x + 1)
  }
```

let swap_fun = #a:Type0 -> x:ref a -> y:ref a -> #vx:erased a -> #vy:erased a -> stt unit
    (requires pts_to x vx ** pts_to y vy)
    (ensures fun _ -> pts_to x vy ** pts_to y vx)


```pulse
fn s1 (_:unit) // should allow nullary "lambdas"
  : swap_fun 
  = (#a:Type0) (x y #_vx #_vy:_)
    {
      let vx = !x;
      let vy = !y;
      x := vy;
      y := vx;
    }
```

let ss = s1

[@@expect_failure]
```pulse
fn s2 (_:unit)
  : swap_fun 
  = (#a:Type0) (x y:_) //make it so that implicit binders in the type can be left out
    {
      let vx = !x;
      let vy = !y;
      x := vy;
      y := vx;
    }
```


// [@@expect_failure]
// ```pulse
// fn test_inner_lambda (#a:Type0)
//                      (x y:ref int)
// requires pts_to x 'vx ** pts_to y 'vy
// ensures  pts_to x 'vy ** pts_to y 'vx
// {
//   ghost
//   fn write_helper (#a:Type) (x:ref a) (n:a)
//     requires pts_to x 'vx
//     ensures  pts_to x n
//   {
//     x := n;
//   };
//   let vx = !x;
//   let vy = !y;
//   write_helper x vy;
//   write_helper y vy;
// } 
// ```
