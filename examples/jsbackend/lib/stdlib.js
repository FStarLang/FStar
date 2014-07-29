JS = {};

JS.alert = function(x){
 window.alert(x);
}

JS.utest = function(msg) {
 return function(x){
  return function(y) {
   if(x+""==y+"")
    document.write("Assertion "+msg+" OK.<br />");
   else
    throw document.writeln("<b>Assertion "+msg+" failed!</b><br />");
}}}

JS.console = {}

JS._tS = function(){return this.t+":"+this.v}

JS.console.log = function(x){
 console.log(x);
}

JS.console.dir = function(x){
 console.dir(x);
}

String.split = function(s){
 return function(x){
  console.log(s);
  var r = List.fold_left(function(u){return function(v){return u+v}})("")(s);
  return x.split(new RegExp("["+r+"]")).reduceRight(function(x,y){
   return {"t":"Prims.Cons", v:[y, x], "toString": JS._tS}
  }, {"t":"Prims.Nil", "v":[], "toString":JS._tS});
}}

String.strcat = function(x){
 return function(y){
  return x+y;
}}

String.concat = function(s){
 return function(l){
  return List.fold_left(function(u){return function(v){return u+s+v}})("")(l).substr(1);
}}

String.compare = function(x){
 return function(y){
  return x==y?0:(x<y?-1:1);
}}

String.length = function(x){
 return x.length;
}

String.substring = function(x){
 return function(f){
  return function(t){
   return x.substr(f,t);
}}}

Microsoft = {}
Microsoft.FStar = {};

List = {};

  List.hd = (function (x_635)
  {
   return (function ($v)
   {
    if($v.t == "Prims.Cons")
     with({
     "hd":$v.v[0],
     "tl":$v.v[1]
     })
      return hd;


    return (function (x_781)
    {
     return (function ()
     {
      throw x_781;
      })();
     })("head of empty list");
    })(x_635);
   });
  List.tail = (function (x_636)
  {
   return (function ($v)
   {
    if($v.t == "Prims.Cons")
     with({
     "hd":$v.v[0],
     "tl":$v.v[1]
     })
      return tl;


    return (function (x_782)
    {
     return (function ()
     {
      throw x_782;
      })();
     })("tail of empty list");
    })(x_636);
   });
  List.mem = (function mem(x)
  {
   return (function (x_637)
   {
    return (function ($v)
    {
     if($v.t == "Prims.Nil")
      return false;

     if($v.t == "Prims.Cons")
      with({
      "hd":$v.v[0],
      "tl":$v.v[1]
      })
       return (function (x_784)
       {
        return (function (x_783)
        {
         return x_783 + "" == x_784;
         });
        })(hd)(x) ? true : List.mem(x)(tl);


     throw "Incomplete pattern";
     })(x_637);
    });
   });
  List.map = (function map(f)
  {
   return (function (x)
   {
    return (function ($v)
    {
     if($v.t == "Prims.Nil")
      return $C("Prims.Nil",[]);

     if($v.t == "Prims.Cons")
      with({
      "a":$v.v[0],
      "tl":$v.v[1]
      })
       return (function (x_786)
       {
        return (function (x_785)
        {
         return $C("Prims.Cons",[x_785,x_786]);
         });
        })(f(a))(List.map(f)(tl));


     throw "Incomplete pattern";
     })(x);
    });
   });
  List.fold_left = (function fold_left(f)
  {
   return (function (x)
   {
    return (function (y)
    {
     return (function ($v)
     {
      if($v.t == "Prims.Nil")
       return x;

      if($v.t == "Prims.Cons")
       with({
       "hd":$v.v[0],
       "tl":$v.v[1]
       })
        return List.fold_left(f)(f(x)(hd))(tl);


      throw "Incomplete pattern";
      })(y);
     });
    });
   });
  List.fold_right = (function fold_right(f)
  {
   return (function (l)
   {
    return (function (x)
    {
     return (function ($v)
     {
      if($v.t == "Prims.Nil")
       return x;

      if($v.t == "Prims.Cons")
       with({
       "hd":$v.v[0],
       "tl":$v.v[1]
       })
        return List.fold_right(f)(tl)(f(hd)(x));


      throw "Incomplete pattern";
      })(l);
     });
    });
   });
  List.iter = (function iter(f)
  {
   return (function (x)
   {
    return (function ($v)
    {
     if($v.t == "Prims.Nil")
      return undefined;

     if($v.t == "Prims.Cons")
      with({
      "a":$v.v[0],
      "tl":$v.v[1]
      })
       return (function ()
       {
        var x_689 = f(a);
        return (function ($v)
        {
         return List.iter(f)(tl);
         })(x_689);
        })();


     throw "Incomplete pattern";
     })(x);
    });
   });
  List.assoc = (function assoc(a)
  {
   return (function (x)
   {
    return (function ($v)
    {
     if($v.t == "Prims.Nil")
      return $C("Prims.None",[]);

     if($v.t == "Prims.Cons" && $v.v[0].t == "Prims.MkTuple2")
      with({
      "ap":$v.v[0].v[0],
      "b":$v.v[0].v[1],
      "tl":$v.v[1]
      })
       return (function (x_788)
       {
        return (function (x_787)
        {
         return x_787 + "" == x_788;
         });
        })(a)(ap) ? (function (x_789)
       {
        return $C("Prims.Some",[x_789]);
        })(b) : List.assoc(a)(tl);


     throw "Incomplete pattern";
     })(x);
    });
   });
  List.append = (function append(x)
  {
   return (function (y)
   {
    return (function ($v)
    {
     if($v.t == "Prims.Nil")
      return y;

     if($v.t == "Prims.Cons")
      with({
      "a":$v.v[0],
      "tl":$v.v[1]
      })
       return (function (x_791)
       {
        return (function (x_790)
        {
         return $C("Prims.Cons",[x_790,x_791]);
         });
        })(a)(List.append(tl)(y));


     throw "Incomplete pattern";
     })(x);
    });
   });
  List.concatMap = (function concatMap(f)
  {
   return (function (x_638)
   {
    return (function ($v)
    {
     if($v.t == "Prims.Nil")
      return $C("Prims.Nil",[]);

     if($v.t == "Prims.Cons")
      with({
      "a":$v.v[0],
      "tl":$v.v[1]
      })
       return (function ()
       {
        var fa = f(a);
        return (function ()
        {
         var ftl = List.concatMap(f)(tl);
         return List.append(fa)(ftl);
         })();
        })();


     throw "Incomplete pattern";
     })(x_638);
    });
   });

