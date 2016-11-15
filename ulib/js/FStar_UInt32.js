/* @flow */

export type uint32 = number;
export type t = uint32;

export let v = (x:uint32): number => x;

export let zero = 0;
export let one = 1;
export let ones = 4294967295;
                                              
export let add = (a:uint32) : ((b:uint32) => uint32) => ((b:uint32) => a + b);
export let add_underspec = (a:uint32) => ((b:uint32) => add(a)(b));
export let add_mod = (a:uint32) => ((b:uint32) => add(a)(b) & 4294967295);

export let sub = (a:uint32) : ((b:uint32) => uint32) => ((b:uint32) => a - b);
export let sub_underspec = (a:uint32) => ((b:uint32) => sub(a)(b));
export let sub_mod = (a:uint32) => ((b:uint32) => sub(a)(b) & 4294967295);

export let mul = (a:uint32) : ((b:uint32) => uint32) => ((b:uint32) => a * b);
export let mul_underspec = (a:uint32) => ((b:uint32) => mul(a)(b));
export let mul_mod = (a:uint32) => ((b:uint32) => mul(a)(b) & 4294967295);

export let div = (a:uint32) : ((b:uint32) => uint32) => ((b:uint32) => a / b);

export let rem = (a:uint32) : ((b:uint32) => uint32) => ((b:uint32) => a % b);

export let logand = (a:uint32) : ((b:uint32) => uint32) => ((b:uint32) => a & b);
export let logxor = (a:uint32) : ((b:uint32) => uint32) => ((b:uint32) => a ^ b);
export let logor  = (a:uint32) : ((b:uint32) => uint32) => ((b:uint32) => a | b);
export let lognot = (a:uint32) : uint32 => ~a;

export let int_to_uint32 =  (x:number) => x % 4294967296;

export let shift_right = (a:uint32) : ((b:uint32) => uint32) => ((b:uint32) => (a >> b));
export let shift_left = (a:uint32) : ((b:uint32) => uint32) => ((b:uint32) => (a << b) & 4294967295);  

/* Comparison operators */
export let eq = (a:uint32) : ((b:uint32) => boolean) => ((b:uint32) => (a == b)); 
export let gt = (a:uint32) : ((b:uint32) => boolean) => ((b:uint32) => (a > b));
export let gte = (a:uint32) : ((b:uint32) => boolean) => ((b:uint32) => (a >= b));
export let lt = (a:uint32) : ((b:uint32) => boolean) => ((b:uint32) => (a < b));
export let lte = (a:uint32) : ((b:uint32) => boolean) => ((b:uint32) => (a <= b));
                                             
/* Infix notations */
export let op_Plus_Hat = add;
export let op_Plus_Question_Hat = add_underspec;
export let op_Plus_Percent_Hat = add_mod;
export let op_Subtraction_Hat = sub;
export let op_Subtraction_Question_Hat = sub_underspec;
export let op_Subtraction_Percent_Hat = sub_mod;
export let op_Star_Hat = mul;
export let op_Star_Question_Hat = mul_underspec;
export let op_Star_Percent_Hat = mul_mod;
export let op_Slash_Hat = div;
export let op_Percent_Hat = rem;
export let op_Hat_Hat = logxor;
export let op_Amp_Hat = logand;
export let op_Bar_Hat = logor;
export let op_Less_Less_Hat = shift_left;
export let op_Greater_Greater_Hat = shift_right;
export let op_Equals_Hat = eq;
export let op_Greater_Hat = gt;
export let op_Greater_Equals_Hat = gte;
export let op_Less_Hat = lt;
export let op_Less_Equals_Hat = lte;


export let of_string = (s : string) => parseInt(s);
export let to_string = (s : number) => s.toString();
export let to_int = (s : number) => s;
export let uint_to_t = (s : number) => int_to_uint32(s);