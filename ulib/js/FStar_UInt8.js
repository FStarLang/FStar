/* @flow */

export type uint8 = number;
export type byte = uint8;
export type t = uint8;

export let v = (x:uint8): number => x;

export let zero = 0;
export let one = 1;
export let ones = 255;
                                              
export let add = (a:uint8) : ((b:uint8) => uint8) => ((b:uint8) => a + b);
export let add_underspec = (a:uint8) => ((b:uint8) => add(a)(b));
export let add_mod = (a:uint8) => ((b:uint8) => add(a)(b) & 255);

export let sub = (a:uint8) : ((b:uint8) => uint8) => ((b:uint8) => a - b);
export let sub_underspec = (a:uint8) => ((b:uint8) => sub(a)(b));
export let sub_mod = (a:uint8) => ((b:uint8) => sub(a)(b) & 255);

export let mul = (a:uint8) : ((b:uint8) => uint8) => ((b:uint8) => a * b);
export let mul_underspec = (a:uint8) => ((b:uint8)=> mul(a)(b));
export let mul_mod = (a:uint8) => ((b:uint8) => mul(a)(b) & 255);

export let div = (a:uint8) : ((b:uint8) => uint8) => ((b:uint8) => Math.floor(a / b));

export let rem = (a:uint8) : ((b:uint8) => uint8) => ((b:uint8) => a % b);

export let logand = (a:uint8) : ((b:uint8) => uint8) => ((b:uint8) => a & b);
export let logxor = (a:uint8) : ((b:uint8) => uint8) => ((b:uint8) => a ^ b);
export let logor  = (a:uint8) : ((b:uint8) => uint8) => ((b:uint8) => a | b);
export let lognot = (a:uint8) : uint8 => ~a;

export let int_to_uint8 =  (x:number) => x % 256;

export let shift_right = (a:uint8) : ((b:uint8) => uint8) => ((b:uint8) => (a >>> b));
export let shift_left = (a:uint8) : ((b:uint8) => uint8) => ((b:uint8) => (a << b) & 255);  

export let gte_mask = (a:uint8) : ((b:uint8) => uint8) => ((b:uint8) => ~((a-b) >> 62) & 255);
export let eq_mask = (a:uint8) : ((b:uint8) => uint8) => ((b:uint8) => gte_mask(a)(b) & gte_mask(b)(a));

/* Comparison operators */
export let eq = (a:uint8) : ((b:uint8) => boolean) => ((b:uint8) => (a == b)); 
export let gt = (a:uint8) : ((b:uint8) => boolean) => ((b:uint8) => (a > b));
export let gte = (a:uint8) : ((b:uint8) => boolean) => ((b:uint8) => (a >= b));
export let lt = (a:uint8) : ((b:uint8) => boolean) => ((b:uint8) => (a < b));
export let lte = (a:uint8) : ((b:uint8) => boolean) => ((b:uint8) => (a <= b));
                                             
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
export let uint_to_t = (s :number) => int_to_uint8(s);