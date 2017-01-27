include Interval1

let zero_I = {low = 0.0; high = 0.0;}

let one_I = {low = 1.0; high = 1.0;}

let fprintf_I fp format i = 
  Printf.fprintf fp "[%s, %s]" 
    (Printf.sprintf format i.low) (Printf.sprintf format i.high) 

let sprintf_I format i = 
  Printf.sprintf "[%s, %s]" 
    (Printf.sprintf format i.low) (Printf.sprintf format i.high) 

              
let compare_I_f {low = a; high = b} x =
  if b < x then 1 else if a <= x then 0 else -1
              
let abs_I = abs_i

let (~-$) = neg_i

let (+$) = add_ii

let (-$) = sub_ii

let ( *$) = mul_ii

let ( *.$) = mul_di

let ( *$.) = mul_id
              
let (/$) = div_ii

let (/.$) = div_di

let (/$.) = div_id

let inv_I = inv_i
             
let sqrt_I = sqrt_i

let sqr_I {low = a; high = b} =
  if 0.0 <= a then {
      low = fmul_low a a;
      high = fmul_high b b;
    }
  else if b <= 0.0 then {
      low = fmul_low b b;
      high = fmul_high a a;
    }
  else {
      low = 0.0;
      high = fsucc (max (a *. a) (b *. b));
    }
               
let pow_I_i ({low = a; high = b} as v) n =
  match n with
  | 1 -> v
  | 2 -> sqr_I v
  | 3 -> {
      (* The sign should be preserved by fmul_low and fmul_high *)
      low = fmul_low (fmul_low a a) a;
      high = fmul_high (fmul_high b b) b;
    }
  | _ -> failwith "pow_I_i: Not implemented"
        
let ( **$.) (x:interval) (f:float) = failwith "(**$.): Not implemented" 
               
let exp_I = exp_i

let log_I = log_i

let cos_I = cos_i

let sin_I = sin_i

let tan_I x = failwith "tan_I: Not implemented"

let asin_I x = failwith "asin_I: Not implemented"

let acos_I x = failwith "acos_I: Not implemented"

let atan_I x = failwith "atan_I: Not implemented"

let sinh_I x = failwith "sinh_I: Not implemented"

let cosh_I x = failwith "cosh_I: Not implemented"

let tanh_I x = failwith "tanh_I: Not implemented"

let size_max_X v =
  Array.fold_left (fun m {low = a; high = b} -> max m (fsub_high b a)) 0.0 v
