let u_float = ldexp 1.0 (-53)

let eta_float = ldexp 1.0 (-1074)

let phi_float = u_float *. (1.0 +. 2.0 *. u_float)

let min_float2 = 2.0 *. min_float
               
let _ = assert (min_float = 0.5 *. (1.0 /. u_float) *. eta_float)
let _ = assert (min_float2 = ldexp 1.0 (-1021))
               
(* succ and pred from the RZBM09 paper *)
(* Algorithm 1 *)
               
let fsucc x =
  let e = phi_float *. abs_float x +. eta_float in
  x +. e

let fpred x =
  let e = phi_float *. abs_float x +. eta_float in
  x -. e

let fadd_low x y =
  let r = x +. y in
  if r = infinity then max_float
  (* TODO: replace with r = 0.0; 
     should be faster and the accuracy is not important for subnormal results *)
  else if -.min_float2 < r && r < min_float2 then r
  else fpred r

let fadd_high x y =
  let r = x +. y in
  if r = neg_infinity then -.max_float
  else if -.min_float2 < r && r < min_float2 then r
  else fsucc r

let fsub_low x y =
  let r = x -. y in
  if r = infinity then max_float
  else if -.min_float2 < r && r <  min_float2 then r
  else fpred r

let fsub_high x y =
  let r = x -. y in
  if r = neg_infinity then -.max_float
  else if -.min_float2 < r && r < min_float2 then r
  else fsucc r

let fmul_low x y =
  if x = 0. || y = 0. then 0.
  else
    let r = x *. y in
    if r = infinity then max_float
    else if r = 0. then
      if (x >= 0. && y >= 0.) || (x <= 0. && y <= 0.) then 0.
      else -.eta_float
    else
      fpred r

let fmul_high x y =
  if x = 0. || y = 0. then 0.
  else
    let r = x *. y in
    if r = neg_infinity then -.max_float
    else if r = 0. then
      if (x >= 0. && y <= 0.) || (x <= 0. && y >= 0.) then 0.
      else eta_float
    else
      fsucc r

let fdiv_low x y = fpred (x /. y)

let fdiv_high x y = fsucc (x /. y)

let fsqrt_low x = if x = 0.0 then 0.0 else fpred (sqrt x)

let fsqrt_high x = if x = 0.0 then 0.0 else fsucc (sqrt x)

let fexp_low x =
  let r = exp x in
  if r > 0.0 then
    fpred r
  else
    0.0

let fexp_high x = fsucc (exp x)

let flog_low x = fpred (log x)

let flog_high x = fsucc (log x)

let fcos_low x =
  let r = cos x in
  if r > -1.0 then
    fpred r
  else if r <> r then
    nan
  else
    -1.0

let fcos_high x =
  let r = cos x in
  if r < 1.0 then
    fsucc r
  else if r <> r then
    nan
  else
    1.0

let fsin_low x =
  let r = sin x in
  if r > -1.0 then
    fpred r
  else if r <> r then
    nan
  else
    -1.0

let fsin_high x =
  let r = sin x in
  if r < 1.0 then
    fsucc r
  else if r <> r then
    nan
  else
    1.0
                          

type interval = {
    low: float;
    high: float;
  }

let is_empty {low = a; high = b} = (a = infinity && b = neg_infinity)

let is_valid ({low = a; high = b} as v) =
  (a <= b && a < infinity && neg_infinity < b) || is_empty v
                  
let empty_interval = {low = infinity; high = neg_infinity}

let entire_interval = {low = neg_infinity; high = infinity}
                       
let zero_interval = {low = 0.0; high = 0.0}

let one_interval = {low = 1.0; high = 1.0}
                  
let make_interval a b = {low = a; high = b}
                  
let neg_i {low = a; high = b} = {
    low = -.b;
    high = -.a;
  }

let abs_i ({low = a; high = b} as v) =
  (* The first condition handles positive and empty intervals *)
  if 0.0 <= a then v
  else if b <= 0.0 then
    {low = -.b; high = -.a}
  else
    {low = 0.0; high = max (-.a) b}
                 
let add_ii {low = a; high = b} {low = c; high = d} =
  if a = infinity || c = infinity then empty_interval
  else {
    low = fadd_low a c;
    high = fadd_high b d;
  }

let add_id {low = a; high = b} c =
  if a = infinity then empty_interval
  else {
    low = fadd_low a c;
    high = fadd_high b c;
  }

let add_di c {low = a; high = b} =
  if a = infinity then empty_interval
  else {
    low = fadd_low c a;
    high = fadd_high c b;
  }

let sub_ii {low = a; high = b} {low = c; high = d} =
  if a = infinity || c = infinity then empty_interval
  else {
    low = fsub_low a d;
    high = fsub_high b c;
  }

let sub_id {low = a; high = b} c =
  if a = infinity then empty_interval
  else {
    low = fsub_low a c;
    high = fsub_high b c;
  }

let sub_di c {low = a; high = b} =
  if a = infinity then empty_interval
  else {
    low = fsub_low c b;
    high = fsub_high c a;
  }

let mul_ii {low = a; high = b} {low = c; high = d} =
  if a = infinity || c = infinity then empty_interval
  else if a >= 0.0 then {
      low = (if c >= 0.0 then fmul_low a c else fmul_low b c);
      high = (if d >= 0.0 then fmul_high b d else fmul_high a d);
    }
  else if b <= 0.0 then {
      low = (if d <= 0.0 then fmul_low b d else fmul_low a d);
      high = (if c <= 0.0 then fmul_high a c else fmul_high b c);
    }
  else if c >= 0.0 then {
      low = fmul_low a d;
      high = fmul_high b d;
    }
  else if d <= 0.0 then {
      low = fmul_low b c;
      high = fmul_high a c;
    }
  else {
      low = fpred (min (a *. d) (b *. c));
      high = fsucc (max (a *. c) (b *. d));
    }
      
let mul_id {low = a; high = b} c =
  if a = infinity then empty_interval
  else if c > 0.0 then {
      low = fmul_low a c;
      high = fmul_high b c;
    }
  else if c < 0.0 then {
      low = fmul_low b c;
      high = fmul_high a c;
    }
  else if c = 0.0 then {
      low = 0.0;
      high = 0.0;
    }
  else {
      low = nan;
      high = nan;
    }
                    
let mul_di c i = mul_id i c
    
let div_ii {low = a; high = b} {low = c; high = d} =
  if c > 0.0 then {
      low = (if a >= 0.0 then fdiv_low a d else fdiv_low a c);
      high = (if b <= 0.0 then fdiv_high b d else fdiv_high b c);
    }
  else if d < 0.0 then {
      low = (if b <= 0.0 then fdiv_low b c else fdiv_low b d);
      high = (if a >= 0.0 then fdiv_high a c else fdiv_high a d);
    }
  else {
      low = nan;
      high = nan;
    }

let div_id {low = a; high = b} c =
  if c > 0.0 then {
      low = fdiv_low a c;
      high = fdiv_high b c;
    }
  else if c < 0.0 then {
      low = fdiv_low b c;
      high = fdiv_high a c;
    }
  else {
      low = nan;
      high = nan;
    }

let div_di a {low = c; high = d} =
  if c > 0.0 then
    begin
      if a >= 0.0 then {
          low = fdiv_low a d;
          high = fdiv_high a c;
        }
      else {
          low = fdiv_low a c;
          high = fdiv_high a d;
        }
    end
  else if d < 0.0 then
    begin
      if a >= 0.0 then {
          low = fdiv_low a d;
          high = fdiv_high a c;
        }
      else {
          low = fdiv_low a c;
          high = fdiv_high a d;
        }
    end
  else {
      low = nan;
      high = nan;
    }

let inv_i {low = a; high = b} =
  if a > 0.0 || b < 0.0 then {
      low = fdiv_low 1.0 b;
      high = fdiv_high 1.0 a;
    }
  else {
      low = nan;
      high = nan;
    }
         
let sqrt_i {low = a; high = b} = {
    low = fsqrt_low a;
    high = fsqrt_high b;
  }
         
let exp_i {low = a; high = b} = {
    low = fexp_low a;
    high = fexp_high b;
  }

let log_i {low = a; high = b} = {
    low = flog_low a;
    high = flog_high b;
  }

let sin_i {low = a; high = b} =
  failwith "Not implemented"

let cos_i {low = a; high = b} =
  failwith "Not implemented"

