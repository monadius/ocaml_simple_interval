let u_float = ldexp 1.0 (-53)

let eta_float = ldexp 1.0 (-1074)

let phi_float = u_float *. (1.0 +. 2.0 *. u_float)

let inv_u_float = 1.0 /. u_float

let bound1_float = 0.5 *. (eta_float /. (u_float *. u_float))

let bound2_float = eta_float /. u_float
                                    
let min_float2 = 2.0 *. min_float
               
let _ = assert (min_float = 0.5 *. (1.0 /. u_float) *. eta_float)
let _ = assert (min_float2 = ldexp 1.0 (-1021))
let _ = assert (bound1_float = ldexp 1.0 (-969))
let _ = assert (bound2_float = ldexp 1.0 (-1021))
               
(* succ and pred from the RZBM09 paper *)
(* Algorithm 2 *)
               
let fsucc x =
  let c = abs_float x in
  if c >= bound1_float then
    x +. phi_float *. c
  else if c < bound2_float then
    x +. eta_float
  else
    let y = inv_u_float *. x in
    let e = phi_float *. abs_float y in
    (y +. e) *. u_float

let fpred x =
  let c = abs_float x in
  if c >= bound1_float then
    x -. phi_float *. c
  else if c < bound2_float then
    x -. eta_float
  else
    let y = inv_u_float *. x in
    let e = phi_float *. abs_float y in
    (y -. e) *. u_float

(* requires: |a| >= |b| *)
let fast_two_sum a b =
  let x = a +. b in
  let t = x -. a in
  let y = b -. t in
  (x, y)

let two_sum1 a b =
  if abs_float a < abs_float b then
    fast_two_sum b a
  else
    fast_two_sum a b

(* The second line may overflow even if the first line does not:
   a = -1.5 *. ldexp 1.0 (1024 - 53)
   b = max_float *)
let two_sum2 a b =
  let x = a +. b in
  let bv = x -. a in
  let av = x -. bv in
  let br = b -. bv in
  let ar = a -. av in
  let y = ar +. br in
  (x, y)

let two_sum = two_sum1

let split =
  let factor = ldexp 1. 27 +. 1. in
  fun a ->
  let c = factor *. a in
  let x = c -. (c -. a) in
  let y = a -. x in
  (x, y)

let two_product a b =
  let x = a *. b in
  let a1, a2 = split a in
  let b1, b2 = split b in
  let r1 = x -. a1 *. b1 in
  let r2 = r1 -. a2 *. b1 in
  let r3 = r2 -. a1 *. b2 in
  let y = a2 *. b2 -. r3 in
  (x, y)

let fadd_low x y =
  let (z, r) = two_sum x y in
  if z = infinity then max_float
  else
    if r >= 0. then z else fpred z

let fadd_high x y =
  let (z, r) = two_sum x y in
  if z = neg_infinity then -.max_float
  else
    if r <= 0. then z else fsucc z

let fsub_low x y = fadd_low x (-.y)

let fsub_high x y = fadd_high x (-.y)


(**************)
                              
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

let fmul_low x y =
  let (z, r) = two_product x y in
  if z = infinity then max_float
  else if z = 0. then
    if (x >= 0. && y >= 0.) || (x <= 0. && y <= 0.) then 0.
    else -.eta_float
  else
    if r >= 0. then z else fpred z

let fmul_high x y =
  let (z, r) = two_product x y in
  if z = neg_infinity then -.max_float
  else if z = 0. then
    if (x >= 0. && y <= 0.) || (x <= 0. && y >= 0.) then 0.
    else eta_float
  else
    if r <= 0. then z else fsucc z

let fdiv_low x y =
  if x = 0. then (if y <> 0. then 0. else nan)
  else
    let r = x /. y in
    if r = infinity then max_float
    else if r = 0. then
      if (x >= 0. && y >= 0.) || (x <= 0. && y <= 0.) then 0.
      else -.eta_float
    else
      fpred r

let fdiv_high x y =
  if x = 0. then (if y <> 0. then 0. else nan)
  else
    let r = x /. y in
    if r = neg_infinity then -.max_float
    else if r = 0. then
      if (x >= 0. && y <= 0.) || (x <= 0. && y >= 0.) then 0.
      else eta_float
    else
      fsucc r

let fsqrt_low x =
  if x = 0. then 0.
  else
    let r = sqrt x in
    if r = infinity then max_float
    else fpred r

let fsqrt_high x = if x = 0. then 0. else fsucc (sqrt x)

let fexp_low x =
  let r = exp x in
  if r = infinity then max_float
  else if r > 0. then fpred r
  else 0.

let fexp_high x = fsucc (exp x)

let flog_low x =
  if x = 1. then 0.
  else
    let r = log x in
    if r = infinity then max_float
    else fpred r

let flog_high x =
  if x = 1. then 0.
  else
    let r = log x in
    if r = neg_infinity then -.max_float
    else fsucc r

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
                          
let rec fpown_low_pos x n =
  assert (x >= 0. && n > 0);
  if n = 1 || x = 0. then x
  else if n = 2 then fmul_low x x
  else if n = 3 then fmul_low x (fmul_low x x)
  else if n land 1 = 0 then
    let t = fpown_low_pos x (n lsr 1) in
    fmul_low t t
  else
    fmul_low x (fpown_low_pos x (n - 1))

let rec fpown_high_pos x n =
  assert (x >= 0. && n > 0);
  if n = 1 || x = 0. then x
  else if n = 2 then fmul_high x x
  else if n = 3 then fmul_high x (fmul_high x x)
  else if n land 1 = 0 then
    let t = fpown_high_pos x (n lsr 1) in
    fmul_high t t
  else
    fmul_high x (fpown_high_pos x (n - 1))

let fpown_low x n =
  match n with
  | 0 -> 1.
  | 1 -> x
  | 2 -> fmul_low x x
  | n when (n land 1 = 0) || x >= 0. -> begin
      let a = abs_float x in
      if n > 0 then
        if a = infinity then max_float
        else fpown_low_pos a n
      else
        if a = infinity then 0.
        else if a = 0. then nan
        else fdiv_low 1.0 (fpown_high_pos a (-n))
    end
  | _ -> begin
      let a = -.x in
      if n > 0 then
        if a = infinity then neg_infinity
        else -.fpown_high_pos a n
      else
        if a = infinity then -.eta_float
        else if a = 0. then nan
        else -.(fdiv_high 1.0 (fpown_low_pos a (-n)))
    end

let fpown_high x n =
  match n with
  | 0 -> 1.
  | 1 -> x
  | 2 -> fmul_high x x
  | n when (n land 1 = 0) || x >= 0. -> begin
      let a = abs_float x in
      if n > 0 then
        if a = infinity then infinity
        else fpown_high_pos a n
      else
        if a = infinity then eta_float
        else if a = 0. then nan
        else fdiv_high 1.0 (fpown_low_pos a (-n))
    end
  | _ -> begin
      let a = -.x in
      if n > 0 then
        if a = infinity then -.max_float
        else -.fpown_low_pos a n
      else
        if a = infinity then 0.
        else if a = 0. then nan
        else -.(fdiv_low 1.0 (fpown_high_pos a (-n)))
    end
     
(* 
Alternative implementation for n >= 4:
let fpown_high x n =
  fexp_high (float_of_int n *. flog_high x)
*)
                                                
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

let mid_i_fast {low = a; high = b} = 0.5 *. (a +. b)

let mid_i {low = a; high = b} =
  if a = neg_infinity then
    if b = infinity then 0. else -.max_float
  else if b = infinity then max_float
  else
    let m = 0.5 *. (a +. b) in
    if m = infinity || m = neg_infinity then
      0.5 *. a +. 0.5 *. b
    else m
                          
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
      low = if a *. d < b *. c then fmul_low a d else fmul_low b c;
      high = if a *. c > b *. d then fmul_high a c else fmul_high b d;
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
  if a = infinity || c = infinity || (c = 0. && d = 0.) then
    empty_interval
  else if c > 0.0 then {
      low = (if a >= 0.0 then fdiv_low a d else fdiv_low a c);
      high = (if b <= 0.0 then fdiv_high b d else fdiv_high b c);
    }
  else if d < 0.0 then {
      low = (if b <= 0.0 then fdiv_low b c else fdiv_low b d);
      high = (if a >= 0.0 then fdiv_high a c else fdiv_high a d);
    }
  else if a = 0. && b = 0. then zero_interval
  else if c = 0. then {
      low = if a >= 0. then fdiv_low a d else neg_infinity;
      high = if b <= 0. then fdiv_high b d else infinity;
    }
  else if d = 0. then {
      low = if b <= 0. then fdiv_low b c else neg_infinity;
      high = if a >= 0. then fdiv_high a c else infinity;
    }
  else entire_interval

let div_id {low = a; high = b} c =
  if a = infinity then empty_interval
  else if c > 0.0 then {
      low = fdiv_low a c;
      high = fdiv_high b c;
    }
  else if c < 0.0 then {
      low = fdiv_low b c;
      high = fdiv_high a c;
    }
  else empty_interval

let div_di a {low = c; high = d} =
  if c = infinity then empty_interval
  else if c > 0. then begin
      if a >= 0. then {
          low = fdiv_low a d;
          high = fdiv_high a c;
        }
      else {
          low = fdiv_low a c;
          high = fdiv_high a d;
        }
    end
  else if d < 0. then begin
      if a >= 0. then {
          low = fdiv_low a d;
          high = fdiv_high a c;
        }
      else {
          low = fdiv_low a c;
          high = fdiv_high a d;
        }
    end
  else if c = 0. && d = 0. then empty_interval
  else if a = 0. then zero_interval
  else if c = 0. then begin
      if a >= 0. then {
          low = fdiv_low a d;
          high = infinity;
        }
      else {
          low = neg_infinity;
          high = fdiv_high a d;
        }
    end
  else if d = 0. then begin
      if a >= 0. then {
          low = neg_infinity;
          high = fdiv_high a c;
        }
      else {
          low = fdiv_low a c;
          high = infinity;
        }
    end
  else entire_interval

let inv_i {low = a; high = b} =
  if a = infinity then empty_interval
  else if 0. < a || b < 0. then {
      low = fdiv_low 1. b;
      high = fdiv_high 1. a;
    }
  else if a = 0. then begin
      if b = 0. then empty_interval
      else {
          low = fdiv_low 1. b;
          high = infinity;
        }
    end
  else if b = 0. then {
      low = neg_infinity;
      high = fdiv_high 1. a;
    }
  else entire_interval
         
let sqrt_i {low = a; high = b} =
  if b < 0. then empty_interval
  else {
      low = if a <= 0. then 0. else fsqrt_low a;
      high = fsqrt_high b;
    }

let sqr_i {low = a; high = b} =
  if a = infinity then empty_interval
  else if a >= 0. then
    {low = fmul_low a a; high = fmul_high b b}
  else if b <= 0. then
    {low = fmul_low b b; high = fmul_high a a}
  else
    let t = max (-.a) b in
    {low = 0.; high = fsucc (t *. t)}

let pown_i ({low = a; high = b} as v) n =
  if a = infinity then empty_interval
  else
    match n with
    | 0 -> one_interval
    | 1 -> v
    | 2 -> sqr_i v
    | n when (n land 1 = 1) -> begin
        if n > 0 then
          {low = fpown_low a n; high = fpown_high b n}
        else begin
            if a = 0. && b = 0. then empty_interval
            else if a >= 0. then {
                low = fpown_low b n;
                high = if a = 0. then infinity else fpown_high a n;
              }
            else if b <= 0. then {
                low = if b = 0. then neg_infinity else fpown_low b n;
                high = fpown_high a n;
              }
            else entire_interval
          end
      end
    | _ -> begin
        if n > 0 then begin
            if a >= 0. then
              {low = fpown_low a n; high = fpown_high b n}
            else if b <= 0. then
              {low = fpown_low b n; high = fpown_high a n}
            else
              let t = max (-.a) b in
              {low = 0.; high = fpown_high t n}
          end
        else begin
            if a = 0. && b = 0. then empty_interval
            else if a >= 0. then {
                low = fpown_low b n;
                high = if a = 0. then infinity else fpown_high a n;
              }
            else if b <= 0. then {
                low = fpown_low a n;
                high = if b = 0. then infinity else fpown_high b n;
              }
            else {
                low = fpown_low (max (-.a) b) n;
                high = infinity;
              }
          end
      end
         
let exp_i {low = a; high = b} =
  if a = infinity then empty_interval
  else {
    low = fexp_low a;
    high = fexp_high b;
  }

let log_i {low = a; high = b} =
  if b < 0. then empty_interval
  else {
    low = if a <= 0. then neg_infinity else flog_low a;
    high = flog_high b;
  }

let sin_i {low = a; high = b} =
  failwith "Not implemented"

let cos_i {low = a; high = b} =
  failwith "Not implemented"



let b = 1.10093729974551529399e-154 and
    a = 1.07564707968713109890e-154 and
    d = 1.38199047941268172594e-154 and
    c = 1.35537116210643683205e-154

let _ = two_product a c
