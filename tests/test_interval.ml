open Num

(* Auxiliary functions *)

let next_float x =
  match classify_float x with
  | FP_nan -> nan
  | FP_infinite ->
     if x = infinity then x else nan
  | FP_zero -> ldexp 1.0 (-1074)
  | _ ->
     begin
       let bits = Int64.bits_of_float x in
       if x < 0.0 then
         Int64.float_of_bits (Int64.pred bits)
       else
         Int64.float_of_bits (Int64.succ bits)
     end
                               
let prev_float x =
  match classify_float x with
  | FP_nan -> nan
  | FP_infinite ->
     if x = neg_infinity then x else nan
  | FP_zero -> ldexp (-1.0) (-1074)
  | _ ->
     begin
       let bits = Int64.bits_of_float x in
       if x < 0.0 then
         Int64.float_of_bits (Int64.succ bits)
       else
         Int64.float_of_bits (Int64.pred bits)
     end

let num_of_float x =
  match classify_float x with
  | FP_zero -> Int 0
  | FP_normal | FP_subnormal ->
     begin
       let m, e = frexp x in
       let t = Int64.of_float (ldexp m 53) in
       num_of_big_int (Big_int.big_int_of_int64 t) */ (Int 2 **/ Int (e - 53))
     end
  | _ ->
     failwith (Printf.sprintf "num_of_float: %e" x)

(* Returns the integer binary logarithm of big_int  *)
(* Returns -1 for non-positive numbers              *)
let log2_big_int_simple =
  let rec log2 acc k =
    if Big_int.sign_big_int k <= 0 then acc
    else log2 (acc + 1) (Big_int.shift_right_big_int k 1) in
  log2 (-1)

let log2_big_int =
  let p = 32 in
  let u = Big_int.power_int_positive_int 2 p in
  let rec log2 acc k =
    if Big_int.ge_big_int k u then
      log2 (acc + p) (Big_int.shift_right_big_int k p)
    else
      acc + log2_big_int_simple k in
  log2 0

(* Returns the integer binary logarithm of the absolute value of num *)
let log2_num r =
  let log2 r = log2_big_int (big_int_of_num (floor_num r)) in
  let r = abs_num r in
  if r </ Int 1 then
    let t = -log2 (Int 1 // r) in
    if (Int 2 **/ Int t) =/ r then t else t - 1
  else log2 r

let float_of_pos_num_lo r =
  assert (sign_num r >= 0);
  if sign_num r = 0 then 0.0
  else begin
      let n = log2_num r in
      let k = min (n + 1074) 52 in
      if k < 0 then 0.0
      else
        let m = big_int_of_num (floor_num ((Int 2 **/ Int (k - n)) */ r)) in
        let f = Int64.to_float (Big_int.int64_of_big_int m) in
        let x = ldexp f (n - k) in
        if x = infinity then max_float else x
    end

let float_of_pos_num_hi r =
  assert (sign_num r >= 0);
  if sign_num r = 0 then 0.0
  else begin
      let n = log2_num r in
      let k = min (n + 1074) 52 in
      if k < 0 then ldexp 1.0 (-1074)
      else
        let t = (Int 2 **/ Int (k - n)) */ r in
        let m0 = floor_num t in
        let m = if t =/ m0 then big_int_of_num m0
                else Big_int.succ_big_int (big_int_of_num m0) in
        let f = Int64.to_float (Big_int.int64_of_big_int m) in
        ldexp f (n - k)
    end
        
let float_of_num_lo r =
  if sign_num r < 0 then
    -. float_of_pos_num_hi (minus_num r)
  else
    float_of_pos_num_lo r

let float_of_num_hi r =
  if sign_num r < 0 then
    -. float_of_pos_num_lo (minus_num r)
  else
    float_of_pos_num_hi r

let rec float_min_nan = function
  | [] -> failwith "float_min_nan: empty list"
  | [x] -> x
  | x :: xs -> if x <> x then nan
               else let t = float_min_nan xs in
                    if t <> t || t < x then t else x

let rec float_max_nan = function
  | [] -> failwith "float_max_nan: empty list"
  | [x] -> x
  | x :: xs -> if x <> x then nan
               else let t = float_max_nan xs in
                    if t <> t || t > x then t else x

let rec float_min = function
  | [] -> infinity
  | x :: xs -> if x = x then min x (float_min xs)
               else float_min xs

let rec float_max = function
  | [] -> neg_infinity
  | x :: xs -> if x = x then max x (float_max xs)
               else float_max xs

                                                     
(* We consider that 0.0 is a real 0 and 0.0 = -0.0.
   We consider that infinity represents a finite positive number and
   neg_infinity represents a finite negative number.
   Under these assumptions we have:
   0.0 * infinity = 0.0,
   infinity + infinity = infinity,
   infinity + neg_infinity = nan (we don't know the sign of the result),
   etc.
 *)

let round_hi z r =
  match classify_float z with
  | FP_nan -> z
  | FP_infinite ->
     if z = infinity then z
     else -.max_float
  | _ ->
     let rz = num_of_float z in
     if compare_num rz r >= 0 then z
     else next_float z

let round_lo z r =
  match classify_float z with
  | FP_nan -> z
  | FP_infinite ->
     if z = neg_infinity then z
     else max_float
  | _ ->
     let rz = num_of_float z in
     if compare_num rz r <= 0 then z
     else prev_float z
                          
let fadd_lo x y =
  match classify_float x, classify_float y with
  | FP_zero, _ -> y
  | _, FP_zero -> x
  | FP_nan, _ | _, FP_nan -> nan
  | FP_infinite, _ | _, FP_infinite ->
     let r = x +. y in
     assert (r = infinity || r = neg_infinity || r <> r);
     r
  | _ -> 
     let r = num_of_float x +/ num_of_float y in
     round_lo (x +. y) r

let fadd_hi x y =
  match classify_float x, classify_float y with
  | FP_zero, _ -> y
  | _, FP_zero -> x
  | FP_nan, _ | _, FP_nan -> nan
  | FP_infinite, _ | _, FP_infinite ->
     let r = x +. y in
     assert (r = infinity || r = neg_infinity || r <> r);
     r
  | _ ->
     let r = num_of_float x +/ num_of_float y in
     round_hi (x +. y) r

let fsub_lo x y = fadd_lo x (-.y)

let fsub_hi x y = fadd_hi x (-.y)
                     
let fmul_lo x y =
  match classify_float x, classify_float y with
  | FP_nan, _ | _, FP_nan -> nan
  | FP_zero, _ | _, FP_zero -> 0.0
  | FP_infinite, _ | _, FP_infinite ->
     let r = x *. y in
     assert (r = infinity || r = neg_infinity);
     if r = infinity then max_float
     else r
  | _ -> 
     let r = num_of_float x */ num_of_float y in
     round_lo (x *. y) r

let fmul_hi x y =
  match classify_float x, classify_float y with
  | FP_nan, _ | _, FP_nan -> nan
  | FP_zero, _ | _, FP_zero -> 0.0
  | FP_infinite, _ | _, FP_infinite ->
     let r = x *. y in
     assert (r = infinity || r = neg_infinity);
     if r = neg_infinity then -.max_float
     else r
  | _ -> 
     let r = num_of_float x */ num_of_float y in
     round_hi (x *. y) r

let fdiv_lo x y =
  match classify_float x, classify_float y with
  | _, FP_zero -> nan
  | FP_nan, _ | _, FP_nan -> nan
  | FP_zero, _ -> 0.0
  | FP_infinite, FP_infinite -> nan
  | FP_infinite, _ | _, FP_infinite ->
     let r = x /. y in
     assert (r = infinity || r = neg_infinity || r = 0.);
     if r = infinity then max_float
     else if r = 0. then
       if (x >= 0. && y >= 0.) || (x <= 0. && y <= 0.) then 0.
       else -.ldexp 1. (-1074)
     else neg_infinity
  | _ -> 
     let r = num_of_float x // num_of_float y in
     round_lo (x /. y) r

let fdiv_hi x y =
  match classify_float x, classify_float y with
  | _, FP_zero -> nan
  | FP_nan, _ | _, FP_nan -> nan
  | FP_zero, _ -> 0.0
  | FP_infinite, FP_infinite -> nan
  | FP_infinite, _ | _, FP_infinite ->
     let r = x /. y in
     assert (r = infinity || r = neg_infinity || r = 0.);
     if r = neg_infinity then -.max_float
     else if r = 0. then
       if (x >= 0. && y <= 0.) || (x <= 0. && y >= 0.) then 0.
       else ldexp 1. (-1074)
     else infinity
  | _ -> 
     let r = num_of_float x // num_of_float y in
     round_hi (x /. y) r

let fsqrt_lo x =
  match classify_float x with
  | FP_nan -> nan
  | FP_infinite -> sqrt x
  | FP_zero -> 0.0
  | _ ->
     if x < 0.0 then nan
     else
       let z = sqrt x in
       let rx = num_of_float x and
           rz = num_of_float z in
       if compare_num (rz */ rz) rx > 0 then prev_float z
       else z

let fsqrt_hi x =
  match classify_float x with
  | FP_nan -> nan
  | FP_infinite -> sqrt x
  | FP_zero -> 0.0
  | _ ->
     if x < 0.0 then nan
     else
       let z = sqrt x in
       let rx = num_of_float x and
           rz = num_of_float z in
       if compare_num (rz */ rz) rx < 0 then next_float z
       else z

(* We assume that x^0 = 1 for any x (nan excluded) *)
let fpown_lo x n =
  match classify_float x with
  | FP_nan -> nan
  | FP_zero ->
     if n = 0 then 1.0
     else if n < 0 then nan
     else 0.0
  | FP_infinite ->
     if n = 0 then 1.0
     else if x = infinity then
       if n < 0 then 0.0 else infinity
     else if n land 1 = 0 then 0.0
     else neg_infinity
  | _ ->
     let r = num_of_float x **/ Int n in
     float_of_num_lo r

let fpown_hi x n =
  match classify_float x with
  | FP_nan -> nan
  | FP_zero ->
     if n = 0 then 1.0
     else if n < 0 then nan
     else 0.0
  | FP_infinite ->
     if n = 0 then 1.0
     else if x = infinity then infinity
     else if n land 1 = 1 then 0.0
     else infinity
  | _ ->
     let r = num_of_float x **/ Int n in
     float_of_num_hi r
     
(* Interval type and functions *)

(* [0, +infinity] contains all finite positive numbers, etc. *)
(* [+infinity, -infinity] represents the only valid empty interval *)

type ti = {
    lo: float;
    hi: float
  }

let empty_interval = {lo = infinity; hi = neg_infinity}

let entire_interval = {lo = neg_infinity; hi = infinity}
                       
let zero_interval = {lo = 0.0; hi = 0.0}

let one_interval = {lo = 1.0; hi = 1.0}

let is_empty {lo; hi} = (lo = infinity && hi = neg_infinity)

let is_entire {lo; hi} = (lo = neg_infinity && hi = infinity)
                          
let is_valid ({lo; hi} as v) =
  (lo <= hi && lo < infinity && neg_infinity < hi) || is_empty v

let is_nan_i {lo; hi} = lo <> lo || hi <> hi

let is_point {lo; hi} = (lo = hi && lo < infinity && neg_infinity < hi)
                                                                        
let contains {lo; hi} x = lo <= x && x <= hi
                                  
let mk_i a b = {lo = a; hi = b}
      
let mk_const_i x = {lo = x; hi = x}

let abs_i ({lo; hi} as v) =
  if is_empty v then empty_interval
  else
    let a = abs_float lo and
        b = abs_float hi in
    if 0.0 <= lo || hi <= 0.0 then
      {lo = float_min_nan [a; b]; hi = float_max_nan [a; b]}
    else
      {lo = 0.0; hi = float_max_nan [a; b]}

let neg_i ({lo; hi} as v) =
  if is_empty v then empty_interval else {lo = -.hi; hi = -.lo}
  
let add_ii ({lo = a; hi = b} as v) ({lo = c; hi = d} as w) =
  if is_empty v || is_empty w then empty_interval
  else
    {lo = fadd_lo a c; hi = fadd_hi b d}

let sub_ii ({lo = a; hi = b} as v) ({lo = c; hi = d} as w) =
  if is_empty v || is_empty w then empty_interval
  else
    {lo = fsub_lo a d; hi = fsub_hi b c}

let mul_ii ({lo = a; hi = b} as v) ({lo = c; hi = d} as w) =
  if is_empty v || is_empty w then empty_interval
  else {
      lo = float_min_nan [fmul_lo a c; fmul_lo a d; fmul_lo b c; fmul_lo b d];
      hi = float_max_nan [fmul_hi a c; fmul_hi a d; fmul_hi b c; fmul_hi b d]
    }

let div_ii ({lo = a; hi = b} as v) ({lo = c; hi = d} as w) =
  if is_empty v || is_empty w || (c = 0.0 && d = 0.0) then empty_interval
  else if contains w 0.0 then begin
      if a = 0.0 && b = 0.0 then zero_interval
      else if c = 0.0 then {
          lo = if a >= 0.0 then fdiv_lo a d else neg_infinity;
          hi = if b <= 0.0 then fdiv_hi b d else infinity
        }
      else if d = 0.0 then {
          lo = if b <= 0.0 then fdiv_lo b c else neg_infinity;
          hi = if a >= 0.0 then fdiv_hi a c else infinity
        }
      else entire_interval
    end
  else {
      lo = float_min [fdiv_lo a c; fdiv_lo a d; fdiv_lo b c; fdiv_lo b d];
      hi = float_max [fdiv_hi a c; fdiv_hi a d; fdiv_hi b c; fdiv_hi b d]
    }

let x = mk_i neg_infinity infinity and
    y = mk_i neg_infinity (-.max_float)
         
let a = x.lo and b = x.hi and
    c = y.lo and d = y.hi

let t1 = [fdiv_lo a c; fdiv_lo a d; fdiv_lo b c; fdiv_lo b d]
let t2 = [fdiv_hi a c; fdiv_hi a d; fdiv_hi b c; fdiv_hi b d]

                       
let add_di x w = add_ii (mk_const_i x) w

let add_id v y = add_ii v (mk_const_i y)

let sub_di x w = sub_ii (mk_const_i x) w

let sub_id v y = sub_ii v (mk_const_i y)

let mul_di x w = mul_ii (mk_const_i x) w

let mul_id v y = mul_ii v (mk_const_i y)

let div_di x w = div_ii (mk_const_i x) w

let div_id v y = div_ii v (mk_const_i y)

let inv_i v = div_ii one_interval v

let sqrt_i ({lo = a; hi = b} as v) =
  if is_empty v || b < 0.0 then empty_interval
  else {
      lo = if a < 0.0 then 0.0 else fsqrt_lo a;
      hi = fsqrt_hi b
    }

let pown_i ({lo = a; hi = b} as v) n =
  if is_empty v || (n < 0 && a = 0.0 && b = 0.0) then empty_interval
  else
    match n with
    | 0 -> one_interval
    | 1 -> v
    | n when n land 1 = 1 -> begin
        (* odd n *)
        if n > 0 then {lo = fpown_lo a n; hi = fpown_hi b n}
        else if a >= 0.0 then {
            lo = fpown_lo b n;
            hi = if a = 0.0 then infinity else fpown_hi a n
          }
        else if b <= 0.0 then {
            lo = if b = 0.0 then neg_infinity else fpown_lo b n;
            hi = fpown_hi a n
          }
        else entire_interval
      end
    | _ -> begin
        (* even n *)
        if n > 0 then begin
            if a >= 0.0 then {lo = fpown_lo a n; hi = fpown_hi b n}
            else if b <= 0.0 then {lo = fpown_lo b n; hi = fpown_hi a n}
            else {lo = 0.0; hi = fpown_hi (float_max_nan [abs_float a; abs_float b]) n}
          end
        else if a >= 0.0 then {
            lo = fpown_lo b n;
            hi = if a = 0.0 then infinity else fpown_hi a n
          }
        else if b <= 0.0 then {
            lo = fpown_lo a n;
            hi = if b = 0.0 then infinity else fpown_hi b n
          }
        else {
            lo = fpown_lo (float_max_nan [abs_float a; abs_float b]) n;
            hi = infinity
          }
      end
