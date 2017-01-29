open Num

(* Auxiliary functions *)

let next_float x =
  match classify_float x with
  | FP_nan -> nan
  | FP_infinite ->
     if x = infinity then x else nan
  | FP_zero -> ldexp 1.0 (-1074)
  | _ ->
     let bits = Int64.bits_of_float x in
     if x < 0.0 then
       Int64.float_of_bits (Int64.pred bits)
     else
       Int64.float_of_bits (Int64.succ bits)

let prev_float x =
  match classify_float x with
  | FP_nan -> nan
  | FP_infinite ->
     if x = neg_infinity then x else nan
  | FP_zero -> ldexp (-1.0) (-1074)
  | _ ->
     let bits = Int64.bits_of_float x in
     if x < 0.0 then
       Int64.float_of_bits (Int64.succ bits)
     else
       Int64.float_of_bits (Int64.pred bits)

let num_of_float x =
  match classify_float x with
  | FP_zero -> Int 0
  | FP_normal | FP_subnormal ->
     let m, e = frexp x in
     let t = Int64.of_float (ldexp m 53) in
     num_of_big_int (Big_int.big_int_of_int64 t) */ (Int 2 **/ Int (e - 53))
  | _ ->
     failwith (Printf.sprintf "num_of_float: %e" x)

let float_of_num_lo r = failwith "Not implemented"

let float_of_num_hi r = failwith "Not implemented"

let rec float_min = function
  | [] -> failwith "float_min: empty list"
  | [x] -> x
  | x :: xs -> if x <> x then nan else min x (float_min xs)

let rec float_max = function
  | [] -> failwith "float_max: empty list"
  | [x] -> x
  | x :: xs -> if x <> x then nan else max x (float_max xs)
                                 
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
  | FP_nan | FP_infinite -> z
  | _ ->
     let rz = num_of_float z in
     if compare_num rz r >= 0 then
       z
     else
       next_float z

let round_lo z r =
  match classify_float z with
  | FP_nan | FP_infinite -> z
  | _ ->
     let rz = num_of_float z in
     if compare_num rz r <= 0 then
       z
     else
       prev_float z
                          
let fadd_lo x y =
  match classify_float x, classify_float y with
  | FP_zero, _ -> y
  | _, FP_zero -> x
  | FP_nan, _ | _, FP_nan -> nan
  | FP_infinite, _ | _, FP_infinite -> x +. y
  | _ -> 
     let r = num_of_float x +/ num_of_float y in
     round_lo (x +. y) r

let fadd_hi x y =
  match classify_float x, classify_float y with
  | FP_zero, _ -> y
  | _, FP_zero -> x
  | FP_nan, _ | _, FP_nan -> nan
  | FP_infinite, _ | _, FP_infinite -> x +. y
  | _ ->
     let r = num_of_float x +/ num_of_float y in
     round_hi (x +. y) r

let fsub_lo x y = fadd_lo x (-.y)

let fsub_hi x y = fadd_hi x (-.y)
                     
let fmul_lo x y =
  match classify_float x, classify_float y with
  | FP_nan, _ | _, FP_nan -> nan
  | FP_zero, _ | _, FP_zero -> 0.0
  | FP_infinite, _ | _, FP_infinite -> x *. y
  | _ -> 
     let r = num_of_float x */ num_of_float y in
     round_lo (x *. y) r

let fmul_hi x y =
  match classify_float x, classify_float y with
  | FP_nan, _ | _, FP_nan -> nan
  | FP_zero, _ | _, FP_zero -> 0.0
  | FP_infinite, _ | _, FP_infinite -> x *. y
  | _ -> 
     let r = num_of_float x */ num_of_float y in
     round_hi (x *. y) r

let fdiv_lo x y =
  match classify_float x, classify_float y with
  | _, FP_zero -> nan
  | FP_nan, _ | _, FP_nan -> nan
  | FP_zero, _ -> 0.0
  | FP_infinite, _ | _, FP_infinite -> x /. y
  | _ -> 
     let r = num_of_float x // num_of_float y in
     round_lo (x /. y) r

let fdiv_hi x y =
  match classify_float x, classify_float y with
  | _, FP_zero -> nan
  | FP_nan, _ | _, FP_nan -> nan
  | FP_zero, _ -> 0.0
  | FP_infinite, _ | _, FP_infinite -> x /. y
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
       if compare_num (rz */ rz) rx > 0 then
         prev_float z
       else
         z

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
       if compare_num (rz */ rz) rx < 0 then
         next_float z
       else
         z
                    

(* Interval type and functions *)

(* [0, +infinity] contains all finite positive numbers, etc. *)

type ti = {
    lo: float;
    hi: float
  }

let is_valid_i {lo; hi} = lo <= hi && lo < infinity && neg_infinity < hi

let is_point_i {lo; hi} = (lo = hi)
                                                                        
let contains_i {lo; hi} x = lo <= x && x <= hi
                                  
let mk_i a b = {lo = a; hi = b}
      
let mk_const_i x = {lo = x; hi = x}

let abs_i {lo; hi} =
  let a = abs_float lo and
      b = abs_float hi in
  if 0.0 <= lo || hi <= 0.0 then
    {lo = min a b; hi = max a b}
  else
    {lo = 0.0; hi = max a b}

let neg_i {lo; hi} = {lo = -.hi; hi = -.lo}
  
let add_ii {lo = a; hi = b} {lo = c; hi = d} =
  {lo = fadd_lo a c; hi = fadd_hi b d}

let sub_ii {lo = a; hi = b} {lo = c; hi = d} =
  {lo = fsub_lo a d; hi = fsub_hi b c}

let mul_ii {lo = a; hi = b} {lo = c; hi = d} = {
    lo = float_min [fmul_lo a c; fmul_lo a d; fmul_lo b c; fmul_lo b d];
    hi = float_max [fmul_hi a c; fmul_hi a d; fmul_hi b c; fmul_hi b d]
  }

let div_ii {lo = a; hi = b} ({lo = c; hi = d} as w) =
  if contains_i w 0.0 then
    {lo = nan; hi = nan}
  else {
      lo = float_min [fdiv_lo a c; fdiv_lo a d; fdiv_lo b c; fdiv_lo b d];
      hi = float_max [fdiv_hi a c; fdiv_hi a d; fdiv_hi b c; fdiv_hi b d]
    }

let add_di x w = add_ii (mk_const_i x) w

let add_id v y = add_ii v (mk_const_i y)

let sub_di x w = sub_ii (mk_const_i x) w

let sub_id v y = sub_ii v (mk_const_i y)

let mul_di x w = mul_ii (mk_const_i x) w

let mul_id v y = mul_ii v (mk_const_i y)

let div_di x w = div_ii (mk_const_i x) w

let div_id v y = div_ii v (mk_const_i y)

let sqrt_i {lo = a; hi = b} =
  {lo = fsqrt_lo a; hi = fsqrt_hi b}
  
