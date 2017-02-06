open Num
open Test
open Interval1

module T = Test_interval
       
(* let () = Random.self_init () *)
let samples = 100

let intervals_of_pair (a, b) =
  if a <= b then
    {low = a; high = b}, T.mk_i a b
  else
    {low = b; high = a}, T.mk_i b a

let test_eq_intervals v tv =
  compare v.low tv.T.lo = 0 && compare v.high tv.T.hi = 0

let test_subset v tv =
  v.low <= tv.T.lo && tv.T.hi <= v.high

let test_subset_1ulp tv v =
  let a = T.prev_float tv.T.lo and
      b = T.next_float tv.T.hi in
  a <= v.low && v.high <= b
                                   
let test_subset_2ulp tv v =
  let a = T.prev_float (T.prev_float tv.T.lo) and
      b = T.next_float (T.next_float tv.T.hi) in
  a <= v.low && v.high <= b

let cmp_intervals v w =
  let a = compare v.low w.low in
  if a = 0 then compare v.high w.high
  else a

let is_pos v = v.low >= 0.0

let is_neg v = v.high <= 0.0

(* fsucc tests *)

let in_special_range =
  let lo = ldexp 1.0 (-1022) and
      hi = ldexp 1.0 (-1020) in
  fun x -> let t = abs_float x in
           lo <= t && t <= hi
                                   
let test_fsucc x =
  let y = fsucc x in
  let z = T.next_float x in
  if in_special_range x then
    fact ("special_range", z <= y && y <= T.next_float z)
  else
    fact ("eq", compare y z = 0);
  true
                    
(* Tests with special values *)
let () =
  run_eq_f "fsucc (eq)" fsucc [
             -.0.0,                       eta_float;
             0.0,                         eta_float;
             min_float,                   min_float +. 2.0 *. eta_float;
             min_float -. eta_float,      min_float;
             -.min_float,                 -.(min_float -. 2.0 *. eta_float);
             eta_float,                   2.0 *. eta_float;
             -.eta_float,                 0.0;
             1.0,                         1.0 +. epsilon_float;
             1.0 -. epsilon_float *. 0.5, 1.0;
             -1.0,                        -.(1.0 -. epsilon_float *. 0.5);
             max_float,                   infinity;
             infinity,                    infinity;
             nan,                         nan;
             neg_infinity,                nan;
           ]

(* Other tests *)
let () =
  run_test (test_f "fsucc (special)" test_fsucc)
           (special_data_f ());
  run_test (test_f "fsucc" test_fsucc)
           (standard_data_f ~n:samples ~sign:0)

(* fpred tests *)
                                   
let test_fpred x =
  let y = fpred x in
  let z = T.prev_float x in
  if in_special_range x then
    fact ("special_range", T.prev_float z <= y && y <= z)
  else
    fact ("eq", compare y z = 0);
  true
                    
(* Tests with special values *)
let () =
  run_eq_f "fpred (eq)" fpred [
             -.0.0,                       -.eta_float;
             0.0,                         -.eta_float;
             min_float,                   min_float -. 2.0 *. eta_float;
             min_float +. eta_float,      min_float -. eta_float;
             -.min_float,                 -.(min_float +. 2.0 *. eta_float);
             eta_float,                   0.0;
             -.eta_float,                 -2.0 *. eta_float;
             1.0,                         1.0 -. 0.5 *. epsilon_float;
             1.0 -. epsilon_float *. 0.5, 1.0 -. epsilon_float;
             -1.0,                        -.(1.0 +. epsilon_float);
             -.max_float,                 neg_infinity;
             infinity,                    nan;
             nan,                         nan;
             neg_infinity,                neg_infinity;
           ]

(* Other tests *)
let () =
  run_test (test_f "fpred (special)" test_fpred)
           (special_data_f ());
  run_test (test_f "fpred" test_fpred)
           (standard_data_f ~n:samples ~sign:0)

(* neg tests *)

let test_neg_i ((a, b) as p) =
  let v, tv = intervals_of_pair p in
  let r = neg_i v and
      tr = T.neg_i tv in
  fact ("eq", test_eq_intervals r tr);
  true
    
let () =
  let f = test_neg_i in
  run_test (test_f2 "neg_i (special)" f)
           (special_data_f2 ());
  run_test (test_f2 "neg_i" f)
           (standard_data_f2 ~n:samples ~sign:0)

(* abs tests *)

let test_abs_i ((a, b) as p) =
  let v, tv = intervals_of_pair p in
  let r = abs_i v and
      tr = T.abs_i tv in
  if T.is_nan_i tv then begin
      fact ("nan", is_nan r.low || is_nan r.high);
    end
  else begin
      fact ("eq", test_eq_intervals r tr);
    end;
  true

let () =
  let f = test_abs_i in
  run_test (test_f2 "abs_i (special)" f)
           (special_data_f2 ());
  run_test (test_f2 "abs_i" f)
           (standard_data_f2 ~n:samples ~sign:0)

(* add tests *)

let test_add_ii ((a, b) as p1) ((c, d) as p2) =
  let v, tv = intervals_of_pair p1 and
      w, tw = intervals_of_pair p2 in
  let r = add_ii v w and
      tr = T.add_ii tv tw in
  if T.is_nan_i tv || T.is_nan_i tw then begin
      fact ("nan", is_nan r.low || is_nan r.high)
    end
  else if T.is_valid_i tv && T.is_valid_i tw then begin
      fact ("valid", r.low <= r.high);
      fact ("subset", test_subset r tr);
      fact ("2ulp", test_subset_2ulp tr r);
      if is_pos v && is_pos w then fact ("pos", is_pos r);
      if is_neg v && is_neg w then fact ("neg", is_neg r);
    end;
  true

let () =
  let f = fun (a, b) (c, d) -> add_ii (make_interval a b) (make_interval c d) in
  run_eq_f2f2 "add_ii (eq)" ~cmp:cmp_intervals f [
                (0., 0.), (0., 0.), {low = 0.; high = 0.};
              ]
    
let () =
  let f = test_add_ii in
  run_test (test_f2f2 "add_ii (special)" f)
           (special_data_f2f2 ());
  run_test (test_f2f2 "add_ii" f)
           (standard_data_f2f2 ~n:samples ~sign:0)

(* sub tests *)

let test_sub_ii ((a, b) as p1) ((c, d) as p2) =
  let v, tv = intervals_of_pair p1 and
      w, tw = intervals_of_pair p2 in
  let r = sub_ii v w and
      tr = T.sub_ii tv tw in
  if T.is_nan_i tv || T.is_nan_i tw then begin
      fact ("nan", is_nan r.low || is_nan r.high)
    end
  else if T.is_valid_i tv && T.is_valid_i tw then begin
      fact ("valid", r.low <= r.high);
      fact ("subset", test_subset r tr);
      fact ("2ulp", test_subset_2ulp tr r);
      if is_pos v && is_neg w then fact ("pos", is_pos r);
      if is_neg v && is_pos w then fact ("neg", is_neg r);
    end;
  true

let () =
  let f = fun (a, b) (c, d) -> sub_ii (make_interval a b) (make_interval c d) in
  run_eq_f2f2 "sub_ii (eq)" ~cmp:cmp_intervals f [
                (0., 0.), (0., 0.), {low = 0.; high = 0.};
              ]
    
let () =
  let f = test_sub_ii in
  run_test (test_f2f2 "sub_ii (special)" f)
           (special_data_f2f2 ());
  run_test (test_f2f2 "sub_ii" f)
           (standard_data_f2f2 ~n:samples ~sign:0)

(* mul tests *)

let test_mul_ii ((a, b) as p1) ((c, d) as p2) =
  let v, tv = intervals_of_pair p1 and
      w, tw = intervals_of_pair p2 in
  let r = mul_ii v w and
      tr = T.mul_ii tv tw in
  if T.is_nan_i tv || T.is_nan_i tw then begin
      fact ("nan", is_nan r.low || is_nan r.high)
    end
  else if T.is_valid_i tv && T.is_valid_i tw then begin
      fact ("valid", r.low <= r.high);
      fact ("subset", test_subset r tr);
      fact ("2ulp", test_subset_2ulp tr r);
      if (is_pos v && is_pos w) || (is_neg v && is_neg w) then
        fact ("pos", is_pos r);
      if (is_pos v && is_neg w) || (is_neg v && is_pos w) then
        fact ("neg", is_neg r);
    end;
  true

let () =
  let f = fun (a, b) (c, d) -> mul_ii (make_interval a b) (make_interval c d) in
  run_eq_f2f2 "mul_ii (eq)" ~cmp:cmp_intervals f [
                (0., 0.), (0., 0.), {low = 0.; high = 0.};
              ]
    
let x () =
  let f = test_mul_ii in
  run_test (test_f2f2 "mul_ii (special)" f)
           (special_data_f2f2 ());
  run_test (test_f2f2 "mul_ii" f)
           (standard_data_f2f2 ~n:samples ~sign:0)

  
