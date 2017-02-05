open Num
open Test
open Test_interval

let _ = Random.init 0

let samples = 1000

(* next_float tests *)

let test_next_float x =
  let y = next_float x in
  ignore begin
      match classify_float x with
      | FP_nan ->
         assert (is_nan y)
      | FP_infinite ->
         if x = neg_infinity then
           assert (is_nan y)
         else
           assert (y = infinity)
      | FP_zero | FP_normal | FP_subnormal ->
         let d = y -. x in
         assert (y > x);
         assert (d > 0.0);
         assert (x +. d = y);
         if x < max_float then assert (x +. d *. 0.25 = x);
    end;
  true
                    
let () =
  let eta_float = ldexp 1.0 (-1074) in
  (* Tests with special values *)
  run_eq_f "next_float (eq)" next_float [
             -.0.0,                       eta_float;
             0.0,                         eta_float;
             min_float,                   min_float +. eta_float;
             min_float -. eta_float,      min_float;
             -.min_float,                 -.(min_float -. eta_float);
             eta_float,                   2.0 *. eta_float;
             -.eta_float,                 0.0;
             1.0,                         1.0 +. epsilon_float;
             1.0 -. epsilon_float *. 0.5, 1.0;
             -1.0,                        -.(1.0 -. epsilon_float *. 0.5);
             max_float,                   infinity;
             infinity,                    infinity;
             nan,                         nan;
             neg_infinity,                nan;
           ];
  
  (* Tests with special data *)
  run_test (test_f "next_float (special)" test_next_float)
           (special_data_f ());
  
  (* Tests with randomly generated data *)
  run_test (test_f "next_float" test_next_float)
           (standard_data_f ~n:samples ~sign:0)

(* prev_float tests *)

let test_prev_float x =
  let y = prev_float x in
  ignore begin
      match classify_float x with
      | FP_nan ->
         assert (is_nan y)
      | FP_infinite ->
         if x = neg_infinity then
           assert (y = neg_infinity)
         else
           assert (is_nan y)
      | FP_zero | FP_normal | FP_subnormal ->
         let d = x -. y in
         assert (y < x);
         assert (d > 0.0);
         assert (x -. d = y);
         if x > -.max_float then assert (x -. d *. 0.25 = x);
    end;
  true

let () =
  let eta_float = ldexp 1.0 (-1074) in
  (* Tests with special values *)
  run_eq_f "prev_float (eq)" prev_float [
             -.0.0, -.eta_float;
             0.0, -.eta_float;
             min_float, min_float -. eta_float;
             min_float +. eta_float, min_float;
             -.min_float, -.(min_float +. eta_float);
             eta_float, 0.0;
             -.eta_float, -2.0 *. eta_float;
             1.0, 1.0 -. 0.5 *. epsilon_float;
             1.0 -. epsilon_float *. 0.5, 1.0 -. epsilon_float;
             -1.0, -.(1.0 +. epsilon_float);
             -.max_float, neg_infinity;
             infinity, nan;
             nan, nan;
             neg_infinity, neg_infinity;
           ];

  (* Tests with special data *)
  run_test (test_f "prev_float (special)" test_prev_float)
           (special_data_f ());

  (* Tests with randomly generated data *)
  run_test (test_f "prev_float" test_prev_float)
           (standard_data_f ~n:samples ~sign:0)

(* num_of_float and float_of_num_lo(hi) tests *)

let test_num_float x =
  let r = num_of_float x in
  let r1 = Num.pred_num r and
      r2 = Num.succ_num r in
  let a = float_of_num_lo r and
      b = float_of_num_hi r and
      a1 = float_of_num_lo r1 and
      b1 = float_of_num_hi r1 and
      a2 = float_of_num_lo r2 and
      b2 = float_of_num_hi r2 in
  ignore begin
      assert (a = x && b = x);
      assert (a1 < x && b1 <= x);
      assert (a2 >= x && b2 > x);
      if b1 = x then assert (a1 = prev_float x);
      if a2 = x then assert (b2 = next_float x);
    end;
  true

let () =
  let eta_float = ldexp 1.0 (-1074) in
  (* Tests with special values *)
  run_eq_f "num_of_float (eq)" ~cmp:compare_num num_of_float [
             -.0.0, Int 0;
             0.0, Int 0;
             eta_float, Int 2 **/ Int (-1074);
             -2.0 *. eta_float, Int (-2) **/ Int (-1073);
             1.0, Int 1;
             -1.5, Int (-3) // Int 2;
           ];

  (* Tests with randomly generated data *)
  run_test (test_f "test_num_float" test_num_float)
           (standard_data_f ~n:samples ~sign:0)
