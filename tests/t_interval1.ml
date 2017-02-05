open Num
open Test
open Interval1

module T = Test_interval
       
(* let _ = Random.init 0 *)

let samples = 1000

let intervals_of_pair (a, b) =
  if a <= b then
    {low = a; high = b}, T.mk_i a b
  else
    {low = b; high = a}, T.mk_i b a

let eq_intervals v tv =
  compare v.low tv.T.lo = 0 && compare v.high tv.T.hi = 0

let subset v tv =
  v.low <= tv.T.lo && tv.T.hi <= v.high

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
                    
let () =
  (* Tests with special values *)
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
           ];
  
  (* Tests with special data *)
  run_test (test_f "fsucc (special)" test_fsucc)
           (special_data_f ());
  
  (* Tests with randomly generated data *)
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
                    
let () =
  (* Tests with special values *)
  run_eq_f "fpred (eq)" fpred [
             -.0.0, -.eta_float;
             0.0, -.eta_float;
             min_float, min_float -. 2.0 *. eta_float;
             min_float +. eta_float, min_float -. eta_float;
             -.min_float, -.(min_float +. 2.0 *. eta_float);
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
  run_test (test_f "fpred (special)" test_fpred)
           (special_data_f ());
  
  (* Tests with randomly generated data *)
  run_test (test_f "fpred" test_fpred)
           (standard_data_f ~n:samples ~sign:0)

(* add tests *)

let test_add ((a, b) as p1) ((c, d) as p2) =
  let v, tv = intervals_of_pair p1 and
      w, tw = intervals_of_pair p2 in
  let r = add_ii v w and
      tr = T.add_ii tv tw in
  if T.is_valid_i tv && T.is_valid_i tw then begin
      fact ("valid", r.low <= r.high);
      fact ("subset", subset r tr);
    end
  else begin
      fact ("not valid", not (r.low <= r.high));
    end;
  true

let () =
  run_test (test_f2f2 "add (special)" test_add)
           (special_data_f2f2 ());
  run_test (test_f2f2 "add" test_add)
           (standard_data_f2f2 ~n:samples ~sign:0)
  
  
  

