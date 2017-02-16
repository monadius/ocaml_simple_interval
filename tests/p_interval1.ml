open Test
open Interval1

let samples = 1000000
let repeats = 10

let uncurry f (a, b) = f a b

let uncurry_and_swap f (a, b) = f b a

let interval_of_pair (a, b) =
  if is_nan a || is_nan b || (a = infinity && b = neg_infinity)
     || (a = infinity && b = infinity) || (a = neg_infinity && b = neg_infinity) then
    empty_interval
  else if a <= b then
    make_interval a b
  else
    make_interval b a
                         
let data_f = array_of_stream (performance_data_f ~n:samples ~sign:0)

let data_f_pos = array_of_stream (performance_data_f ~n:samples ~sign:1)

let data_f2 = array_of_stream (performance_data_f2 ~n:samples ~sign:0)

let data_i = Array.map interval_of_pair data_f2

let data_if = Array.init (Array.length data_i)
                         (fun i -> data_i.(i), data_f.(i))

let data_i_pos = Array.map abs_i data_i

let data_i2 =
  let p (p1, p2) = interval_of_pair p1, interval_of_pair p2 in
  let s = performance_data_f2f2 ~n:samples ~sign:0 in
  array_of_stream (stream_map p s)

let run_f ?base_mean name f =
  run_performance_test ~repeats ?base_mean ~name f data_f

let run_f_pos ?base_mean name f =
  run_performance_test ~repeats ?base_mean ~name f data_f_pos

let run_ff ?base_mean name f =
  run_performance_test ~repeats ?base_mean ~name (uncurry f) data_f2

let run_i ?base_mean name f =
  run_performance_test ~repeats ?base_mean ~name f data_i

let run_i_pos ?base_mean name f =
  run_performance_test ~repeats ?base_mean ~name f data_i_pos

let run_if ?base_mean name f =
  run_performance_test ~repeats ?base_mean ~name (uncurry f) data_if

let run_fi ?base_mean name f =
  run_performance_test ~repeats ?base_mean ~name (uncurry_and_swap f) data_if

let run_ii ?base_mean name f =
  run_performance_test ~repeats ?base_mean ~name (uncurry f) data_i2

let test_add_ii {low = a; high = b} {low = c; high = d} = {
    low = a +. c;
    high = b +. d;
  }

let test_sub_ii {low = a; high = b} {low = c; high = d} = {
    low = a -. d;
    high = b -. c;
  }

let test_mul_ii {low = a; high = b} {low = c; high = d} = {
    low = a *. c;
    high = b *. d;
  }

let test_div_ii {low = a; high = b} {low = c; high = d} = {
    low = a /. d;
    high = b /. c;
  }

let test_inv_i {low = a; high = b} = {
    low = 1. /. a;
    high = 1. /. b;
  }

let test_sqr_i {low = a; high = b} = {
    low = a *. a;
    high = b *. b;
  }

let test_sqrt_i {low = a; high = b} = {
    low = sqrt a;
    high = sqrt b;
  }

let test_exp_i {low = a; high = b} = {
    low = exp a;
    high = exp b;
  }

let test_log_i {low = a; high = b} = {
    low = log a;
    high = log b;
  }

let test_pow_i {low = a; high = b} x = {
    low = a ** x;
    high = b ** x;
  }

(* Tests for floating-point functions *)                                       
let () =
  Gc.compact ();
  print_performance_header ();
  let base_mean, _ = run_f "empty" (fun a -> 0) in
  ignore @@ run_ff "empty2" (fun a b -> 0);
  ignore @@ run_f "fsucc" ~base_mean fsucc;
  ignore @@ run_f "fpred" ~base_mean fpred;
  let base_mean, _ = run_ff "+." ( +. ) in
  ignore @@ run_ff "fadd_low" ~base_mean fadd_low;
  ignore @@ run_ff "fadd_high" ~base_mean fadd_high;
  let base_mean, _ = run_ff "-." ( -. ) in
  ignore @@ run_ff "fsub_low" ~base_mean fsub_low;
  ignore @@ run_ff "fsub_high" ~base_mean fsub_high;
  let base_mean, _ = run_ff "*." ( *. ) in
  ignore @@ run_ff "fmul_low" ~base_mean fmul_low;
  ignore @@ run_ff "fmul_high" ~base_mean fmul_high;
  let base_mean, _ = run_ff "/." ( /. ) in
  ignore @@ run_ff "fdiv_low" ~base_mean  fdiv_low;
  ignore @@ run_ff "fdiv_high" ~base_mean fdiv_high;
  let base_mean, _ = run_f "sqrt" sqrt in
  ignore @@ run_f_pos "fsqrt_low" ~base_mean fsqrt_low;
  ignore @@ run_f_pos "fsqrt_high" ~base_mean fsqrt_high;
  let base_mean, _ = run_f "exp" exp in
  ignore @@ run_f "fexp_low" ~base_mean fexp_low;
  ignore @@ run_f "fexp_high" ~base_mean fexp_high;
  let base_mean, _ = run_f "x^2" (fun x -> x ** 2.) in
  ignore @@ run_f "fpown_low(2)" ~base_mean (fun x -> fpown_low x 2);
  ignore @@ run_f "fpown_high(2)" ~base_mean (fun x -> fpown_high x 2);
  let base_mean, _ = run_f "x^3" (fun x -> x ** 3.) in
  ignore @@ run_f "fpown_low(3)" ~base_mean (fun x -> fpown_low x 3);
  ignore @@ run_f "fpown_high(3)" ~base_mean (fun x -> fpown_high x 3);
  let base_mean, _ = run_f "x^(-2)" (fun x -> x ** (-2.)) in
  ignore @@ run_f "fpown_low(-2)" ~base_mean (fun x -> fpown_low x (-2));
  ignore @@ run_f "fpown_high(-2)" ~base_mean (fun x -> fpown_high x (-2));
  let base_mean, _ = run_f "x^(-3)" (fun x -> x ** (-3.)) in
  ignore @@ run_f "fpown_low(-3)" ~base_mean (fun x -> fpown_low x (-3));
  ignore @@ run_f "fpown_high(-3)" ~base_mean (fun x -> fpown_high x (-3))


(* Tests for interval functions *)  
let () =
  Gc.compact ();
  Printf.printf "\n";
  print_performance_header ();
  let base_mean, _ = run_i "empty" (fun a -> 0) in
  ignore @@ run_i "mid_i_fast" ~base_mean mid_i_fast;
  ignore @@ run_i "mid_i" ~base_mean mid_i;
  ignore @@ run_i "neg_i" ~base_mean neg_i;
  ignore @@ run_i "abs_i" ~base_mean abs_i;
  let base_mean, _ = run_ii "*test*: add_ii" test_add_ii in
  ignore @@ run_ii "add_ii" ~base_mean add_ii;
  ignore @@ run_if "add_id" ~base_mean add_id;
  ignore @@ run_fi "add_di" ~base_mean add_di;
  let base_mean, _ = run_ii "*test*: sub_ii" test_sub_ii in
  ignore @@ run_ii "sub_ii" ~base_mean sub_ii;
  ignore @@ run_if "sub_id" ~base_mean sub_id;
  ignore @@ run_fi "sub_di" ~base_mean sub_di;
  let base_mean, _ = run_ii "*test*: mul_ii" test_mul_ii in
  ignore @@ run_ii "mul_ii" ~base_mean mul_ii;
  ignore @@ run_if "mul_id" ~base_mean mul_id;
  ignore @@ run_fi "mul_di" ~base_mean mul_di;
  let base_mean, _ = run_ii "*test*: div_ii" test_div_ii in
  ignore @@ run_ii "div_ii" ~base_mean div_ii;
  ignore @@ run_if "div_id" ~base_mean div_id;
  ignore @@ run_fi "div_di" ~base_mean div_di;
  let base_mean, _ = run_i "*test*: inv_i" test_inv_i in
  ignore @@ run_i "inv_i" ~base_mean inv_i;
  let base_mean, _ = run_i "*test*: sqr_i" test_sqr_i in
  ignore @@ run_i "sqr_i" ~base_mean sqr_i;
  let base_mean, _ = run_i_pos "*test*: sqrt_i" test_sqrt_i in
  ignore @@ run_i_pos "sqrt_i" ~base_mean sqrt_i;
  let base_mean, _ = run_i "*test*: exp_i" test_exp_i in
  ignore @@ run_i "exp_i" ~base_mean exp_i;
  let base_mean, _ = run_i_pos "*test*: log_i" test_log_i in
  ignore @@ run_i_pos "log_i" ~base_mean log_i;
  let base_mean, _ = run_i "*test*: x^2" (fun v -> test_pow_i v 2.) in
  ignore @@ run_i "pown_i(2)" ~base_mean (fun v -> pown_i v 2);
  let base_mean, _ = run_i "*test*: x^3" (fun v -> test_pow_i v 3.) in
  ignore @@ run_i "pown_i(3)" ~base_mean (fun v -> pown_i v 3);
  let base_mean, _ = run_i "*test*: x^(-2)" (fun v -> test_pow_i v (-2.)) in
  ignore @@ run_i "pown_i(-2)" ~base_mean (fun v -> pown_i v (-2));
  let base_mean, _ = run_i "*test*: x^(-3)" (fun v -> test_pow_i v (-3.)) in
  ignore @@ run_i "pown_i(-3)" ~base_mean (fun v -> pown_i v (-3))
                   
                   
