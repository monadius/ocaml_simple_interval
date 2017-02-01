let _ = Random.init 0

let rnd_float sign exp =
  let neg_flag = if sign = 0 then Random.bool() else (sign < 0) in
  let x = 1.0 +. Random.float (1.0 -. epsilon_float) in
  let x = if neg_flag then -.x else x in
  ldexp x exp

(* Returns an n-element stream of random floating-point numbers
   with exponents in the range [e_min, e_max] *)
let rand_floats ~n ~sign e_min e_max =
  assert (e_max >= e_min);
  let d = e_max - e_min + 1 in
  let next i =
    if i >= n then None
    else
      let e = e_min + Random.int d in
      Some (rnd_float sign e) in
  Stream.from next

(* Returns a stream of random floating-point numbers
   where first n elements have the exponent e_min and the
   last n elements have the exponent e_max *)
let rand_floats_all ~n ~sign e_min e_max =
  assert (e_max >= e_min);
  let e = ref e_min in
  let k = ref 0 in
  let next i =
    if !k >= n then begin
        incr e;
        k := 0
      end;
    incr k;
    if !e > e_max then None
    else Some (rnd_float sign !e) in
  Stream.from next

(* Returns a stream of floating-point numbers in the form
   +/-2^e with e in [e_min, e_max] *)
let p2_floats e_min e_max =
  assert (e_max >= e_min);
  let e = ref e_min in
  let next i =
    if !e > e_max then None
    else begin
        let exp = !e in
        let m = if i land 1 = 0 then 1.0 else (incr e; -1.0) in
        Some (ldexp m exp)
      end in
  Stream.from next

let special_floats = [
    nan;
    neg_infinity;
    infinity;
    0.0;
    -.0.0;
    max_float;
    -.max_float;
    min_float;
    -.min_float;
    1.0;
    -.1.0;
    1.0 +. epsilon_float;
    -.(1.0 +. epsilon_float);
    ldexp 1.0 (-1074);
    -.(ldexp 1.0 (-1074));
    ldexp 1.0 (-1073);
    -.(ldexp 1.0 (-1073));
  ]

let stream_map f stream =
  let next i =
    try Some (f (Stream.next stream))
    with Stream.Failure -> None in
  Stream.from next
        
let test_float_num =
  let test x =
    let n = num_of_float x in
    let n1 = n +/ Int 1 and
        n2 = n -/ Int 1 in
    let a = float_of_num_lo n and
        b = float_of_num_hi n and
        a1 = float_of_num_lo n1 and
        b1 = float_of_num_hi n1 and
        a2 = float_of_num_lo n2 and
        b2 = float_of_num_hi n2 in
    if x = a && x = b && x <= a1 && x < b1 && x > a2 && x >= b2 then ()
    else Printf.printf "FAIL: x = %e\n" x
  in
  let rec all_tests n =
    if n >= -1074 then
      let x = rnd_float 1 n and
          y = rnd_float (-1) n and
          z = rnd_float 0 n in
      let _ = test x;
              test y;
              test z in
      all_tests (n - 1)
    else
      ()
  in
  all_tests

let is_nan x = (compare x nan = 0)

(* Tests next_float for all arguments *)
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
         if x < max_float then assert (x +. d *. 0.4 = x);
    end;
  true

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
         if x > -.max_float then assert (x -. d *. 0.4 = x);
    end;
  true

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


type 'a test = {
    test_name: 'a -> string;
    test_func: 'a -> bool;
  }
                 
let mk_test ~name f = {
    test_name = name;
    test_func = f
  }
                        
let run_test (test: 'a test) (data: 'a Stream.t) =
  let run x =
    try
      let result = test.test_func x in
      assert result
    with _ ->
      let msg = test.test_name x in
      Printf.printf "\rFAIL: %s\n" msg
  in
  Stream.iter run data

let name_f name x =
  Printf.sprintf "%s: %.20e" name x

let name_f2 name (a, b) =
  Printf.sprintf "%s: [%.20e, %.20e]" name a b

let name_f2f2 name ((a, b), (c, d)) =
  Printf.sprintf "%s: [%.20e, %.20e] [%.20e, %.20e]" name a b c d

let name_f2f name ((a, b), c) =
  Printf.sprintf "%s: [%.20e, %.20e] %.20e" name a b c

let name_ff2 name (a, (b, c)) =
  Printf.sprintf "%s: %.20e [%.20e, %.20e]" name a b c

let test_f name f = mk_test (name_f name) f

let test_f2 name f = mk_test (name_f2 name) f

let test_f2f2 name f =
  mk_test (name_f2f2 name) (fun (p1, p2) -> f p1 p2)

let test_f2f name f =
  mk_test (name_f2f name) (fun (p, x) -> f p x)

let test_ff2 name f =
  mk_test (name_ff2 name) (fun (x, p) -> f x p)

let mk_eq_test name_f f =
  mk_test (fun (arg, _) -> name_f arg)
          (fun (arg, result) -> compare (f arg) result = 0)

let run_eq_f name f data =
  let test = mk_eq_test (name_f name) f in
  let sd = Stream.of_list data in
  run_test test sd

let run_eq_f2 name f data =
  let test = mk_eq_test (name_f2 name) f in
  let sd = Stream.of_list data in
  run_test test (stream_map (fun (a, b, r) -> (a, b), r) sd)

let run_eq_f2f2 name f data =
  let test = mk_eq_test (name_f2f2 name) (fun (p1, p2) -> f p1 p2) in
  let sd = Stream.of_list data in
  run_test test (stream_map (fun (a, b, c, d, r) -> ((a, b), (c, d)), r) sd)

let run_eq_f2f name f data =
  let test = mk_eq_test (name_f2f name) (fun (p, x) -> f p x) in
  let sd = Stream.of_list data in
  run_test test (stream_map (fun (a, b, c, r) -> ((a, b), c), r) sd)

let run_eq_ff2 name f data =
  let test = mk_eq_test (name_ff2 name) (fun (x, p) -> f x p) in
  let sd = Stream.of_list data in
  run_test test (stream_map (fun (a, b, c, r) -> (a, (b, c)), r) sd)

let _ =
  run_test (mk_test_f "num_float" test_num_float)
           (Stream.of_list special_floats)
              
let _ =
  run_test (mk_test_f "num_float" test_num_float)
           (rand_floats ~n:1000 ~sign:0 (-50) 50)


let _ =
  run_eq_f2f "eq" (fun (a, b) x -> x +. a +. b)
           [
             1.0, 1.0, 1.0, 2.0;
           ]
             
let _ =
  let eta_float = ldexp 1.0 (-1074) in
  run_eq_f "eq_next_float" next_float [
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
           ]

let _ =
  let eta_float = ldexp 1.0 (-1074) in
  run_eq_f "eq_prev_float" prev_float [
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
           ]
