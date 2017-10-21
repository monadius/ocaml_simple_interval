open Test
open Interval2

module T = Test_interval
       
(* let () = Random.self_init () *)
let samples = 
  try int_of_string (Sys.getenv "TEST_SAMPLES")
  with Not_found -> 1000

let () = Format.printf "samples = %d@." samples

let intervals_of_pair =
  let intervals (a, b) =
    if is_nan a || is_nan b || (a = infinity && b = neg_infinity) ||
         (a = infinity && b = infinity) || (a = neg_infinity && b = neg_infinity) then
      empty_interval, T.empty_interval
    else if a <= b then
      {low = a; high = b}, T.mk_i a b
    else
      {low = b; high = a}, T.mk_i b a in
  fun (a, b) ->
  let v, tv = intervals (a, b) in
  assert (T.is_valid tv);
  v, tv

let test_eq_intervals v tv =
  compare v.low tv.T.lo = 0 && compare v.high tv.T.hi = 0

let test_subset v tv =
  if T.is_empty tv then is_empty v
  else
    v.low <= tv.T.lo && tv.T.hi <= v.high

let cmp_intervals v w =
  let a = compare v.low w.low in
  if a = 0 then compare v.high w.high
  else a

let is_pos v = v.low >= 0.0

let is_neg v = v.high <= 0.0


(* fsucc tests *)

let test_fsucc x =
  let y = fsucc x in
  let z = T.next_float x in
  begin
    fact ("eq", compare y z = 0);
  end;
  true
                    
let () =
  run_eq_f "fsucc (eq)" fsucc [
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

let () =
  run_test (test_f "fsucc (special)" test_fsucc)
           (special_data_f ());
  run_test (test_f "fsucc" test_fsucc)
           (standard_data_f ~n:samples ~sign:0)


(* fpred tests *)
                                   
let test_fpred x =
  let y = fpred x in
  let z = T.prev_float x in
  begin
    fact ("eq", compare y z = 0);
  end;
  true
                    
let () =
  run_eq_f "fpred (eq)" fpred [
             -.0.0,                       -.eta_float;
             0.0,                         -.eta_float;
             min_float,                   min_float -. eta_float;
             min_float +. eta_float,      min_float;
             -.min_float,                 -.(min_float +. eta_float);
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

let () =
  run_test (test_f "fpred (special)" test_fpred)
           (special_data_f ());
  run_test (test_f "fpred" test_fpred)
           (standard_data_f ~n:samples ~sign:0)


(* mid tests *)

let test_mid_i ((a, b) as p) =
  let v, tv = intervals_of_pair p in
  let m = mid_i v in
  if is_empty v then fact ("empty", is_nan m)
  else
    begin
      fact ("in", v.low <= m && m <= v.high);
      fact ("finite", neg_infinity < m && m < infinity);
      if v.low = -.v.high then fact ("sym", m = 0.);
    end;
  true

let () =
  let f = fun (a, b) -> mid_i (make_interval a b) in
  run_eq_f2 "mid_i (eq)" f [
              (-0., 0.),                     0.;
              (infinity, neg_infinity),      nan;
              (neg_infinity, infinity),      0.;
              (0., infinity),                max_float;
              (neg_infinity, 0.),            -.max_float;
              (-1., infinity),               max_float;
              (neg_infinity, 2.),            -.max_float;
              (-3., 3.),                     0.;
              (max_float *. 0.5, max_float), max_float *. 0.75;
              (4., 100.),                    52.;
              (-3., 5.),                     1.;
              (0., eta_float),               0.;
              (eta_float, 2. *. eta_float),  2. *. eta_float;
              (eta_float, eta_float),        eta_float;
              (max_float, max_float),        max_float;
            ]

let () =
  let f = test_mid_i in
  run_test (test_f2 "mid_i (special)" f)
           (special_data_f2 ());
  run_test (test_f2 "mid_i" f)
           (standard_data_f2 ~n:samples ~sign:0)


(* neg tests *)

let test_neg_i ((a, b) as p) =
  let v, tv = intervals_of_pair p in
  let r = neg_i v and
      tr = T.neg_i tv in
  begin
    fact ("valid", is_valid r && T.is_valid tr);
    fact ("eq", test_eq_intervals r tr);
  end;
  true

let () =
  let f = fun (a, b) -> neg_i (make_interval a b) in
  run_eq_f2 "neg_i (eq)" ~cmp:cmp_intervals f [
              (-0., 0.),                make_interval 0. 0.;
              (infinity, neg_infinity), empty_interval;
              (neg_infinity, infinity), entire_interval;
              (1., infinity),           make_interval neg_infinity (-1.);
              (neg_infinity, -3.),      make_interval 3. infinity;
              (-3., 2.),                make_interval (-2.) 3.;
            ]
    
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
  begin
    fact ("valid", is_valid r && T.is_valid tr);
    fact ("eq", test_eq_intervals r tr);
  end;
  true

let () =
  let f = fun (a, b) -> abs_i (make_interval a b) in
  run_eq_f2 "abs_i (eq)" ~cmp:cmp_intervals f [
              (-0., 0.),                zero_interval;
              (infinity, neg_infinity), empty_interval;
              (neg_infinity, infinity), make_interval 0. infinity;
              (1., infinity),           make_interval 1. infinity;
              (neg_infinity, -3.),      make_interval 3. infinity;
              (neg_infinity, 3.),       make_interval 0. infinity;
              (-3., 2.),                make_interval 0. 3.;
              (-3., -2.),               make_interval 2. 3.;
            ]

let () =
  let f = test_abs_i in
  run_test (test_f2 "abs_i (special)" f)
           (special_data_f2 ());
  run_test (test_f2 "abs_i" f)
           (standard_data_f2 ~n:samples ~sign:0)


(* min/max tests *)

let test_min_max_ii ((a, b) as p1) ((c, d) as p2) =
  let v, tv = intervals_of_pair p1 and
      w, tw = intervals_of_pair p2 in
  let r1 = min_ii v w and
      r2 = max_ii v w and
      tr1 = T.min_ii tv tw and
      tr2 = T.max_ii tv tw in
  begin
    fact ("valid", is_valid r1 && is_valid r2 && T.is_valid tr1 && T.is_valid tr2);
    fact ("eq_min", test_eq_intervals r1 tr1);
    fact ("eq_max", test_eq_intervals r2 tr2);
  end;
  true

let () =
  let f = test_min_max_ii in
  run_test (test_f2f2 "min(max)_ii (special)" f)
           (special_data_f2f2 ());
  run_test (test_f2f2 "min(max)_ii" f)
           (standard_data_f2f2 ~n:samples ~sign:0)


(* add tests *)

let test_add_ii ((a, b) as p1) ((c, d) as p2) =
  let v, tv = intervals_of_pair p1 and
      w, tw = intervals_of_pair p2 in
  let r = add_ii v w and
      tr = T.add_ii tv tw in
  begin
    fact ("valid", is_valid r && T.is_valid tr);
    fact ("eq", test_eq_intervals r tr);
    if is_pos v && is_pos w then fact ("pos", is_pos r);
    if is_neg v && is_neg w then fact ("neg", is_neg r);
  end;
  true

let test_add_id_di ((a, b) as p) (c, _) =
  let v, tv = intervals_of_pair p in
  let x = if is_nan c || c = infinity || c = neg_infinity then 0. else c in
  let r = add_id v x and
      r' = add_di x v and
      tr = T.add_id tv x in
  begin
    fact ("id = di", cmp_intervals r r' = 0);
    fact ("valid", is_valid r && T.is_valid tr);
    fact ("eq", test_eq_intervals r tr);
    if is_pos v && x >= 0. then fact ("pos", is_pos r);
    if is_neg v && x <= 0. then fact ("neg", is_neg r);
  end;
  true

let () =
  let f = fun (a, b) (c, d) -> add_ii (make_interval a b) (make_interval c d) in
  run_eq_f2f2 "add_ii (eq)" ~cmp:cmp_intervals f [
                (0., 0.), (0., 0.), zero_interval;
                (infinity, neg_infinity), (1., 2.), empty_interval;
                (-3., -5.), (infinity, neg_infinity), empty_interval;
                (infinity, neg_infinity), (0., infinity), empty_interval;
                (neg_infinity, infinity), (0., 1.), entire_interval;
                (neg_infinity, infinity), (neg_infinity, infinity), entire_interval;
                (3., 5.), (-3., 0.), make_interval 0. 5.;
                (neg_infinity, -1.), (0.1, infinity), entire_interval;
              ]
    
let () =
  let f = test_add_ii in
  run_test (test_f2f2 "add_ii (special)" f)
           (special_data_f2f2 ());
  run_test (test_f2f2 "add_ii" f)
           (standard_data_f2f2 ~n:samples ~sign:0)

let () =
  let f = test_add_id_di in
  run_test (test_f2f2 "add_id(di) (special)" f)
           (special_data_f2f2 ());
  run_test (test_f2f2 "add_id(di)" f)
           (standard_data_f2f2 ~n:samples ~sign:0)


(* sub tests *)

let test_sub_ii ((a, b) as p1) ((c, d) as p2) =
  let v, tv = intervals_of_pair p1 and
      w, tw = intervals_of_pair p2 in
  let r = sub_ii v w and
      tr = T.sub_ii tv tw in
  begin
    fact ("valid", is_valid r && T.is_valid tr);
    fact ("eq", test_eq_intervals r tr);
    if is_pos v && is_neg w then fact ("pos", is_pos r);
    if is_neg v && is_pos w then fact ("neg", is_neg r);
  end;
  true

let test_sub_id_di ((a, b) as p) (c, _) =
  let v, tv = intervals_of_pair p in
  let x = if is_nan c || c = infinity || c = neg_infinity then 0. else c in
  let r = sub_id v x and
      r' = sub_di x v and
      tr = T.sub_id tv x and
      tr' = T.sub_di x tv in
  begin
    fact ("valid", is_valid r && is_valid r' && T.is_valid tr && T.is_valid tr');
    fact ("eq", test_eq_intervals r tr && test_eq_intervals r' tr');
    if is_pos v && x <= 0. then begin
        fact ("pos(id)", is_pos r);
        fact ("neg(di)", is_neg r');
      end;
    if is_neg v && x >= 0. then begin
        fact ("neg(id)", is_neg r);
        fact ("pos(di)", is_pos r');
      end;
  end;
  true

let () =
  let f = fun (a, b) (c, d) -> sub_ii (make_interval a b) (make_interval c d) in
  run_eq_f2f2 "sub_ii (eq)" ~cmp:cmp_intervals f [
                (0., 0.), (0., 0.), zero_interval;
                (infinity, neg_infinity), (1., 2.), empty_interval;
                (-3., -5.), (infinity, neg_infinity), empty_interval;
                (infinity, neg_infinity), (0., infinity), empty_interval;
                (neg_infinity, infinity), (0., 1.), entire_interval;
                (neg_infinity, infinity), (neg_infinity, infinity), entire_interval;
                (3., 5.), (0., 3.), make_interval 0. 5.;
                (neg_infinity, -1.), (neg_infinity, 0.1), entire_interval;
              ]
    
let () =
  let f = test_sub_ii in
  run_test (test_f2f2 "sub_ii (special)" f)
           (special_data_f2f2 ());
  run_test (test_f2f2 "sub_ii" f)
           (standard_data_f2f2 ~n:samples ~sign:0)

let () =
  let f = test_sub_id_di in
  run_test (test_f2f2 "sub_id(di) (special)" f)
           (special_data_f2f2 ());
  run_test (test_f2f2 "sub_id(di)" f)
           (standard_data_f2f2 ~n:samples ~sign:0)

(* mul tests *)

let test_mul_ii ((a, b) as p1) ((c, d) as p2) =
  let v, tv = intervals_of_pair p1 and
      w, tw = intervals_of_pair p2 in
  let r = mul_ii v w and
      tr = T.mul_ii tv tw in
  begin
    fact ("valid", is_valid r && T.is_valid tr);
    fact ("eq", test_eq_intervals r tr);
    if (is_pos v && is_pos w) || (is_neg v && is_neg w) then fact ("pos", is_pos r);
    if (is_pos v && is_neg w) || (is_neg v && is_pos w) then fact ("neg", is_neg r);
  end;
  true

let test_mul_id_di ((a, b) as p) (c, _) =
  let v, tv = intervals_of_pair p in
  let x = if is_nan c || c = infinity || c = neg_infinity then 0. else c in
  let r = mul_id v x and
      r' = mul_di x v and
      tr = T.mul_id tv x in
  begin
    fact ("id = di", cmp_intervals r r' = 0);
    fact ("valid", is_valid r && T.is_valid tr);
    fact ("eq", test_eq_intervals r tr);
    if (is_pos v && x >= 0.) || (is_neg v && x <= 0.) then fact ("pos", is_pos r);
    if (is_pos v && x <= 0.) || (is_neg v && x >= 0.) then fact ("neg", is_neg r);
  end;
  true

let () =
  let f = fun (a, b) (c, d) -> mul_ii (make_interval a b) (make_interval c d) in
  run_eq_f2f2 "mul_ii (eq)" ~cmp:cmp_intervals f [
        (0., 0.), (0., 0.), zero_interval;
        (infinity, neg_infinity), (1., 2.), empty_interval;
        (-3., -5.), (infinity, neg_infinity), empty_interval;
        (infinity, neg_infinity), (0., infinity), empty_interval;
        (neg_infinity, infinity), (neg_infinity, infinity), entire_interval;
        (neg_infinity, infinity), (0., 1.), entire_interval;
        (neg_infinity, infinity), (neg_infinity, infinity), entire_interval;
        (neg_infinity, infinity), (0., 0.), zero_interval;
        (neg_infinity, -1.), (0., infinity), make_interval neg_infinity 0.;
        (neg_infinity, -1.), (neg_infinity, 0.), make_interval 0. infinity;
              ]
    
let () =
  let f = test_mul_ii in
  run_test (test_f2f2 "mul_ii (special)" f)
           (special_data_f2f2 ());
  run_test (test_f2f2 "mul_ii" f)
           (standard_data_f2f2 ~n:samples ~sign:0)

let () =
  let f = test_mul_id_di in
  run_test (test_f2f2 "mul_id(di) (special)" f)
           (special_data_f2f2 ());
  run_test (test_f2f2 "mul_id(di)" f)
           (standard_data_f2f2 ~n:samples ~sign:0)


(* div tests *)

let test_div_ii ((a, b) as p1) ((c, d) as p2) =
  let v, tv = intervals_of_pair p1 and
      w, tw = intervals_of_pair p2 in
  let r = div_ii v w and
      tr = T.div_ii tv tw in
  begin
    fact ("valid", is_valid r && T.is_valid tr);
    fact ("eq", test_eq_intervals r tr);
    if (is_pos v && is_pos w) || (is_neg v && is_neg w) then fact ("pos", is_pos r);
    if (is_pos v && is_neg w) || (is_neg v && is_pos w) then fact ("neg", is_neg r);
  end;
  true

let test_div_id_di ((a, b) as p) (c, _) =
  let v, tv = intervals_of_pair p in
  let x = if is_nan c || c = infinity || c = neg_infinity then 0. else c in
  let r = div_id v x and
      r' = div_di x v and
      tr = T.div_id tv x and
      tr' = T.div_di x tv in
  begin
    fact ("valid", is_valid r && is_valid r' && T.is_valid tr && T.is_valid tr');
    fact ("eq", test_eq_intervals r tr && test_eq_intervals r' tr');
    if (is_pos v && x >= 0.) || (is_neg v && x <= 0.) then begin
        fact ("pos(id)", is_pos r);
        fact ("pos(di)", is_pos r');
      end;
    if (is_pos v && x <= 0.) || (is_neg v && x >= 0.) then begin
        fact ("neg(id)", is_neg r);
        fact ("neg(di)", is_neg r');
      end;
  end;
  true

let () =
  let f = fun (a, b) (c, d) -> div_ii (make_interval a b) (make_interval c d) in
  run_eq_f2f2 "div_ii (eq)" ~cmp:cmp_intervals f [
        (0., 0.), (0., 0.), empty_interval;
        (infinity, neg_infinity), (1., 2.), empty_interval;
        (-3., -5.), (infinity, neg_infinity), empty_interval;
        (infinity, neg_infinity), (0., infinity), empty_interval;
        (neg_infinity, infinity), (neg_infinity, infinity), entire_interval;
        (neg_infinity, infinity), (0., 1.), entire_interval;
        (neg_infinity, infinity), (0., 0.), empty_interval;
        (0., 0.), (neg_infinity, infinity), zero_interval;
        (neg_infinity, 0.), (0., infinity), make_interval neg_infinity 0.;
        (neg_infinity, 1.), (0., infinity), entire_interval;
        (neg_infinity, -100.), (0., infinity), make_interval neg_infinity 0.;
        (2., infinity), (0., infinity), make_interval 0. infinity;
        (neg_infinity, 0.), (neg_infinity, 0.), make_interval 0. infinity;
        (0., infinity), (0., infinity), make_interval 0. infinity;
        (-1., 1.), (0., 1.), entire_interval;
              ]
    
let () =
  let f = test_div_ii in
  run_test (test_f2f2 "div_ii (special)" f)
           (special_data_f2f2 ());
  run_test (test_f2f2 "div_ii" f)
           (standard_data_f2f2 ~n:samples ~sign:0)

let () =
  let f = test_div_id_di in
  run_test (test_f2f2 "div_id(di) (special)" f)
           (special_data_f2f2 ());
  run_test (test_f2f2 "div_id(di)" f)
           (standard_data_f2f2 ~n:samples ~sign:0)


(* inv tests *)

let test_inv_i ((a, b) as p) =
  let v, tv = intervals_of_pair p in
  let r = inv_i v and
      tr = T.inv_i tv in
  begin
    fact ("valid", is_valid r && T.is_valid tr);
    fact ("eq", test_eq_intervals r tr);
    if is_pos v then fact ("pos", is_pos r);
    if is_neg v then fact ("neg", is_neg r);
  end;
  true

let () =
  let f = fun (a, b) -> inv_i (make_interval a b) in
  run_eq_f2 "inv_i (eq)" ~cmp:cmp_intervals f [
              (-0., 0.),                empty_interval;
              (infinity, neg_infinity), empty_interval;
              (neg_infinity, infinity), entire_interval;
              (0., infinity),           make_interval 0. infinity;
              (neg_infinity, 0.),       make_interval neg_infinity 0.;
              (neg_infinity, 3.),       entire_interval;
              (-1., infinity),          entire_interval;
            ]

let () =
  let f = test_inv_i in
  run_test (test_f2 "inv_i (special)" f)
           (special_data_f2 ());
  run_test (test_f2 "inv_i" f)
           (standard_data_f2 ~n:samples ~sign:0)


(* sqrt tests *)

let test_sqrt_i ((a, b) as p) =
  let v, tv = intervals_of_pair p in
  let r = sqrt_i v and
      tr = T.sqrt_i tv in
  begin
    fact ("valid", is_valid r && T.is_valid tr);
    fact ("eq", test_eq_intervals r tr);
    fact ("pos", is_pos r);
    if v.high < 0. then fact ("empty", is_empty r);
  end;
  true

let () =
  let f = fun (a, b) -> sqrt_i (make_interval a b) in
  run_eq_f2 "sqrt_i (eq)" ~cmp:cmp_intervals f [
              (-0., 0.),                zero_interval;
              (infinity, neg_infinity), empty_interval;
              (-3., -2.),               empty_interval;
              (neg_infinity, infinity), make_interval 0. infinity;
              (0., infinity),           make_interval 0. infinity;
              (-5., 0.),                zero_interval;
              (neg_infinity, 0.),       zero_interval;
              (-1., infinity),          make_interval 0. infinity;
            ]

let () =
  let f = test_sqrt_i in
  run_test (test_f2 "sqrt_i (special)" f)
           (special_data_f2 ());
  run_test (test_f2 "sqrt_i" f)
           (standard_data_f2 ~n:samples ~sign:0)

(* sqr tests *)

let test_sqr_i ((a, b) as p) =
  let v, tv = intervals_of_pair p in
  let r = sqr_i v and
      tr = T.sqr_i tv in
  begin
    fact ("valid", is_valid r && T.is_valid tr);
    fact ("eq", test_eq_intervals r tr);
    fact ("pos", is_pos r);
  end;
  true

let () =
  let f = fun (a, b) -> sqr_i (make_interval a b) in
  run_eq_f2 "sqr_i (eq)" ~cmp:cmp_intervals f [
              (-0., 0.),                zero_interval;
              (infinity, neg_infinity), empty_interval;
              (neg_infinity, infinity), make_interval 0. infinity;
              (0., infinity),           make_interval 0. infinity;
              (neg_infinity, 0.),       make_interval 0. infinity;
              (-1., infinity),          make_interval 0. infinity;
              (neg_infinity, 2.),       make_interval 0. infinity;
            ]

let () =
  let f = test_sqr_i in
  run_test (test_f2 "sqr_i (special)" f)
           (special_data_f2 ());
  run_test (test_f2 "sqr_i" f)
           (standard_data_f2 ~n:samples ~sign:0)


(* pown tests *)

let test_pown_i ((a, b) as p) =
  let v, tv = intervals_of_pair p in
  let r0 = pown_i v 0 and
      r1 = pown_i v 1 and
      r3 = pown_i v 3 and
      r8 = pown_i v 8 and
      rn1 = pown_i v (-1) and
      rn2 = pown_i v (-2) and
      rn3 = pown_i v (-3) and
      tr3 = T.pown_i tv 3 and
      tr8 = T.pown_i tv 8 and
      trn1 = T.pown_i tv (-1) and
      trn2 = T.pown_i tv (-2) and
      trn3 = T.pown_i tv (-3) in
  begin
    fact ("valid", is_valid r0 && is_valid r1 && is_valid r3 && is_valid r8 &&
                     is_valid rn1 && is_valid rn2 && is_valid rn3 &&
                       T.is_valid tr3 && T.is_valid tr8 && T.is_valid trn1 &&
                         T.is_valid trn2 && T.is_valid trn3);
    if is_empty v then fact ("empty0", is_empty r0)
    else fact ("eq0", cmp_intervals r0 one_interval = 0);
    if T.is_empty tr3 then fact ("empty3", is_empty r3);
    if T.is_empty tr8 then fact ("empty8", is_empty r8);
    if T.is_empty trn1 then fact ("empty(-1)", is_empty rn1);
    if T.is_empty trn2 then fact ("empty(-2)", is_empty rn2);
    if T.is_empty trn3 then fact ("empty(-3)", is_empty rn3);
    fact ("eq1", cmp_intervals r1 v = 0);
    fact ("eq_pos", test_eq_intervals r3 tr3 && test_eq_intervals r8 tr8);
    fact ("eq_neg", test_eq_intervals rn1 trn1
                    && test_eq_intervals rn2 trn2
                    && test_eq_intervals rn3 trn3);
    if is_pos v then fact ("pos", is_pos r3 && is_pos r8
                                  && is_pos rn1 && is_pos rn2
                                  && is_pos rn3);
    if is_neg v then fact ("neg(odd)", is_neg r3 && is_neg rn1
                                       && is_neg rn3);
    if is_neg v then fact ("pos(even)", is_pos r8 && is_pos rn2);
  end;
  true

let () =
  let f = fun (a, b) e -> pown_i (make_interval a b) (int_of_float e) in
  run_eq_f2f "pown_i (eq)" ~cmp:cmp_intervals f [
               (-0., 0.), 3.,                 zero_interval;
               (0., 0.), 8.,                  zero_interval;
               (0., 0.), -2.,                 empty_interval;              
               (0., 0.), -3.,                 empty_interval;
               (0., 0.), -8.,                 empty_interval;
               (infinity, neg_infinity), -3., empty_interval;
               (neg_infinity, infinity), 3.,  entire_interval;
               (neg_infinity, infinity), 8.,  make_interval 0. infinity;
               (neg_infinity, infinity), -2., make_interval 0. infinity;
               (neg_infinity, infinity), -3., entire_interval;
               (neg_infinity, infinity), -8., make_interval 0. infinity;
               (0., infinity), 3.,            make_interval 0. infinity;
               (0., infinity), 8.,            make_interval 0. infinity;
               (0., infinity), -2.,           make_interval 0. infinity;
               (0., infinity), -3.,           make_interval 0. infinity;
               (0., infinity), -8.,           make_interval 0. infinity;
               (neg_infinity, 0.), 3.,        make_interval neg_infinity 0.;
               (neg_infinity, 0.), 8.,        make_interval 0. infinity;
               (neg_infinity, 0.), -2.,       make_interval 0. infinity;
               (neg_infinity, 0.), -3.,       make_interval neg_infinity 0.;
               (neg_infinity, 0.), -8.,       make_interval 0. infinity;
               (-1., infinity), 8.,           make_interval 0. infinity;
               (-1., infinity), -2.,          make_interval 0. infinity;
               (-1., infinity), -3.,          entire_interval;
               (-1., infinity), -8.,          make_interval 0. infinity;
               (neg_infinity, 2.), 8.,        make_interval 0. infinity;
               (neg_infinity, 2.), -2.,       make_interval 0. infinity;
               (neg_infinity, 2.), -3.,       entire_interval;
               (neg_infinity, 2.), -8.,       make_interval 0. infinity;              
             ]

let () =
  let f = test_pown_i in
  run_test (test_f2 "pown_i (special)" f)
           (special_data_f2 ());
  run_test (test_f2 "pown_i" f)
           (standard_data_f2 ~n:samples ~sign:0)

let () =
  let errs = errors () in
  if errs > 0 then
    Format.printf "FAILED: %d@." errs
  else
    Format.printf "ALL PASSED@.";
  exit (if errs > 0 then 1 else 0)
