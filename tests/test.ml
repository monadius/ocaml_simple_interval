let is_nan x = (compare x nan = 0)
                 
(* Returns a random floating-point number.
   sign: specifies the sign of the result (0 denotes a random sign)
   exp: the exponent of the result *)
let rand_float sign exp =
  let neg_flag = if sign = 0 then Random.bool() else (sign < 0) in
  let x = 1.0 +. Random.float (1.0 -. epsilon_float) in
  let x = if neg_flag then -.x else x in
  ldexp x exp

(* Auxiliary stream and list functions *)
        
let stream_map f stream =
  let next i =
    try Some (f (Stream.next stream))
    with Stream.Failure -> None in
  Stream.from next

let stream_concat streams =
  let ss = ref streams in
  let rec next i =
    match !ss with
    | [] -> None
    | stream :: rest ->
       begin
         try Some (Stream.next stream)
         with Stream.Failure -> (ss := rest; next i)
       end in
  Stream.from next

let stream_concat_random streams =
  let ss = Array.of_list streams in
  let n = ref (Array.length ss) in
  let rec next i =
    if !n <= 0 then None
    else begin
        let k = Random.int !n in
        try Some (Stream.next ss.(k))
        with Stream.Failure ->
          begin
            decr n;
            ss.(k) <- ss.(!n);
            next i
          end
      end in
  Stream.from next

let all_pairs list =
  let rec pairs x s =
    match s with
    | [] -> []
    | y :: ys -> (x, y) :: pairs x ys in
  List.fold_left (fun r x -> List.rev_append (pairs x list) r) [] list

let stream_pairs stream =
  let next i =
    try
      let x = Stream.next stream in
      let y = try Stream.next stream with Stream.Failure -> x in
      Some (x, y)
    with Stream.Failure -> None in
  Stream.from next

(* Streams of floating-point numbers *)
        
(* Returns an n-element stream of random floating-point numbers
   with exponents in the range [e_min, e_max] *)
let rand_floats ~n ~sign e_min e_max =
  assert (e_max >= e_min);
  let d = e_max - e_min + 1 in
  let next i =
    if i >= n then None
    else
      let e = e_min + Random.int d in
      Some (rand_float sign e) in
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
    else Some (rand_float sign !e) in
  Stream.from next

(* Returns a stream of floating-point numbers in the form
   +/-2^e with e in [e_min, e_max] *)
let p2_floats ~sign e_min e_max =
  assert (e_max >= e_min);
  let e = ref e_min in
  let next i =
    if !e > e_max then None
    else begin
        let exp = !e in
        let m =
          if sign > 0 then (incr e; 1.0)
          else if sign < 0 then (incr e; -1.0)
          else if i land 1 = 0 then 1.0
          else (incr e; -1.0) in
        Some (ldexp m exp)
      end in
  Stream.from next

(* Returns a stream of random floating-point numbers in
   the form +/-2^e with e in [e_min, e_max] *)
let rand_p2_floats ~n ~sign e_min e_max =
  assert (e_max >= e_min);
  let d = e_max - e_min + 1 in
  let next i =
    if i >= n then None
    else begin
        let neg_flag = if sign = 0 then Random.bool() else (sign < 0) in
        let e = e_min + Random.int d in
        let x = ldexp 1.0 e in
        if neg_flag then Some (-.x) else Some x
      end in
  Stream.from next


(* Functions for running tests *)              

type 'a test = {
    test_name: string;
    test_arg_name: 'a -> string;
    test_func: 'a -> bool;
  }
                 
let mk_test name arg_name f = {
    test_name = name;
    test_arg_name = arg_name;
    test_func = f
  }
                        
let run_test (test: 'a test) (data: 'a Stream.t) =
  let run x =
    try
      let result = test.test_func x in
      assert result
    with _ ->
      let msg = test.test_arg_name x in
      let fmt = Format.err_formatter in
      Format.pp_print_string fmt ("\rFAIL: " ^ msg);
      Format.pp_print_newline fmt () in
  begin
    let fmt = Format.std_formatter in
    Format.pp_print_string fmt ("Running: " ^ test.test_name ^ " ...");
    Format.pp_print_flush fmt ();
    Stream.iter run data;
    Format.pp_print_string fmt " done";
    Format.pp_print_newline fmt ()
  end

let run_tests (test: 'a test) (data: 'a Stream.t list) =
  run_test test (stream_concat data)

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

let test_f name f = mk_test name (name_f name) f

let test_f2 name f = mk_test name (name_f2 name) f

let test_f2f2 name f =
  mk_test name (name_f2f2 name) (fun (p1, p2) -> f p1 p2)

let test_f2f name f =
  mk_test name (name_f2f name) (fun (p, x) -> f p x)

let test_ff2 name f =
  mk_test name (name_ff2 name) (fun (x, p) -> f x p)

let mk_eq_test ?(cmp = Pervasives.compare) name name_arg f =
  mk_test name
          (fun (arg, _) -> name_arg arg)
          (fun (arg, result) -> cmp (f arg) result = 0)

let run_eq_f ?cmp name f data =
  let test = mk_eq_test ?cmp name (name_f name) f in
  let sd = Stream.of_list data in
  run_test test sd

let run_eq_f2 ?cmp name f data =
  let test = mk_eq_test ?cmp name (name_f2 name) f in
  let sd = Stream.of_list data in
  run_test test (stream_map (fun (a, b, r) -> (a, b), r) sd)

let run_eq_f2f2 ?cmp name f data =
  let test = mk_eq_test ?cmp name (name_f2f2 name) (fun (p1, p2) -> f p1 p2) in
  let sd = Stream.of_list data in
  run_test test (stream_map (fun (a, b, c, d, r) -> ((a, b), (c, d)), r) sd)

let run_eq_f2f ?cmp name f data =
  let test = mk_eq_test ?cmp name (name_f2f name) (fun (p, x) -> f p x) in
  let sd = Stream.of_list data in
  run_test test (stream_map (fun (a, b, c, r) -> ((a, b), c), r) sd)

let run_eq_ff2 ?cmp name f data =
  let test = mk_eq_test ?cmp name (name_ff2 name) (fun (x, p) -> f x p) in
  let sd = Stream.of_list data in
  run_test test (stream_map (fun (a, b, c, r) -> (a, (b, c)), r) sd)

(* Predefined test data *)
           
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

let special_data_f () = Stream.of_list special_floats

let special_data_f2 () =
  Stream.of_list (List.filter (fun (a, b) -> not (a > b))
                              (all_pairs special_floats))

let special_data_f2f2 () =
  let pairs = List.filter (fun (a, b) -> not (a > b))
                          (all_pairs special_floats) in
  Stream.of_list (all_pairs pairs)
           
let standard_data_f ~n ~sign =
  stream_concat [
      rand_floats_all 10 sign (-1074) 1023;
      p2_floats sign (-1075) 1023;
      stream_concat_random [
          rand_p2_floats (n / 2) sign (-30) 30;
          rand_floats (n / 2) sign (-30) 30;
        ];
      rand_floats n sign (-1074) 1023
    ]

let standard_data_f2 ~n ~sign =
  stream_pairs (standard_data_f (2 * n) sign)

let standard_data_f2f2 ~n ~sign =
  stream_pairs (standard_data_f2 (2 * n) sign)
