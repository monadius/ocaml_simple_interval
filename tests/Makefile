all: t_interval1 t_interval1_opt t_interval2 t_interval2_opt
	./t_interval1
	./t_interval1_opt
	./t_interval2
	./t_interval2_opt

t_interval1:
	ocamlc -o t_interval1 -I .. nums.cma unix.cma \
		../interval1.ml test_interval.ml test.ml t_interval1.ml
	ocamlc -o p_interval1 -I .. unix.cma \
		../interval1.ml test.ml p_interval1.ml

t_interval1_js:
	ocamlfind ocamlc -I .. -package js_of_ocaml -package num -package unix -linkpkg \
		-o t_interval1.bytes ../interval1.ml test.ml test_interval.ml t_interval1.ml
	js_of_ocaml t_interval1.bytes
	ocamlfind ocamlc -I .. -package js_of_ocaml -package num -package unix -linkpkg \
		-o p_interval1.bytes ../interval1.ml test.ml test_interval.ml p_interval1.ml
	js_of_ocaml p_interval1.bytes

t_interval1_opt:
	ocamlopt -o t_interval1_opt -I .. nums.cmxa unix.cmxa \
		../interval1.ml test_interval.ml test.ml t_interval1.ml
	ocamlopt -o p_interval1_opt -I .. unix.cmxa \
		../interval1.ml test.ml p_interval1.ml

t_interval2:
	ocamlc -o t_interval2 -I .. nums.cma unix.cma \
		../interval2.ml test_interval.ml test.ml t_interval2.ml
	ocamlc -o p_interval2 -I .. nums.cma unix.cma \
		../interval2.ml test.ml p_interval2.ml

t_interval2_js:
	ocamlfind ocamlc -I .. -package js_of_ocaml -package num -package unix -linkpkg \
		-o t_interval2.bytes ../interval2.ml test.ml test_interval.ml t_interval2.ml
	js_of_ocaml t_interval2.bytes
	ocamlfind ocamlc -I .. -package js_of_ocaml -package num -package unix -linkpkg \
		-o p_interval2.bytes ../interval2.ml test.ml test_interval.ml p_interval2.ml
	js_of_ocaml p_interval2.bytes

t_interval2_opt:
	ocamlopt -o t_interval2_opt -I .. nums.cmxa unix.cmxa \
		../interval2.ml test_interval.ml test.ml t_interval2.ml
	ocamlopt -o p_interval2_opt -I .. nums.cmxa unix.cmxa \
		../interval2.ml test.ml p_interval2.ml

t_interval_tmp:
	ocamlc -o t_interval_tmp -I .. nums.cma unix.cma \
		../interval_tmp.ml test_interval.ml test.ml t_interval_tmp.ml

t_interval_tmp_opt:
	ocamlopt -o t_interval_tmp_opt -I .. nums.cmxa unix.cmxa \
		../interval_tmp.ml test_interval.ml test.ml t_interval_tmp.ml

clean:
	rm -f *.cmo *.cmi *.cmx *.o \
	   t_interval1 t_interval2 t_interval_tmp \
	   p_interval1 p_interval2 p_interval_tmp \
	   t_interval1_opt t_interval2_opt t_interval_tmp_opt \
	   p_interval1_opt p_interval2_opt p_interval_tmp_opt
