all: interval1 interval1-opt

interval1:
	ocamlc -o t_interval1 -I .. nums.cma unix.cma \
		../interval1.ml test_interval.ml test.ml t_interval1.ml
	ocamlc -o p_interval1 -I .. unix.cma \
		../interval1.ml test.ml p_interval1.ml

interval1-opt:
	ocamlopt -o t_interval1_opt -I .. nums.cmxa unix.cmxa \
		../interval1.ml test_interval.ml test.ml t_interval1.ml
	ocamlopt -o p_interval1_opt -I .. unix.cmxa \
		../interval1.ml test.ml p_interval1.ml

interval2:
	ocamlc -o t_interval2 -I .. nums.cma unix.cma \
		../interval2.ml test_interval.ml test.ml t_interval2.ml

interval2-opt:
	ocamlopt -o t_interval2_opt -I .. nums.cmxa unix.cmxa \
		../interval2.ml test_interval.ml test.ml t_interval2.ml

interval3:
	ocamlc -o t_interval3 -I .. nums.cma unix.cma \
		../interval3.ml test_interval.ml test.ml t_interval3.ml

interval3-opt:
	ocamlopt -o t_interval3_opt -I .. nums.cmxa unix.cmxa \
		../interval3.ml test_interval.ml test.ml t_interval3.ml

clean:
	rm -f *.cmo *.cmi *.cmx *.o \
	   t_interval1 t_interval2 t_interval3 \
	   p_interval1 p_interval2 p_interval3 \
	   t_interval1_opt t_interval2_opt t_interval3_opt \
	   p_interval1_opt p_interval2_opt p_interval3_opt
