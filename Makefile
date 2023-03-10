OCAMLFLAGS=-thread -rectypes -linkpkg -package coq-core.kernel

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile cube_solver cube_table_maker fast_cube_solver\
   cube.data

KNOWNFILES := Makefile _CoqProject

.DEFAULT_GOAL := all_cube #invoke-coqmakefile

all_cube : cube.data cube_table_maker fast_cube_solver cube_solver

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

all_positions.ml,all_positions.mli: cube_explore.vo extract_20.vo
	coqc extract_20.v

all_positions.cmi : all_positions.mli
	ocamlfind ocamlopt $(OCAMLFLAGS) all_positions.mli

all_positions.cmx : all_positions.ml all_positions.cmi
	ocamlfind ocamlopt -c $(OCAMLFLAGS) all_positions.ml

print_solution.cmi : print_solution.mli all_positions.cmi
	ocamlfind ocamlopt -c $(OCAMLFLAGS) print_solution.mli

print_solution.cmx : print_solution.ml print_solution.cmi all_positions.cmx
	ocamlfind ocamlopt -c $(OCAMLFLAGS) print_solution.ml

cube_solver : all_positions.cmx print_solution.cmx stub.ml
	 ocamlfind ocamlopt $(OCAMLFLAGS) -o cube_solver all_positions.cmx\
              print_solution.cmx stub.ml

cube_table_maker : all_positions.cmx stub2.ml
	 ocamlfind ocamlopt $(OCAMLFLAGS) -o cube_table_maker all_positions.cmx\
              stub2.ml
fast_cube_solver: all_positions.cmx print_solution.cmx stub3.m
	ocamlfind ocamlopt $(OCAMLFLAGS) -o fast_cube_solver all_positions.cmx\
          print_solution.cmx stub3.ml

cube.data : cube_table_maker
	./cube_table_maker

clean:
	rm -f *.cmx *.vo cube_solver cube.data cube_table_maker fast_cube_solver

%: invoke-coqmakefile
	@true

