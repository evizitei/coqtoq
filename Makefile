.PHONY: compile clean
compile:
	mkdir -p build
	coqc -o build/basic_proofs.vo basic_proofs.v

clean:
	rm -rf build