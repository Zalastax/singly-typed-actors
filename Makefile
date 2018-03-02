include .rc.make

.PHONY: latex latex-clean main generated-main
latex:
	$(MAKE) -f latex.make all

latex-clean:
	$(MAKE) -f latex.make clean

main:
	stack exec agda -- -c src/Examples/Main.agda

generated-main:
	sed 's/__ENTRY__/$(ENTRY)/' src/Examples/Main-template.agda > src/Examples/Main-generated.agda
	stack exec agda -- -c src/Examples/Main-generated.agda

