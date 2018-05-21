include .rc.make

subdirs := src/ src/Examples/ src/Libraries/ src/Selective/ src/Selective/Libraries/ src/Selective/Examples/
agda-objects := $(wildcard $(subdirs:%=%*.agdai))
executables := $(wildcard $(subdirs:%=%*.exe))
malonzo := $(wildcard $(subdirs:%=%MAlonzo/))

.PHONY: latex latex-clean main generated-main clean
latex:
	$(MAKE) -f latex.make all

latex-clean:
	$(MAKE) -f latex.make clean

main:
	stack exec agda -- -c src/Examples/Main.agda

generated-main:
	sed 's/__ENTRY__/$(ENTRY)/' src/Examples/Main-template.agda > src/Examples/Main-generated.agda
	stack exec agda -- -c src/Examples/Main-generated.agda

selective-generated-main:
	sed 's/__ENTRY__/$(ENTRY)/' src/Selective/Examples/Main-template.agda > src/Selective/Examples/Main-generated.agda
	stack exec agda -- -c src/Selective/Examples/Main-generated.agda

test-that-all-compliles:
	$(MAKE) latex-clean
	$(MAKE) latex
	stack exec agda -- --no-main -c src/Selective/Examples/Main-generated.agda
	stack exec agda -- --no-main -c src/Examples/Main-generated.agda

clean:
ifneq ($(strip $(agda-objects)),)
	rm $(agda-objects)
endif
ifneq ($(strip $(executables)),)
	rm $(executables)
endif
ifneq ($(strip $(malonzo)),)
	rm -rf $(malonzo)
endif
