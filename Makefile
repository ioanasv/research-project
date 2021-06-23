.PHONY: default build

default: build

build: 
	mkdir -p build
	@echo == Compiling project ==
	agda2hs -o src src/RangedSets/DiscreteOrdered.agda
	agda2hs -o src src/RangedSets/Boundaries.agda
	agda2hs -o src src/RangedSets/Ranges.agda
	agda2hs -o src src/RangedSets/RangedSet.agda

haskell: build
	ghc -fno-code src/RangedSets/DiscreteOrdered.hs
	ghc -fno-code src/RangedSets/Boundaries.hs
	ghc -fno-code src/RangedSets/Ranges.hs	
	ghc -fno-code src/RangedSets/RangedSet.hs
