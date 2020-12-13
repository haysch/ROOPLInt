.PHONY: build install

build:
	stack build

install:
	stack install

rplpp-test: build
	stack exec ROOPLInt test/ArrayUsageExample.rplpp
	stack exec ROOPLInt test/BinaryTree.rplpp
	stack exec ROOPLInt test/LinkedList.rplpp
	stack exec ROOPLInt test/DoublyLinkedList.rplpp
	stack exec ROOPLInt test/SimpleArithmetic.rplpp
	stack exec ROOPLInt test/SimpleConditional.rplpp
	stack exec ROOPLInt test/SimpleLoop.rplpp
	stack exec ROOPLInt test/SimpleMethodCall.rplpp