.PHONY: docker-build docker-run build install

build:
	stack build

install:
	stack install

docker-build:
	docker build -t rooplint:latest -f Dockerfile .

docker-run: docker-build
	docker run -p 8080:80 -it --rm --name rooplint-interface rooplint:latest

rplpp-test: build
	stack exec ROOPLInt test/ArrayUsageExample.rplpp
	stack exec ROOPLInt test/BinaryTree.rplpp
	stack exec ROOPLInt test/LinkedList.rplpp
	stack exec ROOPLInt test/DoublyLinkedList.rplpp
	stack exec ROOPLInt test/Fibonacci.rplpp
	stack exec ROOPLInt test/SimpleArithmetic.rplpp
	stack exec ROOPLInt test/SimpleConditional.rplpp
	stack exec ROOPLInt test/SimpleLoop.rplpp
	stack exec ROOPLInt test/SimpleMethodCall.rplpp