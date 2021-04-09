.PHONY: docker-build docker-run build install rplpp-test

build:
	stack build

install: build
	stack install

docker-build:
	docker build -t rooplpp:latest -f Dockerfile .

docker-run: docker-build
	docker run -p 8080:80 -it --rm --name rooplpp-interface rooplpp:latest

rplpp-test: build
	stack exec rooplpp test/ArrayUsageExample.rplpp
	stack exec rooplpp test/BinaryTree.rplpp
	stack exec rooplpp test/BinaryTreeArrayUsage.rplpp
	stack exec rooplpp test/LinkedList.rplpp
	stack exec rooplpp test/LinkedListReversal.rplpp
	stack exec rooplpp test/DoublyLinkedList.rplpp
	stack exec rooplpp test/Fibonacci.rplpp
	stack exec rooplpp test/FindMinMax.rplpp
	stack exec rooplpp test/SimpleArithmetic.rplpp
	stack exec rooplpp test/SimpleConditional.rplpp
	stack exec rooplpp test/SimpleLoop.rplpp
	stack exec rooplpp test/SimpleMethodCall.rplpp
