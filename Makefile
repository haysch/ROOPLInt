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
	stack exec ROOPLPP test/ArrayUsageExample.rplpp
	stack exec ROOPLPP test/BinaryTree.rplpp
	stack exec ROOPLPP test/BinaryTreeArrayUsage.rplpp
	stack exec ROOPLPP test/LinkedList.rplpp
	stack exec ROOPLPP test/DoublyLinkedList.rplpp
	stack exec ROOPLPP test/Fibonacci.rplpp
	stack exec ROOPLPP test/SimpleArithmetic.rplpp
	stack exec ROOPLPP test/SimpleConditional.rplpp
	stack exec ROOPLPP test/SimpleLoop.rplpp
	stack exec ROOPLPP test/SimpleMethodCall.rplpp
