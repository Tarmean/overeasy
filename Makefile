include Makefile.base

.PHONY: exe
exe: build
	stack exec -- overeasy-exe

.PHONY: docker-test
docker-test:
	docker run -i -v ${PWD}:/project -w /project -t haskell:8.10.7 /bin/bash -c 'make test'

.PHONY: debug-test
debug-test:
	PROP_UNIT_DEBUG=1 stack test --trace --profile

.PHONY: deep-test
deep-test:
	PROP_UNIT_LIMIT=1000 make test
