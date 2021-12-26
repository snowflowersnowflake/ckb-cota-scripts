build:
	cd contracts && cargo fmt
	capsule build

build-release:
	cd contracts && cargo fmt
	cp c/build/ckb_smt build/release/
	capsule build --release

test:
	cd contracts && cargo fmt
	cp c/build/ckb_smt build/debug/
	capsule test

test-release:
	cp c/build/ckb_smt build/release/
	capsule test --release

clean:
	rm -rf build/debug

clean-release:
	rm -rf build/release

.PHONY: build test clean