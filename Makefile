# The development lives in theories/. These targets run there.
.PHONY: all test check clean map
all:
	$(MAKE) -C theories
test:
	$(MAKE) -C theories test
check:
	$(MAKE) -C theories check
clean:
	$(MAKE) -C theories clean
# The relation map: every cited Rocq name exists, every formula renders.
map:
	sh docs/explorer/check.sh
