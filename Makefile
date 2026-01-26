.PHONY: all
all: help

.PHONY: help
help:
	@echo "Available Makefile targets:"
	@echo "- prepare: Sets up a local uv workspace (enables standalone use)."
	@echo "- clean: Removes the local uv workspace."

pyproject.toml: pyproject.toml.disabled
	cp $< $@

.PHONY: prepare
prepare: pyproject.toml

.PHONY: clean
clean:
	rm -f pyproject.toml
