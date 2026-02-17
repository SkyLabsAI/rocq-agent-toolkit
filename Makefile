.PHONY: all
all: help

.PHONY: help
help:
	@echo "Available Makefile targets:"
	@echo "- prepare: Sets up a local uv workspace (enables standalone use)."
	@echo "- clean: Removes the local uv workspace."
	@echo "- update: Add instructions to update pyproject.toml.disabled."

pyproject.toml: pyproject.toml.disabled
	cp $< $@

.PHONY: prepare
prepare: pyproject.toml

.PHONY: clean
clean:
	rm -f pyproject.toml

update:
	cp ../../pyproject.toml pyproject.toml.disabled
	echo 'Edit pyproject.toml.disabled and "filtermap" `tool.uv.workspace.members` to paths under `fmdeps/rocq-agent-toolkit`"
