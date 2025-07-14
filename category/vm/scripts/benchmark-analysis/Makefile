RUN := uv run

.PHONY: check
check:
	$(RUN) mypy src
	$(RUN) black --check src
	$(RUN) isort --check src
	$(RUN) autoflake --quiet --check src
	$(RUN) flake8 src

.PHONY: format
format:
	$(RUN) autoflake --quiet --in-place src
	$(RUN) isort src
	$(RUN) black src