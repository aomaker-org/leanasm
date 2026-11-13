# Path: leanasm/Makefile
# Makefile for leanasm workspace

SHELL := /bin/bash
REPO_ROOT := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
export PATH := $(HOME)/.elan/bin:$(PATH)

LAKE := lake
LEAN := lean
CHUNK_SECS ?= 900

# Include lazy hydration module
-include $(REPO_ROOT)/mk/hydrate.mk

.PHONY: help build build-chunk build-incremental build-status run test check clean status sync

help:
	@echo "leanasm Development Targets:"
	@echo "  make build            - Build the Lean executable and packages via lake"
	@echo "  make build-chunk      - Build incrementally up to CHUNK_SECS (default 900s = 15m)"
	@echo "  make build-incremental- Build all modules incrementally; fail if slice incomplete"
	@echo "  make build-status     - Show per-module .olean cache status and build timings"
	@echo "  make run              - Run the compiled Lean executable"
	@echo "  make test             - Run workspace verification and tests"
	@echo "  make check            - Typecheck and verify Lean files without full link"
	@echo "  make clean            - Remove lake build artifacts"
	@echo "  make status           - Show repository and toolchain status"
	@echo "  make sync             - Verify turn state, run tests, and audit tree"
	@echo "  make hydrate SUB=..   - Hydrate (inflate/wet) dormant subrepo"
	@echo "  make dehydrate SUB=.. - Dehydrate (dry) working tree to reclaim disk"
	@echo "  make hydrate-status   - Check thermal lifecycle status of submodules"

build:
	$(LAKE) build

build-chunk:
	python3 tools/incremental_build.py --budget-secs $(CHUNK_SECS)

build-incremental:
	python3 tools/incremental_build.py --budget-secs $(CHUNK_SECS) --require-complete

build-status:
	python3 tools/incremental_build.py --status

run:
	$(LAKE) exe leanasm

test: build
	@echo "[+] Running Lean executable test..."
	@$(LAKE) exe leanasm
	@echo "[+] Lean executable ran successfully."

check:
	$(LEAN) Main.lean

clean:
	$(LAKE) clean

status:
	@echo "=== Leanasm Environment Status ==="
	@echo "Node:      $$(hostname)"
	@echo "Lean:      $$(which $(LEAN) 2>/dev/null || echo 'Not found')"
	@if command -v $(LEAN) >/dev/null 2>&1; then $(LEAN) --version; fi
	@echo "Lake:      $$(which $(LAKE) 2>/dev/null || echo 'Not found')"
	@if command -v $(LAKE) >/dev/null 2>&1; then $(LAKE) --version; fi
	@echo "Git Head:  $$(git rev-parse --short HEAD 2>/dev/null || echo 'Pending')"
	@git status --short

sync: status test
	@echo "[+] Workspace synced and verified."

# end of file: leanasm/Makefile

# ------------------------------------------------------------------------------
# Yang-Mills Verification & Exploration Targets
# ------------------------------------------------------------------------------
.PHONY: ym-clone ym-integrity ym-status

YM_DIR := $(REPO_ROOT)/subrepos/YM/submissions/openai-20261028

ym-clone:
	@if [ ! -d "$(REPO_ROOT)/subrepos/YM/.git" ]; then \
		echo "[*] Cloning yang-mills-group/YM into subrepos/YM..."; \
		mkdir -p $(REPO_ROOT)/subrepos; \
		git clone https://github.com/yang-mills-group/YM.git $(REPO_ROOT)/subrepos/YM; \
		echo "[+] yang-mills-group/YM cloned successfully."; \
	else \
		echo "[+] subrepos/YM already present."; \
	fi

ym-integrity: ym-clone
	@echo "[*] Checking SHA-256 byte integrity of Yang-Mills package..."
	@cd $(YM_DIR) && python3 scripts/verify.py integrity

ym-status:
	@if [ -d "$(YM_DIR)" ]; then \
		echo "YM Package Directory: $(YM_DIR)"; \
		git -C $(REPO_ROOT)/subrepos/YM status --short; \
	else \
		echo "YM repository not hydrated. Run 'make ym-clone' or 'make ym-integrity'."; \
	fi
