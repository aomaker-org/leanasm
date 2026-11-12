# Path: leanasm/Makefile
# Makefile for leanasm workspace

SHELL := /bin/bash
REPO_ROOT := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
export PATH := $(HOME)/.elan/bin:$(PATH)

LAKE := lake
LEAN := lean

# Include lazy hydration module
-include $(REPO_ROOT)/mk/hydrate.mk

.PHONY: help build run test check clean status sync

help:
	@echo "leanasm Development Targets:"
	@echo "  make build          - Build the Lean executable and packages via lake"
	@echo "  make run            - Run the compiled Lean executable"
	@echo "  make test           - Run workspace verification and tests"
	@echo "  make check          - Typecheck and verify Lean files without full link"
	@echo "  make clean          - Remove lake build artifacts"
	@echo "  make status         - Show repository and toolchain status"
	@echo "  make sync           - Verify turn state, run tests, and audit tree"
	@echo "  make hydrate SUB=.. - Hydrate (inflate/wet) dormant subrepo"
	@echo "  make dehydrate SUB=.- Dehydrate (dry) working tree to reclaim disk"
	@echo "  make hydrate-status - Check thermal lifecycle status of submodules"

build:
	$(LAKE) build

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
