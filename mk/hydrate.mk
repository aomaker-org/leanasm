# Path: leanasm/mk/hydrate.mk
# Purpose: Dynamic, on-demand ("lazy") Git submodule hydration & thermal management.
# Lineage: Adapted from clouds-labs/mk/hydrate.mk
# Max Column: 80 Columns (comments/docs) / 120 Chars (code)

.PHONY: hydrate dehydrate hydrate-status hydrate-all dehydrate-all \
        wet dry desertify wet-all dry-all thermal-status

# Usage: $(call hydrate-if-dormant,subrepos/llama.cpp)
define hydrate-if-dormant
	@if [ ! -d "$(REPO_ROOT)/$(1)/.git" ] && [ ! -f "$(REPO_ROOT)/$(1)/.git" ]; then \
		echo "[*] [LAZY HYDRATION] Subrepo '$(1)' is dormant. Inflating on demand..."; \
		git -C $(REPO_ROOT) submodule update --init --recursive $(1); \
		echo "[+] Subrepo '$(1)' is now hydrated (wet) into working tree."; \
	fi
endef

hydrate:
ifdef ALL
	@echo "[*] Hydrating (wetting) ALL registered workspace submodules..."
	git -C $(REPO_ROOT) submodule update --init --recursive
	@echo "[+] All submodules successfully hydrated (hot/wet)."
else ifdef SUB
	@_FULL_PATH="$(SUB)"; \
	if [ -d "$(REPO_ROOT)/subrepos/$${SUB}" ] || ([ -f "$(REPO_ROOT)/.gitmodules" ] && grep -q "subrepos/$${SUB}" "$(REPO_ROOT)/.gitmodules"); then \
		_FULL_PATH="subrepos/$${SUB}"; \
	fi; \
	echo "[*] Hydrating subrepo: $${_FULL_PATH}..."; \
	git -C $(REPO_ROOT) submodule update --init --recursive "$${_FULL_PATH}"; \
	echo "[+] Subrepo $${_FULL_PATH} hydrated into active working tree (hot/wet)."
else
	@echo "[!] Usage: make hydrate SUB=<name> [or: make hydrate ALL=1]"
	@echo "    Aliases: make wet SUB=<name>"
endif

wet: hydrate
hydrate-all:
	@$(MAKE) hydrate ALL=1
wet-all:
	@$(MAKE) hydrate ALL=1

dehydrate:
ifdef ALL
	@echo "[*] Dehydrating (drying) ALL submodules to reclaim disk space..."
	git -C $(REPO_ROOT) submodule deinit -f --all
	@echo "[+] All submodules dehydrated (dry/cold). Disk space reclaimed."
else ifdef SUB
	@_FULL_PATH="$(SUB)"; \
	if [ -d "$(REPO_ROOT)/subrepos/$${SUB}" ] || ([ -f "$(REPO_ROOT)/.gitmodules" ] && grep -q "subrepos/$${SUB}" "$(REPO_ROOT)/.gitmodules"); then \
		_FULL_PATH="subrepos/$${SUB}"; \
	fi; \
	echo "[*] Dehydrating subrepo & drying working tree: $${_FULL_PATH}..."; \
	git -C $(REPO_ROOT) submodule deinit -f "$${_FULL_PATH}"; \
	echo "[+] Subrepo $${_FULL_PATH} dehydrated (dry/cold). Working tree evacuated."
else
	@echo "[!] Usage: make dehydrate SUB=<name> [or: make dehydrate ALL=1]"
	@echo "    Aliases: make dry SUB=<name>"
endif

dry: dehydrate
desertify: dehydrate
dehydrate-all:
	@$(MAKE) dehydrate ALL=1
dry-all:
	@$(MAKE) dehydrate ALL=1

hydrate-status:
	@echo "============================================================"
	@echo "    Submodule Thermal Lifecycle & Hydration Audit           "
	@echo "============================================================"
	@echo " [GIT SUBMODULE REGISTRY STATUS]"
	@git -C $(REPO_ROOT) submodule status 2>/dev/null || echo "No submodules registered."
	@echo ""
	@echo " [THERMAL STATE AUDIT BY SUBREPO]"
	@if [ -d "$(REPO_ROOT)/subrepos" ]; then \
		for d in $(REPO_ROOT)/subrepos/*; do \
			if [ -d "$$d" ]; then \
				_REL="$${d#$(REPO_ROOT)/}"; \
				if [ -d "$$d/.git" ] || [ -f "$$d/.git" ]; then \
					_SZ=$$(du -sh "$$d" 2>/dev/null | cut -f1); \
					echo "  [HOT / WET]        $${_REL} (Size: $${_SZ})"; \
				elif [ -d "$(REPO_ROOT)/.git/modules/$${_REL}" ]; then \
					_CSZ=$$(du -sh "$(REPO_ROOT)/.git/modules/$${_REL}" 2>/dev/null | cut -f1); \
					echo "  [WARM / DRY]       $${_REL} (Tree empty, object cache: $${_CSZ})"; \
				else \
					echo "  [COLD / DESERT]    $${_REL} (Dormant manifest pointer only)"; \
				fi; \
			fi; \
		done; \
	else \
		echo "  No subrepos directory currently present."; \
	fi

thermal-status: hydrate-status

# end of file: leanasm/mk/hydrate.mk
