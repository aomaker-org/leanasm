<!-- Path: leanasm/docs/lazy_hydration_guide.md -->
<!-- Max Column: 80 Columns -->

# Lazy Hydration and Subrepo Lifecycle Guide

## Background & Philosophy

Modeled on the thermal lifecycle and lazy-hydration architecture from
`clouds-labs`, `leanasm` adopts an on-demand hydration workflow for subrepos,
external theorem libraries, and heavy dependencies (such as `llama.cpp`,
`repl`, `Mathlib`, or `formal-conjectures`).

## Thermal State Synonyms

| Thermal State | Tactile State | Definition |
| :--- | :--- | :--- |
| **Hot** | **Wet / Inflated** | Submodule is checked out, active, and populated on disk. |
| **Warm** | **Dry / Cached** | Working tree evacuated; git object cache kept in `.git/modules`. |
| **Cold** | **Desert / Dormant** | Uninitialized submodule; only pointer exists in `.gitmodules`. |

## Key Operations

### 1. On-Demand Lazy Hydration
When a build recipe requires an external subproject (e.g. `subrepos/llama.cpp`
or `subrepos/repl`), the build system checks for the presence of the
submodule's `.git` entry. If absent, it automatically triggers:
```bash
git submodule update --init --recursive <path>
```

### 2. Manual Hydration (`make hydrate` / `make wet`)
Developers or agents can explicitly inflate submodules when beginning work:
```bash
make hydrate SUB=llama.cpp
make wet ALL=1
```

### 3. Dehydration (`make dehydrate` / `make dry`)
To preserve disk space on constrained local hosts or CI environments, subtrees
can be dehydrated without losing git commit references:
```bash
make dehydrate SUB=llama.cpp
make dry ALL=1
```

### 4. Thermal Audit (`make hydrate-status`)
Displays whether registered submodules are hot (wet on disk), warm (cached in
`.git/modules`), or cold (dormant manifest pointer).

<!-- end of file: leanasm/docs/lazy_hydration_guide.md -->
