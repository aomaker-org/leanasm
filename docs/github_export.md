# Path: leanasm/docs/github_export.md
# docs/github_export.md - GitHub Repository, Issues, and PRs Export Guide
# Max Column: 80 Columns

## Overview

This guide explains how repository file manifests, GitHub Issues, and Pull
Requests (PRs) from `aomaker-org/leanasm` were generated and formatted for
ingestion into Google NotebookLM or Gemini notebooks.

---

## 1. Generated Artifacts Summary

The following files are available in `docs/`:

- [`docs/raw_repo_links.txt`](docs/raw_repo_links.txt):
  Raw `https://raw.githubusercontent.com/...` URLs for all 157 tracked files.
- [`docs/github_issues.md`](docs/github_issues.md):
  Formatted Markdown digest of all 35 GitHub issues (metadata and body text).
- [`docs/github_prs.md`](docs/github_prs.md):
  Formatted Markdown digest of all 57 GitHub PRs (metadata, branches, body).
- [`docs/github_issues.json`](docs/github_issues.json):
  Full structured JSON export of all repository issues.
- [`docs/github_prs.json`](docs/github_prs.json):
  Full structured JSON export of all pull requests.
- [`docs/github_issue_pr_links.txt`](docs/github_issue_pr_links.txt):
  Plaintext list of web URLs for all issues and PRs.

---

## 2. Ingestion Options for Google NotebookLM / Gemini

1. **Direct File Upload (Fastest & Richest)**:
   Upload [`docs/github_issues.md`](docs/github_issues.md) and
   [`docs/github_prs.md`](docs/github_prs.md) directly as source documents
   into NotebookLM. NotebookLM indexes markdown documents with full headings
   and preserves cross-references.

2. **Raw GitHub Source Links (Auto-Synced)**:
   Once merged and pushed to `main`, NotebookLM or web-capable notebooks can
   read directly from:
   - `https://raw.githubusercontent.com/aomaker-org/leanasm/main/docs/github_issues.md`
   - `https://raw.githubusercontent.com/aomaker-org/leanasm/main/docs/github_prs.md`
   - `https://raw.githubusercontent.com/aomaker-org/leanasm/main/docs/raw_repo_links.txt`

---

## 3. AGY Prompt Example for Re-generating or Updating

To reproduce, refresh, or update these exports in future sessions with `agy`,
you can run the following sample prompt:

```text
Please refresh the GitHub exports for the repository:
1. Generate an updated list of raw GitHub URLs for all repository files into
   docs/raw_repo_links.txt using the base format:
   https://raw.githubusercontent.com/aomaker-org/leanasm/main/<filepath>
2. Query the GitHub CLI (`gh`) to fetch all open and closed issues and pull
   requests.
3. Export:
   - A clean Markdown digest of all issues to docs/github_issues.md
   - A clean Markdown digest of all pull requests to docs/github_prs.md
   - Structured JSON files to docs/github_issues.json and docs/github_prs.json
   - Web URLs to docs/github_issue_pr_links.txt
```

---

## 4. Shell / Python Reproducibility Script

Below is the standalone command used to generate the export files:

```bash
# 1. Generate repository raw links
python3 -c "
import subprocess
prefix = 'https://raw.githubusercontent.com/aomaker-org/leanasm/main/'
files = subprocess.check_output(['git', 'ls-files'], text=True).splitlines()
with open('docs/raw_repo_links.txt', 'w') as f:
    for fpath in files:
        f.write(f'{prefix}{fpath}\n')
"

# 2. Export Issues and PRs via gh CLI into JSON and Markdown digests
python3 -c '
import json, subprocess
repo = "aomaker-org/leanasm"

issues_json = subprocess.check_output([
    "gh", "issue", "list", "--repo", repo, "--state", "all", "--limit", "200",
    "--json", "number,title,state,author,createdAt,updatedAt,closedAt,labels,body,url"
], text=True)

prs_json = subprocess.check_output([
    "gh", "pr", "list", "--repo", repo, "--state", "all", "--limit", "200",
    "--json", "number,title,state,author,createdAt,updatedAt,closedAt,labels,body,url,headRefName,baseRefName"
], text=True)

issues = json.loads(issues_json)
prs = json.loads(prs_json)

with open("docs/github_issues.json", "w") as f:
    json.dump(issues, f, indent=2)

with open("docs/github_prs.json", "w") as f:
    json.dump(prs, f, indent=2)

with open("docs/github_issue_pr_links.txt", "w") as f:
    f.write("# GitHub Issues\n")
    for item in sorted(issues, key=lambda x: x["number"]):
        f.write(item["url"] + "\n")
    f.write("\n# GitHub Pull Requests\n")
    for item in sorted(prs, key=lambda x: x["number"]):
        f.write(item["url"] + "\n")

with open("docs/github_issues.md", "w") as f:
    f.write("# Repository Issues Digest (aomaker-org/leanasm)\n\n")
    for item in sorted(issues, key=lambda x: x["number"]):
        labels = ", ".join([l["name"] for l in item.get("labels", [])]) or "None"
        author = item["author"]["login"] if item.get("author") else "unknown"
        f.write(f"## Issue #{item[\"number\"]}: {item[\"title\"]}\n")
        f.write(f"- **Status**: {item[\"state\"]}\n")
        f.write(f"- **Author**: @{author}\n")
        f.write(f"- **Created**: {item[\"createdAt\"]}\n")
        f.write(f"- **Labels**: {labels}\n")
        f.write(f"- **URL**: {item[\"url\"]}\n\n")
        f.write(f"### Description\n\n{item.get(\"body\") or \"_No description provided._\"}\n\n---\n\n")

with open("docs/github_prs.md", "w") as f:
    f.write("# Repository Pull Requests Digest (aomaker-org/leanasm)\n\n")
    for item in sorted(prs, key=lambda x: x["number"]):
        labels = ", ".join([l["name"] for l in item.get("labels", [])]) or "None"
        author = item["author"]["login"] if item.get("author") else "unknown"
        head_ref = item.get("headRefName", "N/A")
        base_ref = item.get("baseRefName", "N/A")
        f.write(f"## PR #{item[\"number\"]}: {item[\"title\"]}\n")
        f.write(f"- **Status**: {item[\"state\"]}\n")
        f.write(f"- **Author**: @{author}\n")
        f.write(f"- **Branch**: `{head_ref}` -> `{base_ref}`\n")
        f.write(f"- **Created**: {item[\"createdAt\"]}\n")
        f.write(f"- **Labels**: {labels}\n")
        f.write(f"- **URL**: {item[\"url\"]}\n\n")
        f.write(f"### Description\n\n{item.get(\"body\") or \"_No description provided._\"}\n\n---\n\n")
'
```

<!-- end of file: leanasm/docs/github_export.md -->
