# External Repos (Mettapedia)

This project embeds external Lean repos as local directories for deterministic builds.

## Canonical remotes

- `Mettapedia/external/exchangeability`
  - `origin`: `https://github.com/zariuq/exchangeability.git`
  - `branch`: `mettapedia`
  - parent repo policy: keep this as a local checkout only; do not track its files in `ai-agents`
- `Mettapedia/Logic/Foundation`
  - `origin`: `git@github.com:godelclaw/Foundation.git`
  - `upstream`: `https://github.com/zariuq/Foundation.git`
- `Mettapedia/Algebra/OrderedSemigroups`
  - `origin`: `git@github.com:godelclaw/OrderedSemigroups.git`
  - `upstream`: `https://github.com/zariuq/OrderedSemigroups.git`

## Branch/toolchain policy

- Keep both embedded repos on `main`.
- Lean toolchain target is `v4.27.0`.
- When syncing from upstream, fast-forward from `upstream/main` and then push to `origin/main`.

## Quick sync

```bash
# Exchangeability
cd Mettapedia/external/exchangeability
git fetch origin --prune
git checkout mettapedia
git pull --ff-only origin mettapedia

# Foundation
cd Mettapedia/Logic/Foundation
git fetch upstream origin --prune
git checkout main
git merge --ff-only upstream/main
git push origin main

# OrderedSemigroups
cd ../../Algebra/OrderedSemigroups
git fetch upstream origin --prune
git checkout main
git merge --ff-only upstream/main
git push origin main
```

## Parent repo rule

- `exchangeability` is an external working checkout under `Mettapedia/external/`.
- The parent `ai-agents` repo should ignore it, like the other embedded external repos.
- If the checkout is missing, clone it manually:

```bash
cd lean-projects/mettapedia/Mettapedia/external
git clone --branch mettapedia https://github.com/zariuq/exchangeability.git exchangeability
```
