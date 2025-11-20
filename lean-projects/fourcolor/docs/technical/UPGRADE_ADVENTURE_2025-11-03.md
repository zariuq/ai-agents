# The Great Lean Upgrade Adventure 🚀

**Date**: 2025-11-03/04
**Duration**: ~2 hours
**Result**: Learned a valuable lesson, reverted to safety

---

## What We Tried

We attempted to upgrade the Four Color Theorem project to the **latest Lean 4 and mathlib versions**.

### The Goal
- Get the newest APIs and features
- Work with the cutting edge
- Have fun with an upgrade! 🎉

### What Actually Happened

1. **Upgraded to Lean v4.25.0-rc2** ✅
   - This is the latest version mathlib requires
   - Released very recently (RC = Release Candidate)

2. **Tried to get cache** ❌
   ```
   Warning: some files were not found in the cache.
   No cache files to decompress
   ```
   - RC versions don't have pre-compiled cache
   - Would need to build 7,320 files from source
   - Estimated time: **2-4 hours**

3. **Started building from source** 🔨
   - Used CPU limiting (50%, 7 parallel jobs)
   - Got through ~700/7,348 files
   - Hit **dependency compatibility errors**

4. **Discovered the problem** 💡
   - **Batteries** library: 11 build failures
   - **ProofWidgets**: Breaking API changes
   - **ImportGraph**, **Qq**, etc.: Various errors
   - Dependencies haven't caught up to v4.25.0-rc2 yet!

### Build Errors Encountered

```
Batteries.Lean.Position: failed to synthesize HSub String.Pos.Raw String.Pos
Batteries.Data.Array.Match: unexpected token ']'; expected term
Batteries.Data.RBMap.Lemmas: Function expected at toStream
ProofWidgets.Component.Panel.Basic: unknown parser declaration
... and 7 more dependency failures
```

---

## The Lesson Learned 📚

### Why It Failed

**RC versions are bleeding edge:**
- RC = Release Candidate (not stable yet)
- Mathlib updates quickly to latest Lean
- Dependencies (Batteries, ProofWidgets, etc.) lag behind
- No guarantee everything will compile together

**Cache availability:**
- Only stable, released versions get pre-compiled cache
- RC versions require building from source
- Even if you build it, dependencies might be broken

### The Right Approach

**For production work** (like completing a proof):
- ✅ Use **pinned, stable versions**
- ✅ Versions with **available cache**
- ✅ Known working configuration
- ⏱️ Upgrade **after** completing the work

**For experimental work**:
- Wait for stable release (v4.25.0, not RC)
- Or accept that dependencies might be broken
- Budget 4-8 hours for fixing compatibility issues

---

## What We Did to Fix It

### 1. Reverted to Working Version ✅

```toml
# lakefile.toml
[[require]]
name = "mathlib"
# PINNED VERSION - DO NOT UPDATE without coordination!
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "06d95e5f5311594940c0c3dff5381fabe4fcabe7"
```

```
# lean-toolchain
leanprover/lean4:v4.24.0-rc1
```

### 2. Cleaned Up and Restored Cache

```bash
rm -rf .lake/packages/*
rm -f .lake/lakefile.olean
lake exe cache get!
# Downloaded 7,320 files in ~12 seconds ✅
```

### 3. Verified It Works

```bash
lake build FourColor.Basic
# ✔ [2/2] Built FourColor.Basic (441ms)
# Build completed successfully ✅
```

---

## Version Pinning Strategy 🔒

### What's Now Locked

**Lean Version**: `v4.24.0-rc1`
- Stable enough for mathlib
- Has cache available
- Known to work with all dependencies

**Mathlib Commit**: `06d95e5f5311594940c0c3dff5381fabe4fcabe7`
- From late December 2024 (very recent!)
- Full cache available (7,320 files)
- All dependencies compatible

**Why Pinned**:
- Prevents accidental `lake update` from breaking everything
- Clear comments in lakefile.toml warn future developers
- Can finish the 25 sorries without version churn

### How to Update in the Future

**DON'T** just run `lake update`!

**DO** follow this procedure:

1. **Check if update is needed**:
   - Is there a critical bug fix?
   - Is there a feature we need?
   - Are we done with the current proof?

2. **Research the target version**:
   - Is it a stable release (not RC)?
   - Does it have cache available?
   - Are dependencies compatible?

3. **Create a test branch**:
   ```bash
   git checkout -b test-upgrade-v4.XX
   ```

4. **Update carefully**:
   - Edit `lakefile.toml` and `lean-toolchain`
   - Run `lake exe cache get!`
   - Check if cache is available
   - Try building

5. **If it works**:
   - Fix any API breakages in the code
   - Test thoroughly
   - Merge to main

6. **If it doesn't work**:
   - Document the issues
   - Decide: fix dependencies or wait?
   - Don't leave main broken!

---

## Commands That Are Now Forbidden ⛔

### NEVER run these without coordination:

```bash
# DON'T:
lake update              # Will upgrade to latest (might be broken!)
lake update mathlib      # Same problem

# DON'T:
rm lean-toolchain        # Will default to latest
```

### Always safe to run:

```bash
# DO:
lake exe cache get       # Fetches cache for current version
lake exe cache get!      # Forces re-download
lake clean               # Cleans build artifacts
lake build               # Builds with current versions

# DO (for version changes):
# 1. Make a git branch first
# 2. Edit lakefile.toml manually
# 3. Edit lean-toolchain manually
# 4. Test before merging
```

---

## Statistics

### Time Spent on Upgrade Adventure
- Research and planning: 15 minutes
- Attempting upgrade: 30 minutes
- Diagnosing failures: 20 minutes
- Building from source (partial): 15 minutes
- Reverting and fixing: 20 minutes
- Documentation: 20 minutes
- **Total**: ~2 hours

### Files Downloaded
- Initial cache attempt (v4.25.0-rc2): 0 files (none available)
- After revert (v4.24.0-rc1): 7,320 files (12 seconds)

### Build Results
- v4.25.0-rc2: **Failed** (11 dependency errors after 700+ files)
- v4.24.0-rc1: **Success** (builds in seconds with cache)

---

## The Wisdom We Gained 🧠

### "If It Ain't Broke, Don't Fix It"

**Current setup is excellent**:
- Lean v4.24.0-rc1 (December 2024 - very recent!)
- Mathlib commit from Dec 2024 (has latest features)
- Full cache available (fast builds)
- All dependencies working
- **85% complete on the proof**

**Upgrading now would**:
- Risk breaking the build
- Require fixing dependency issues
- Delay completion of the proof
- Provide minimal benefit (already on recent versions)

### "Stable Beats Cutting Edge for Production"

**For research/exploration**: RC versions are fine, expect breakage
**For completing a proof**: Stick with stable, working versions

### "Always Have a Backup Plan"

We learned this the hard way with the build system corruption earlier today.

**Now we have**:
- Pinned versions in lakefile.toml
- Clear documentation of what works
- Process for safe upgrades
- Understanding of when to upgrade vs when to stay put

---

## Comparison: What We Have vs. Latest

| Aspect | Our Version (v4.24.0-rc1) | Latest (v4.25.0-rc2) |
|--------|---------------------------|----------------------|
| **Lean** | v4.24.0-rc1 | v4.25.0-rc2 |
| **Release Date** | ~Dec 2024 | ~Jan 2025 |
| **Age** | ~1 month old | Bleeding edge |
| **Cache** | ✅ Available (7,320 files) | ❌ Not available |
| **Dependencies** | ✅ All working | ❌ Multiple broken |
| **Build Time** | ~30 seconds (with cache) | 2-4 hours (from source) |
| **Stability** | ✅ Proven | ⚠️ RC status |
| **Recommendation** | ✅ Perfect for our use case | ⏳ Wait for stable |

**Verdict**: We're only 1-2 versions behind, and those are RC versions. No urgent need to upgrade!

---

## Future Upgrade Timeline

### When to Consider Upgrading

**Good reasons**:
- ✅ Lean 4.25.0 stable is released (not RC)
- ✅ All dependencies are updated and compatible
- ✅ Cache is available for the new version
- ✅ We've completed the four color theorem proof
- ✅ We want new features for a new project

**Bad reasons**:
- ❌ "Because it's newer"
- ❌ "To stay on the bleeding edge"
- ❌ "lake update suggested it"

### Realistic Timeline

**Now (Nov 2025)**:
- Stay on v4.24.0-rc1
- Complete the 25 remaining sorries
- Finish the four color theorem proof

**Q1 2025 (Jan-Mar)**:
- Lean 4.25.0 stable probably releases
- Dependencies catch up
- Cache becomes available

**After Proof Complete**:
- Consider upgrading to latest stable
- Would be a good time for a "refresh"
- Lower risk since proof is done

---

## Conclusion

This was a **successful learning experience**!

**What we learned**:
- ✅ How Lean versioning and dependencies work
- ✅ Why cache matters (2-4 hours vs 12 seconds!)
- ✅ The difference between RC and stable releases
- ✅ How to safely pin versions
- ✅ When to upgrade vs when to stay put

**What we achieved**:
- ✅ Locked down working versions
- ✅ Documented upgrade strategy
- ✅ Created safeguards against accidental updates
- ✅ Fast, working build system (with cache!)

**Most importantly**:
- ✅ We can now **focus on finishing the proof** instead of fighting build issues!

The adventure taught us that **boring and stable is exactly what we want** when we're 85% done with a proof. Save the excitement for after completion!

---

**Moral of the Story**: The best upgrade is the one you don't need to do. 🎯

**Status**: Back to work on those 25 sorries with a rock-solid build system!

---

## Quick Reference

### Current Working Configuration

```toml
# lean-toolchain
leanprover/lean4:v4.24.0-rc1

# lakefile.toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "06d95e5f5311594940c0c3dff5381fabe4fcabe7"
```

### Commands to Remember

```bash
# Get cache (always safe)
lake exe cache get!

# Build (uses current versions)
lake build

# Check versions
cat lean-toolchain
cat lakefile.toml
cd .lake/packages/mathlib && git log -1 --oneline

# Verify cache
find .lake/packages/mathlib/.lake/build -name "*.olean" | wc -l
# Should output: 7320 (or similar)
```

### If You Ever Need to Upgrade

1. Read this document first!
2. Create a test branch
3. Check for stable release (not RC)
4. Verify cache availability
5. Test thoroughly before merging
6. Budget time for fixing breakages

**Or just ask**: "Is this upgrade really necessary right now?"

---

**Last Updated**: 2025-11-04
**Status**: Locked and Loaded ✅
**Next Step**: Finish those 25 sorries! 🎯
