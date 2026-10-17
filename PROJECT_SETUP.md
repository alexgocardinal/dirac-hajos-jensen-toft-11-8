# Before posting this folder to GitHub

Copy the following **existing** files from the `dirac_hajos` mathlib project
on your computer into this folder, beside `README.md`:

1. `lean-toolchain`
2. `lakefile.toml` or `lakefile.lean`
3. `lake-manifest.json`

Then run `sh verify.sh` from this folder. A successful run verifies exactly the
files listed in `README.md`. `.gitignore` excludes the generated `.lake` cache.

The paper's general `k ≥ 5` theorem is not fully formalized yet; the source
documents its precise current status.
