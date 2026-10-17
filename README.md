# Clique identification in a Dirac–Hajós construction

Alex Chan · Harvard University and National Bureau of Economic Research  
<achan@hbs.edu>

This repository accompanies a draft paper on Jensen–Toft Problem 11.8. The
paper proves a counterexample for every `k ≥ 5`. The formal proof is **not yet
complete for every k**.

## Verified finite certificate

The import chain below was checked by Lean 4/mathlib in the author's working
project. `D5Counterexample.lean` establishes that the concrete 23-vertex graph
contains edge `01`, has a five-coloring, and neither it nor its edge deletion
has a four-coloring. All of these files live together at the repository root
because their Lean imports use these exact names.

```text
AllColorRigidityFixed.lean
  → PaletteBridgeImported.lean
  → D5Structure.lean
  → D5NoFour.lean
  → D5Counterexample.lean
```

## Checked steps toward the general theorem

These separate modules passed Lean on the author's machine:

- `GeneralObstruction.lean` — two-copy contradiction for any color type.
- `GeneralPaletteEncodingFixed.lean` — naming arbitrary three-color palettes.
- `GeneralPaletteRigidity.lean` — transfer of base rigidity to those palettes.
- `GeneralTwoCopy.lean` — two base copies with palette assumptions.
- `GeneralColorCount.lean` — pigeonhole bound outside an `r`-clique.
- `GeneralRemainingPalette.lean` — constructs the three remaining colors.
- `GeneralCliqueObstruction.lean` — combines clique colors with two-copy rigidity.
- `GeneralConstructionNative.lean` — defines the output edge family and checks
  that `r = 1` is the concrete `D5Structure.lean` edge set. **This last equality
  uses `native_decide`, which trusts the Lean compiler for that calculation.**

The following additional modules passed Lean on the author's machine:

- `GeneralEdgeFacts.lean` and `GeneralCliqueEdgesFixed.lean` — graph-specific
  base, clique, and join edges in the symbolic family.
- `GeneralColorPullback.lean` — a proper output coloring restricts to both
  twelve-vertex base copies.
- `GeneralCliqueColors.lean` — the added clique vertices receive distinct
  colors avoided by their respective base copies.
- `GeneralNoKMinusOne.lean` — **for every `r`, the symbolic output `dEdges r`
  has no proper coloring with `r + 3` colors**. For `k = r + 4`, this gives the
  chromatic lower bound in the paper's construction.

The input `k`-criticality proof and the matching general `k`-coloring remain
unformalized. Do not describe the paper's full all-`k` theorem as Lean
verified yet.

## Reproduce the checks

From this folder in a compatible mathlib project, run:

```sh
sh verify.sh
```

The script compiles imports in order and stops at the first Lean error.
Warnings about deprecated tactics or unused simplifier arguments are harmless.

To make the repository reproducible, copy `lean-toolchain`, `lakefile.toml`
(or `lakefile.lean`), and `lake-manifest.json` from the **working** mathlib
project on the author's computer into this folder. Those three exact files
were not available when this bundle was made. Do not upload `.lake`.

## Paper and data

- `paper/paper.tex` — LaTeX source in the requested article format.
- `paper/paper.pdf` — readable draft with the current verification status.
- `data/dirac_hajos_graphs.json` — finite edges and coloring certificates.
- `scripts/dirac_hajos_11_8_check.py` — independent Python checker, runnable as
  `python3 scripts/dirac_hajos_11_8_check.py`.

The paper links to this repository: [https://github.com/alexgocardinal/dirac-hajos-jensen-toft-11-8](https://github.com/alexgocardinal/dirac-hajos-jensen-toft-11-8).
