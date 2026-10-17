#!/bin/sh
set -eu

mkdir -p .lake/build/lib/lean

for module in \
  AllColorRigidityFixed \
  PaletteBridgeImported \
  D5Structure \
  D5NoFour \
  D5Counterexample \
  GeneralObstruction \
  GeneralPaletteEncodingFixed \
  GeneralPaletteRigidity \
  GeneralTwoCopy \
  GeneralColorCount \
  GeneralRemainingPalette \
  GeneralCliqueObstruction \
  GeneralConstructionNative \
  GeneralEdgeFacts \
  GeneralCliqueEdgesFixed \
  GeneralColorPullback \
  GeneralCliqueColors \
  GeneralNoKMinusOne
do
  echo "Checking $module.lean"
  lake env lean -o ".lake/build/lib/lean/$module.olean" "$module.lean"
done

echo "All listed Lean files passed. The remaining all-k steps are still in progress."
