#!/usr/bin/env bash

set -e

# Determine top-level artefact directory
ARTEFACT="$(dirname "$(cd -- "$(dirname "$0")" >/dev/null 2>&1; pwd -P)")"
>&2 echo "Determined \${ARTEFACT} as \`${ARTEFACT}\`"

RUNEXP="${ARTEFACT}/scripts/single-experiment.sh"

mkdir -p "${ARTEFACT}/results"

echo "=== P-Minimal (CB) Experiments ==="
echo "inst-hash,pmin-cb-baseline,pmin-cb-proof-logging,pmin-cb-proof-checking"
for inst in "${ARTEFACT}"/benchmarks/*.mcnf.xz; do
  >&2 echo "Running P-Minimal (CB) experiments for instance \`${inst}\`"
  "${RUNEXP}" "${ARTEFACT}/benchmarks/${inst}.mcnf.xz" p-minimal cb --core-boosting=true
done

echo ""
echo "=== BiOptSat (CB) Experiments ==="
echo "inst-hash,bos-cb-baseline,bos-cb-proof-logging,bos-cb-proof-checking"
for inst in "${ARTEFACT}"/benchmarks/*.mcnf.xz; do
  >&2 echo "Running BiOptSat (CB) experiments for instance \`${inst}\`"
  "${RUNEXP}" "${ARTEFACT}/benchmarks/${inst}.mcnf.xz" bioptsat cb --core-boosting=true
done

echo ""
echo "=== LowerBounding (CB) Experiments ==="
echo "inst-hash,lb-cb-baseline,lb-cb-proof-logging,lb-cb-proof-checking"
for inst in "${ARTEFACT}"/benchmarks/*.mcnf.xz; do
  >&2 echo "Running LowerBounding (CB) experiments for instance \`${inst}\`"
  "${RUNEXP}" "${ARTEFACT}/benchmarks/${inst}.mcnf.xz" lower-bounding cb --core-boosting=true
done

echo ""
echo "=== P-Minimal (no-CB) Experiments ==="
echo "inst-hash,pmin-nocb-baseline,pmin-nocb-proof-logging,pmin-nocb-proof-checking"
for inst in "${ARTEFACT}"/benchmarks/*.mcnf.xz; do
  >&2 echo "Running P-Minimal (no-CB) experiments for instance \`${inst}\`"
  "${RUNEXP}" "${ARTEFACT}/benchmarks/${inst}.mcnf.xz" p-minimal nocb --core-boosting=false
done

echo ""
echo "=== BiOptSat (no-CB) Experiments ==="
echo "inst-hash,bos-nocb-baseline,bos-nocb-proof-logging,bos-nocb-proof-checking"
for inst in "${ARTEFACT}"/benchmarks/*.mcnf.xz; do
  >&2 echo "Running BiOptSat (no-CB) experiments for instance \`${inst}\`"
  "${RUNEXP}" "${ARTEFACT}/benchmarks/${inst}.mcnf.xz" bioptsat nocb --core-boosting=false
done

echo ""
echo "=== LowerBounding (no-CB) Experiments ==="
echo "inst-hash,lb-nocb-baseline,lb-nocb-proof-logging,lb-nocb-proof-checking"
for inst in "${ARTEFACT}"/benchmarks/*.mcnf.xz; do
  >&2 echo "Running LowerBounding (no-CB) experiments for instance \`${inst}\`"
  "${RUNEXP}" "${ARTEFACT}/benchmarks/${inst}.mcnf.xz" lower-bounding nocb --core-boosting=false
done
