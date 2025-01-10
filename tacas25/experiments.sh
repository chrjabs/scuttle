#!/usr/bin/env bash

set -e

# Determine top-level artefact directory
ARTEFACT="$(dirname "$(cd -- "$(dirname "$0")" >/dev/null 2>&1; pwd -P)")"
>&2 echo "Determined \${ARTEFACT} as \`${ARTEFACT}\`"

RUNEXP="${ARTEFACT}/scripts/single-experiment.sh"

mkdir -p "${ARTEFACT}/results"

INSTANCES="0ec932de353de4de3bc67c4caec08bb9 009f795766e470b1e3f38815240eeae3 14ebdfdede4d00ddb39afd0ec2e96272 32fe4527cc9d2c943f03b2ae19ba0611 4f6237dc32086b905e38df19c02b2497 66df4b4dfbcebeedae549fdb11380b9e"

echo "inst-hash,pmin-cb-baseline,pmin-cb-proof-logging,pmin-cb-proof-checking"
for inst in ${INSTANCES}; do
  >&2 echo "Running P-Minimal experiments for instance \`${inst}\`"
  "${RUNEXP}" "${ARTEFACT}/benchmarks/${inst}.mcnf.xz" p-minimal cb --core-boosting=true
done
