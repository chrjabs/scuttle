#!/usr/bin/env bash

# Runs a single experiment, i.e., a scuttle algorithm on an instance with and without proof logging, and checking the proof

INSTANCE=$1
ALGORITHM=$2
COMMENT=$3

if [[ ! -f "${INSTANCE}" ]]; then
  >&2 echo "Instance \`${INSTANCE}\` does not exist"
  exit 1
fi

EXTRACTED="/tmp/$(basename -s .xz "${INSTANCE}")"
xz -dc "${INSTANCE}" > "${EXTRACTED}"

# Determine top-level artefact directory
ARTEFACT="$(dirname "$(cd -- "$(dirname "$0")" >/dev/null 2>&1; pwd -P)")"
>&2 echo "Determined \${ARTEFACT} as \`${ARTEFACT}\`"

SCUTTLE="${ARTEFACT}/bin/scuttle"
if [[ ! -x "${SCUTTLE}" ]]; then
  >&2 echo "scuttle not found at \`${SCUTTLE}\`, please run \`${ARTEFACT}/scripts/install.sh\` first"
  exit 1
fi

RUNSOLVER="${ARTEFACT}/bin/runsolver"
if [[ ! -x "${RUNSOLVER}" ]]; then
  >&2 echo "runsolver not found at \`${RUNSOLVER}\`, please run \`${ARTEFACT}/scripts/install.sh\` first"
  exit 1
fi

VERIPB="${HOME}/.local/bin/veripb"
if [[ ! -x "${VERIPB}" ]]; then
  >&2 echo "veripb not found at \`${VERIPB}\`, please run \`${ARTEFACT}/scripts/install.sh\` first"
  exit 1
fi

mkdir -p "${ARTEFACT}/results/"

# Run baseline
BASELINELOG="${ARTEFACT}/results/$(basename -s .mcnf ${EXTRACTED}).${ALGORITHM}.${COMMENT}.baseline"
>&2 echo "Writing baseline files to \`${BASELINELOG}.{out,var,wat}\`"
"${RUNSOLVER}" --timestamp -d 15 -o "${BASELINELOG}.out" -v "${BASELINELOG}.var" -w "${BASELINELOG}.wat" -C 3600 -M 32768 "${SCUTTLE}" "${ALGORITHM}" -v2 --preprocessing=false ${@:4} "${EXTRACTED}"

# Run proof-logging
LOGGINGLOG="${ARTEFACT}/results/$(basename -s .mcnf ${EXTRACTED}).${ALGORITHM}.${COMMENT}.logging"
>&2 echo "Writing proof-logging files to \`${LOGGINGLOG}.{out,var,wat,pbp,opb}\`"
"${RUNSOLVER}" --timestamp -d 15 -o "${LOGGINGLOG}.out" -v "${LOGGINGLOG}.var" -w "${LOGGINGLOG}.wat" -C 3600 -M 32768 "${SCUTTLE}" "${ALGORITHM}" -v2 --preprocessing=false ${@:4} "${EXTRACTED}" "${LOGGINGLOG}.pbp" "${LOGGINGLOG}.opb"

rm "${EXTRACTED}"

check_log () {
  LOG="$1"
  if grep -q -m1 'Maximum CPU time exceeded: sending SIGTERM then SIGKILL' "${LOG}.wat"; then
    echo "timeout"
    exit 1
  fi
  if grep -q -m1 'Maximum VSize exceeded: sending SIGTERM then SIGKILL' "${LOG}.wat"; then
    echo "memout"
    exit 2
  fi
  if grep -q -m1 'Child ended because it received signal 6 (SIGABRT)' "${LOG}.wat"; then
    echo "memout"
    exit 2
  fi
  if grep -q -m1 'Child ended because it received signal 11 (SIGSEGV)' "${LOG}.wat"; then
    echo "memout"
    exit 2
  fi
  grep -m1 "^CPUTIME" "${LOG}.var" | cut -d '=' -f2
}

print_results () {
  HASH=$(basename -s .mcnf.xz "${INSTANCE}")
  BASELINE=$(check_log "${BASELINELOG}")
  LOGGING=$(check_log "${LOGGINGLOG}")
  CHECKING="n/a"
  if [[ -f "${VERIPBLOG}.out" ]]; then
    CHECKING=$(check_log "${VERIPBLOG}")
  fi
  echo "${HASH},${BASELINE},${LOGGING},${CHECKING}"
}

VERIPBLOG="${ARTEFACT}/results/$(basename -s .mcnf ${EXTRACTED}).${ALGORITHM}.${COMMENT}.veripb"

if ! check_log "${LOGGINGLOG}"> /dev/null; then
  >&2 echo "Skipping VeriPB due to solver not done"
  print_results
  exit 0
fi

# Run VeriPB if proof-logging run terminated
>&2 echo "Writing proof-checking files to \`${VERIPBLOG}.{out,var,wat}\`"
"${RUNSOLVER}" --timestamp -d 15 -o "${VERIPBLOG}.out" -v "${VERIPBLOG}.var" -w "${VERIPBLOG}.wat" -C 36000 -M 32768 "${VERIPB}" --forceCheckDeletion "${LOGGINGLOG}.opb" "${LOGGINGLOG}.pbp"

print_results
