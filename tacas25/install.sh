#!/usr/bin/env bash

# Installation script for the TACAS'25 artefact
# To be run from the artefact downloaded from Zenodo and in the TACAS VM

set -e

# Determine top-level artefact directory
ARTEFACT="$(dirname "$(cd -- "$(dirname "$0")" >/dev/null 2>&1; pwd -P)")"
echo "Determined \${ARTEFACT} as \`${ARTEFACT}\`"

for dir in runsolver veripb benchmarks scripts; do
  if [ ! -d "${ARTEFACT}/${dir}" ]; then
    echo "\`${ARTEFACT}/${dir}\` does not exitst, make sure to run this script from the downloaded TACAS'25 artefact"
    exit 1
  fi
done

# Install dependencies
sudo apt-get update
sudo apt-get -y install \
  build-essential curl pkg-config libssl-dev libclang-dev \
  python3 python3-pip python3-dev python3-venv g++ libgmp-dev

# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | \
  sh -s -- --default-toolchain none -y
source "${HOME}/.cargo/env"
rustup install nightly-2024-08-13 --profile minimal

# Install scuttle
# Build scripts on a VBox shared folder seem to not execute, hence we move the
# target directory to be in the VM
CARGO_TARGET_DIR="/tmp/scuttle-target" \
  cargo install --locked --path "${ARTEFACT}/scuttle/" --root "${ARTEFACT}"

# Install runsolver
cd "${ARTEFACT}/runsolver/src"
make runsolver
mv "${ARTEFACT}/runsolver/src/runsolver" "${ARTEFACT}/bin/"

# Install VeriPB
# Pip does not like to be executed in a VBox shared folder either, so copy the veripb directory just in case
cp -r "${ARTEFACT}/veripb" /tmp/veripb
pip3 install --user setuptools
pip3 install --user /tmp/veripb
rm -r /tmp/veripb
