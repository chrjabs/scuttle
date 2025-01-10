#!/usr/bin/env bash

set -e

ARTEFACT="${1:-$(pwd)/tacas25-certified-mo-maxsat.zip}"
rm -rf "${ARTEFACT}"

SRCDIR="$(dirname "$(cd -- "$(dirname "$0")" >/dev/null 2>&1; pwd -P)")"

echo "Updating git submodules"
git -C "${SRCDIR}" submodule update --init --recursive

PACKDIR="/tmp/tacas25-certified-mo-maxsat/"
rm -rf "${PACKDIR}"
mkdir -p "${PACKDIR}"/{scuttle/{,maxpre-rs,rustsat},scripts,benchmarks}

echo "Copying artefact README"
cp "${SRCDIR}/tacas25/README.md" "${PACKDIR}"

echo "Copying paper data"
cp -r "${SRCDIR}/tacas25/data/" "${PACKDIR}"

echo "Copying scuttle source"
cp -r "${SRCDIR}"/{cadical-veripb-tracer,core,patches,proc,src,Cargo.lock,Cargo.toml,LICENSE,rust-toolchain.toml,README.md} "${PACKDIR}/scuttle/"
echo "Copying maxpre-rs source"
cp -r "${SRCDIR}"/maxpre-rs/{cppsrc,src,build.rs,Cargo.toml,LICENSE,README.md} "${PACKDIR}/scuttle/maxpre-rs"
echo "Copying rustsat source"
cp -r "${SRCDIR}"/rustsat/{cadical,pidgeons,src,Cargo.toml,LICENSE,README.md} "${PACKDIR}/scuttle/rustsat"
rm -f "${PACKDIR}"/scuttle/rustsat/cadical/*.log

echo "Copying artefact scripts"
cp "${SRCDIR}"/tacas25/{install.sh,experiments.sh,experiments-all.sh,single-experiment.sh} "${PACKDIR}/scripts/"

echo "Downloading runsolver"
RUNSOLVERCOMMIT="adf45810890dc9f6db06104d7842c2a26eb48f7a"
RUNSOLVERURL="https://github.com/chrjabs/runsolver/archive/${RUNSOLVERCOMMIT}.zip"
curl -L -o /tmp/runsolver.zip "${RUNSOLVERURL}"
cd "${PACKDIR}"
unzip /tmp/runsolver.zip && rm /tmp/runsolver.zip
mv "runsolver-${RUNSOLVERCOMMIT}/" "runsolver/"

echo "Downloading VeriPB"
VERIPBCOMMIT="fa86e38016cb7be21d086b84f829fa93b7e93bce"
VERIPBURL="https://gitlab.com/MIAOresearch/software/VeriPB/-/archive/${VERIPBCOMMIT}/VeriPB-${VERIPBCOMMIT}.tar.gz"
curl -o /tmp/veripb.tar.gz "${VERIPBURL}"
cd "${PACKDIR}"
tar -xzf /tmp/veripb.tar.gz && rm /tmp/veripb.tar.gz
mv "VeriPB-${VERIPBCOMMIT}/" "veripb/"
echo "Stripping unnecessary data from VeriPB"
rm -r "${PACKDIR}"/veripb/{sat-competition,tests,utils}

echo "Downloading Instances"
HASHES=$(cat "${SRCDIR}/tacas25/data/mcnf_meta.csv" | cut -d ',' -f1,4 | grep 'True' | cut -d ',' -f1 | tr '\n' ',' | sed 's/,$/\n/')
cd "${PACKDIR}/benchmarks/"
curl -L -Z -O "https://www.cs.helsinki.fi/group/coreo/benchmarks/multi-opt/{${HASHES}}.mcnf.xz"

echo "Zipping artefact"
cd "$(dirname "${PACKDIR}")"
zip -r "${ARTEFACT}" "$(basename "${PACKDIR}")"
rm -r "${PACKDIR}"
