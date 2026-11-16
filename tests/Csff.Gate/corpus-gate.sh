#!/bin/zsh
set -u
HERE=${0:a:h}
ROOT=${HERE:h:h}
CORPUS=""
WORK="${TMPDIR:-/tmp}/csff-gate"
CLI=""
CONFIGS=""
JOBS=8
BUDGET=8
OUT=""
UPDATE=0
KEEP=0
REFUSALS=0

while [ $# -gt 0 ]; do
  case $1 in
    --corpus) CORPUS=$2; shift 2 ;;
    --cli) CLI=$2; shift 2 ;;
    --configs) CONFIGS=$2; shift 2 ;;
    --jobs) JOBS=$2; shift 2 ;;
    --symbol-budget) BUDGET=$2; shift 2 ;;
    --out) OUT=$2; shift 2 ;;
    --work) WORK=$2; shift 2 ;;
    --update-pins) UPDATE=1; shift ;;
    --keep) KEEP=1; shift ;;
    --refusals) REFUSALS=1; shift ;;
    *) echo "corpus-gate: unknown option $1" >&2; exit 2 ;;
  esac
done

if [ -z "$CONFIGS" ]; then
  CONFIGS=$(cd "$HERE/configs" && ls *.json | sed 's/\.json$//' | tr '\n' ' ')
fi
if [ -z "$OUT" ]; then
  OUT=$(mktemp -d "${TMPDIR:-/tmp}/csff-gate.XXXXXX")
fi
mkdir -p "$OUT" "$WORK"

if [ -z "$CORPUS" ]; then
  echo "corpus-gate: pass --corpus <a dotnet/runtime checkout>" >&2
  exit 2
fi
if [ ! -d "$CORPUS" ]; then
  echo "corpus-gate: no corpus at $CORPUS" >&2
  exit 2
fi

if [ -z "$CLI" ]; then
  echo "corpus-gate: publishing the native CLI"
  ( cd "$ROOT" && dotnet build -t:Native -c Release ) > "$OUT/native-build.log" 2>&1
  if [ $? -ne 0 ]; then
    echo "corpus-gate: native publish failed, see $OUT/native-build.log" >&2
    exit 2
  fi
  CLI=$ROOT/out/csff/bin/Csff.Cli
fi
if [ ! -x "$CLI" ]; then
  echo "corpus-gate: $CLI is not executable" >&2
  exit 2
fi

echo "corpus-gate: building the adjudicator"
( cd "$ROOT" && dotnet build tests/Csff.Gate/Csff.Gate.fsproj -c Release ) > "$OUT/gate-build.log" 2>&1
if [ $? -ne 0 ]; then
  echo "corpus-gate: adjudicator build failed, see $OUT/gate-build.log" >&2
  exit 2
fi
GATE=$ROOT/tests/Csff.Gate/bin/Release/net11.0/Csff.Gate.dll

if ! (
  set -o pipefail
  cd "$CORPUS" &&
  find . \( -type f -o -type l \) -name '*.cs' -print0 \
    | LC_ALL=C sort -z \
    | xargs -0 shasum -a 256 \
    | shasum -a 256
) > "$OUT/corpus-identity"; then
  echo "corpus-gate: failed to hash corpus at $CORPUS" >&2
  exit 2
fi
CORPUS_FILES=$(cd "$CORPUS" && find . \( -type f -o -type l \) -name '*.cs' | wc -l | tr -d ' ')
CORPUS_HASH=$(cut -d' ' -f1 "$OUT/corpus-identity")
echo "corpus-gate: corpus $CORPUS files=$CORPUS_FILES identity=${CORPUS_HASH:0:16}"
echo "corpus-gate: cli $CLI"
echo "corpus-gate: reports in $OUT"

FAILED=0

compare_set() {
  local label=$1 config=$2 produced=$3 pinned=$4
  if [ "$UPDATE" = "1" ]; then
    mkdir -p "$HERE/pins/$config"
    cp "$produced" "$pinned"
    echo "  $label: pinned $(wc -l < "$produced" | tr -d ' ') entries"
    return 0
  fi
  if [ ! -f "$pinned" ]; then
    echo "  $label: FAIL no pin at $pinned ($(wc -l < "$produced" | tr -d ' ') entries produced)" >&2
    FAILED=1
    return 1
  fi
  if diff -q "$pinned" "$produced" > /dev/null; then
    echo "  $label: $(wc -l < "$produced" | tr -d ' ') entries, matches pin"
  else
    echo "  $label: FAIL pinned set changed" >&2
    diff "$pinned" "$produced" | head -40 >&2
    FAILED=1
  fi
}

cli_run_ok() {
  local run_status=$1 verb=$2 log=$3
  case $run_status in
    0|1|3)
      grep -Eq "^${verb} [0-9]+ C# files in " "$log"
      return $?
      ;;
    *)
      return 1
      ;;
  esac
}

cleanup_work() {
  if [ "$KEEP" = "0" ]; then
    rm -rf "$1"
  fi
}

for config in ${=CONFIGS}; do
  CFG=$HERE/configs/$config.json
  if [ ! -f "$CFG" ]; then
    echo "corpus-gate: no configuration $CFG" >&2
    FAILED=1
    continue
  fi

  mkdir -p "$OUT/$config" "$HERE/pins/$config"
  W=$WORK/$config
  rm -rf "$W"
  cp -Rc "$CORPUS" "$W" 2> /dev/null || cp -R "$CORPUS" "$W"

  echo "== $config: $(tr -d '\n' < "$CFG")"

  "$CLI" --no-cache --jobs "$JOBS" --config-path "$CFG" "$W" > "$OUT/$config/format.log" 2>&1
  FORMAT_STATUS=$?
  if ! cli_run_ok "$FORMAT_STATUS" "Formatted" "$OUT/$config/format.log"; then
    echo "  csff write pass failed (exit $FORMAT_STATUS), see $OUT/$config/format.log" >&2
    FAILED=1
    cleanup_work "$W"
    continue
  fi
  grep -E "^$W/.*: " "$OUT/$config/format.log" | sed "s|^$W/||" | sort > "$OUT/$config/refused.txt"
  grep "could not be proven" "$OUT/$config/refused.txt" > "$OUT/$config/unverified.txt" || true
  grep -v "could not be proven" "$OUT/$config/refused.txt" > "$OUT/$config/errors.txt" || true
  tail -1 "$OUT/$config/format.log" | sed 's/^/  /'

  echo "  csff exit=$FORMAT_STATUS errors=$(wc -l < "$OUT/$config/errors.txt" | tr -d ' ')" \
    "unverified=$(wc -l < "$OUT/$config/unverified.txt" | tr -d ' ')"

  CSFF_DECLINES=1 CSFF_ROSLYNSTATS=1 "$CLI" --check --no-cache --jobs "$JOBS" \
    --config-path "$CFG" "$CORPUS" > "$OUT/$config/census.log" 2>&1
  CENSUS_STATUS=$?
  if ! cli_run_ok "$CENSUS_STATUS" "Checked" "$OUT/$config/census.log"; then
    echo "  csff census pass failed (exit $CENSUS_STATUS), see $OUT/$config/census.log" >&2
    FAILED=1
    cleanup_work "$W"
    continue
  fi
  grep '^verification-decline ' "$OUT/$config/census.log" \
    | sed "s|$CORPUS/||" | awk '{print $3 "\t" $2}' | sort > "$OUT/$config/declines.txt"
  grep '^roslynstats ' "$OUT/$config/census.log" | sed 's/^/  /'

  dotnet "$GATE" --before "$CORPUS" --after "$W" --label "$config" --jobs "$JOBS" \
    --symbol-budget "$BUDGET" --report "$OUT/$config/findings.txt" \
    --pins "$HERE/pins/$config/disagreements.txt" > "$OUT/$config/gate.log" 2>&1
  GATE_STATUS=$?
  if [ "$GATE_STATUS" != "0" ] && [ "$GATE_STATUS" != "1" ]; then
    echo "  adjudicator failed (exit $GATE_STATUS), see $OUT/$config/gate.log" >&2
    FAILED=1
    cleanup_work "$W"
    continue
  fi
  grep -E '^gate |^  ' "$OUT/$config/gate.log" | head -12 | sed 's/^/  /'
  cut -f1,2 "$OUT/$config/findings.txt" | sort -u > "$OUT/$config/disagreements.txt"

  if [ "$REFUSALS" = "1" ]; then
    CSFF_GATE_CORPUS=$CORPUS CSFF_GATE_REFUSED=$OUT/$config/refused.txt \
      CSFF_GATE_CONFIG=$CFG \
      dotnet run --project "$ROOT/tests/Csff.Tests" -c Release -- \
      --filter-test-case "refused corpus files" --no-spinner --colours 0 \
      > "$OUT/$config/refusals.log" 2>&1
    grep -A200 'refused files adjudicated' "$OUT/$config/refusals.log" \
      | grep -v '^\[' | sed 's/^/  /' | head -60
  fi

  compare_set "corpus errors" "$config" "$OUT/$config/errors.txt" "$HERE/pins/$config/errors.txt"
  compare_set "unverified files" "$config" "$OUT/$config/unverified.txt" "$HERE/pins/$config/unverified.txt"
  compare_set "declines" "$config" "$OUT/$config/declines.txt" "$HERE/pins/$config/declines.txt"
  compare_set "disagreements" "$config" "$OUT/$config/disagreements.txt" "$HERE/pins/$config/disagreements.txt"

  if [ "$GATE_STATUS" != "0" ] && [ "$UPDATE" != "1" ]; then
    echo "  adjudication: FAIL (exit $GATE_STATUS)" >&2
    grep '^gate: ' "$OUT/$config/gate.log" | head -20 >&2
    FAILED=1
  fi

  cleanup_work "$W"
done

if [ "$FAILED" = "0" ]; then
  echo "corpus-gate: PASS (reports in $OUT)"
else
  echo "corpus-gate: FAIL (reports in $OUT)" >&2
fi
exit $FAILED
