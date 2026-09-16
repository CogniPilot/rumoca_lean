#!/usr/bin/env bash
set -euo pipefail
report=$1
test -s "$report"
# A final line without a newline is still audited.
while IFS= read -r line || [ -n "$line" ]; do
  case "$line" in
    *' depends on axioms: ['*']')
      names=${line#*'['}
      names=${names%']'}
      IFS=', ' read -r -a axioms <<< "$names"
      for axiom in "${axioms[@]}"; do
        case "$axiom" in
          propext|Classical.choice|Quot.sound) ;;
          *) printf 'unapproved Lean axiom: %s\n' "$axiom" >&2; exit 1 ;;
        esac
      done
      ;;
    *' does not depend on any axioms') ;;
    *) printf 'unexpected Lean audit output: %s\n' "$line" >&2; exit 1 ;;
  esac
done < "$report"
