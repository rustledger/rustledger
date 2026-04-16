#!/usr/bin/env bash
# Branch name validation for pre-push hook

BRANCH=$(git rev-parse --abbrev-ref HEAD)

# Skip for main branch or detached HEAD
if [ "$BRANCH" = "main" ] || [ "$BRANCH" = "HEAD" ]; then
  exit 0
fi

# Allow release-plz branches (e.g., release-plz-2026-01-18T17-10-14Z)
if [[ "$BRANCH" =~ ^release-plz- ]]; then
  echo "✅ Branch name '$BRANCH' is valid (release-plz)"
  exit 0
fi

# Standard branch naming pattern
PATTERN="^(feature|fix|docs|chore|refactor|release|hotfix|claude|dependabot|copilot|perf)/[a-zA-Z0-9][a-zA-Z0-9/_.-]*$"

if [[ "$BRANCH" =~ $PATTERN ]]; then
  echo "✅ Branch name '$BRANCH' is valid"
  exit 0
else
  echo "❌ Branch name '$BRANCH' does not match pattern"
  echo ""
  echo "Branch names must follow: <type>/<description>"
  echo "  Types: feature, fix, docs, chore, refactor, release, hotfix, claude, dependabot, copilot, perf"
  echo "  Description: letters, numbers, hyphens, underscores, slashes, dots"
  echo ""
  echo "Examples:"
  echo "  feature/add-csv-export"
  echo "  fix/balance-calculation"
  echo "  perf/winnow-parser"
  echo ""
  echo "Note: 'feat/' is NOT valid, use 'feature/' instead"
  exit 1
fi
