#!/usr/bin/env bash
# Branch name validation for pre-push hook
#
# When used as a pre-push hook, validates the branch(es) actually being pushed
# (read from stdin), not just HEAD. Falls back to HEAD if stdin is empty
# (e.g., when run manually).

PATTERN="^(feat|feature|fix|docs|chore|refactor|release|hotfix|claude|dependabot|copilot|perf)/[a-zA-Z0-9][a-zA-Z0-9/_.-]*$"

validate_branch() {
  local branch="$1"

  # Skip main branch or detached HEAD
  if [ "$branch" = "main" ] || [ "$branch" = "HEAD" ] || [ -z "$branch" ]; then
    return 0
  fi

  # Allow release-plz branches (e.g., release-plz-2026-01-18T17-10-14Z)
  if [[ "$branch" =~ ^release-plz- ]]; then
    echo "✅ Branch name '$branch' is valid (release-plz)"
    return 0
  fi

  if [[ "$branch" =~ $PATTERN ]]; then
    echo "✅ Branch name '$branch' is valid"
    return 0
  else
    echo "❌ Branch name '$branch' does not match pattern"
    echo ""
    echo "Branch names must follow: <type>/<description>"
    echo "  Types: feat, feature, fix, docs, chore, refactor, release, hotfix, claude, dependabot, copilot, perf"
    echo "  Description: letters, numbers, hyphens, underscores, slashes, dots"
    echo ""
    echo "Examples:"
    echo "  feat/add-csv-export"
    echo "  feature/add-csv-export"
    echo "  fix/balance-calculation"
    echo "  perf/winnow-parser"
    return 1
  fi
}

# When used as a pre-push hook, stdin contains lines of:
#   <local ref> <local sha> <remote ref> <remote sha>
# Extract the branch names from the local refs being pushed.
if [ ! -t 0 ]; then
  # Reading from stdin (pre-push hook)
  exit_code=0
  while read -r local_ref _local_sha _remote_ref _remote_sha; do
    # Extract branch name from refs/heads/branch-name
    branch="${local_ref#refs/heads/}"
    if ! validate_branch "$branch"; then
      exit_code=1
    fi
  done
  exit $exit_code
else
  # Run manually — validate HEAD
  BRANCH=$(git rev-parse --abbrev-ref HEAD)
  validate_branch "$BRANCH"
fi
