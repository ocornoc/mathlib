DEPLOY_NIGHTLY_GITHUB_USER=leanprover-community-bot

set -e
set -x

cd scripts
./mk_all.sh
lean --run mk_nolint.lean
./rm_all.sh

git add nolints.txt
git commit -m "chore(scripts): update nolints.txt" || true
git push origin-bot HEAD:master || true
