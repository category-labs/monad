#!/bin/bash
set -x
set -e

REPO_URL=https://github.com/monad-crypto/monad
DATE=$(date +"%m_%d_%Y")
SUMMARY_FILENAME=summary_${DATE}.html
COMPLETE_RESULTS_FILENAME=complete_results_${DATE}.html

ARGS='--repo_url '${REPO_URL}' --commit '${CURRENT_COMMIT}' --date '${DATE}

python3 ./scripts/ethereum-tests/render_results.py $ARGS --file results.json --summary >${SUMMARY_FILENAME}
python3 ./scripts/ethereum-tests/render_results.py $ARGS --file results.json >${COMPLETE_RESULTS_FILENAME}
python3 ./scripts/ethereum-tests/send_mail.py ${ARGS} \
	--gmail_user ${GMAIL_APP_USER} \
	--gmail_password ${GMAIL_APP_PASSWORD} \
	--summary ${SUMMARY_FILENAME} \
	--complete_results ${COMPLETE_RESULTS_FILENAME}
