#set -x
set -e

# preprocess
TMP_FILE=$(mktemp)
TMP_DIR="output"

generate_arguments() {
	file="$1"
	for fork in $(jq '[.[]][0].post | keys | .[]' -r "$file"); do
		num_transactions=$(jq '[.[]][0].post.'$fork' | length' "$file")
		for index in $(seq 0 $((num_transactions - 1))); do
			echo $file $fork $index
		done
	done
}

export -f generate_arguments
find ./third_party/ethereum-tests/GeneralStateTests -name '*.json' |
	grep -v stCreateTest/CreateOOGafterMaxCodesize |
	grep -v stQuadraticComplexityTest/Call50000_sha256 |
	grep -v stTimeConsuming/static_Call50000_sha256 |
	grep -v stTimeConsuming/CALLBlake2f_MaxRounds |
	grep -v "VMTests/vmPerformance.*" |
	grep -v stTransactionTest/HighGasPrice |
	grep -v stTransactionTest/ValueOverflow | shuf | parallel generate_arguments >"$TMP_FILE"

run_test() {
	IFS=' '
	read -ra lines <<<"$1"
	file="${lines[0]}"
	fork="${lines[1]}"
	index="${lines[2]}"
	filtered_file=$(echo "$file" | tr '/' '_' | tr '.' '_')

	log_dir='output/'"$filtered_file"'_'"$fork"'_'"$index"
	log_file="$log_dir"/log
	mkdir -p "$log_dir"
	{ ./scripts/genpoststate/wrap_gps.sh "$file" "$fork" "$index" 2>&1; } >> "$log_file"
	if [[ $? -eq 0 ]]; then
		echo "Test for fork '$file' '$fork' '$index' succeeded." | tee -a "$log_file"
	else
		echo "FAIL: Test for fork '$file' '$fork' '$index' failed. See '$log_file' for details." | tee -a "$log_file"
	fi
}

# export function so parallel can see it
export -f run_test

parallel_exit_code=0
# halt-on-error 0 = do not halt if a job fails, exit status will be the number of jobs failed
parallel -j 25 --halt-on-error 0 -a "$TMP_FILE" run_test
parallel_exit_code=$?

rm "$TMP_FILE"

echo "$TMP_DIR"

exit $parallel_exit_code
