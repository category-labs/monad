#!/usr/bin/env bash

set -e

capitalize_first_letter() {
	local input="$1"
	local first_letter="$(echo "${input:0:1}" | tr '[:lower:]' '[:upper:]')"
	local rest="${input:1}"
	echo "${first_letter}${rest}"
}

dump_output() {
	env=$(jq -c '' env.json)
	poststate=$(jq -c '' post.json)
	prestate=$(jq -c '' prestate.json)
	result=$(jq -c '' result.json)
	txs=$(jq -c '' txs.json)
	json_string=$(jq -n \
		--argjson env "$env" \
		--argjson prestate "$prestate" \
		--argjson poststate "$poststate" \
		--argjson result "$result" \
		--slurpfile trace *.jsonl \
		--argjson txs "$txs" \
		'{env: $env, prestate: $prestate, poststate: $poststate, result: $result, trace: $trace, txs: $txs}')

	echo $json_string | jq -c
}

TESTFILE="/tmp/test.json"

cp /dev/stdin ${TESTFILE}

fork_name="$1"
transaction_index="$2"
capitalized_fork_name=$(capitalize_first_letter "$fork_name")
expected_state_root=$(jq '[.[]][0].post.'${capitalized_fork_name}'['$transaction_index'].hash' /tmp/test.json)
transaction_data_index=$(jq -r '[.[]][0].post.'${capitalized_fork_name}'['$transaction_index'].indexes.data' "${TESTFILE}")
transaction_gas_index=$(jq -r '[.[]][0].post.'${capitalized_fork_name}'['$transaction_index'].indexes.gas' "${TESTFILE}")
transaction_value_index=$(jq -r '[.[]][0].post.'${capitalized_fork_name}'['$transaction_index'].indexes.value' "${TESTFILE}")

alloc=$(jq -r '[.[]][0].pre' ${TESTFILE})
env=$(jq -r '[.[]][0].env' ${TESTFILE})
txs=$(jq -r '[.[]][0].transaction | def hex(x): x | sub("^0x0*"; "0x") | sub("^0x$"; "0x0");

def hex_to_num(x): x[2:] | tonumber;

[ [ {
    input: .data['"$transaction_data_index"'],
    gas: hex(.gasLimit['"$transaction_gas_index"']),
    gasPrice: hex(.gasPrice),
    nonce: .nonce,
    to: .to,
    value: hex(.value['"$transaction_value_index"']),
    v: "0x0",
    r: "0x0",
    s: "0x0",
    secretKey: .secretKey,
    hash: "0x0000000000000000000000000000000000000000000000000000000000000000",
    sender: .sender
} ] | to_entries[] | .value.nonce = "0x\(hex_to_num(.value.nonce))" |
                     .value |
                     if .to == "" then del(.to) else . end ]' "${TESTFILE}")

printf "$alloc\n" >prestate.json
printf "$env\n" >env.json
printf "$txs\n" >txs.json

if [[ "$fork_name" == "Frontier" ]] ||
	[[ "$fork_name" == "Homestead" ]] ||
	[[ "$fork_name" == "EIP158" ]] ||
	[[ "$fork_name" == "Byzantium" ]] ||
	[[ "$fork_name" == "Constantinople" ]] ||
	[[ "$fork_name" == "ConstantinopleFix" ]] ||
	[[ "$fork_name" == "Istanbul" ]] ||
	[[ "$fork_name" == "Berlin" ]] ||
	[[ "$fork_name" == "London" ]]; then
	# currentRandom must not exist before merge to prevent t8n from choosing the wrong instruction table
	jq 'del(.currentRandom)' env.json >/tmp/env.json
	mv /tmp/env.json env.json
fi

if [ "$fork_name" == "Merge" ] || [ "$fork_name" == "Shanghai" ]; then
	# difficulty post merge must be zero or omitted in order for t8n to not exit
	jq 'del(.currentDifficulty)' env.json >/tmp/env.json
	mv /tmp/env.json env.json
fi

if [ "$fork_name" == "Shanghai" ]; then
	# Shanghai needs an empty withdrawals section in order for t8n to not exit
	jq '. += {withdrawals: []}' env.json >/tmp/env.json
	mv /tmp/env.json env.json
fi

./evm t8n \
	--state.reward 0 \
	--state.chainid 1 \
	--trace \
	--state.reward 0 \
	--input.alloc prestate.json \
	--input.txs txs.json \
	--state.fork "$fork_name" \
	--output.alloc post.json \
	--output.result result.json # &>/dev/null

printf "\n" >>poststate.json
printf "\n" >>result.json

actual_state_root=$(jq '.stateRoot' result.json)

return_code=0

# they better match >:(
if [ "$expected_state_root" != "$actual_state_root" ]; then
	echo "Error: State root does not match"
	echo "Expected: $expected_state_root"
	echo "Actual: $actual_state_root"
	return_code=-1
fi

dump_output

exit $return_code
