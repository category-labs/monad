#!/usr/bin/env bash

set -x
set -e

TESTFILE=$(mktemp)

file_name="$1"
cp "$file_name" "${TESTFILE}"


dump_output() {
	cat env.json
	cat post.json
	cat prestate.json
	cat result.json
	cat txs.json
	cat ./*.jsonl
}

fork_name="${2^}"
transaction_index="$3"
expected_state_root=$(jq '[.[]][0].post.'${fork_name}'['$transaction_index'].hash' "$TESTFILE")

output=$(jq -r '[.[]][0].post.'${fork_name}'['$transaction_index'].indexes | .data, .gas, .value' "${TESTFILE}")

readarray -t lines <<<"$output"
transaction_data_index="${lines[0]}"
transaction_gas_index="${lines[1]}"
transaction_value_index="${lines[2]}"

t8n_input=$(jq -c '{alloc: ([.[]][0].pre), env: ([.[]][0].env), txs: ([[.[]][0].transaction |
         def hex(x): x | sub("^0x0*"; "0x") | sub("^0x$"; "0x0");
         def hex_to_num(x): x[2:] | tonumber;
         [
             {
               input: .data['"$transaction_data_index"'],
               gas: hex(.gasLimit['"$transaction_gas_index"']),
               gasPrice: (if has("gasPrice") then  hex(.gasPrice) else null end),
               maxFeePerGas: (if has("maxFeePerGas") then hex(.maxFeePerGas) else null end),
               maxPriorityFeePerGas: (if has("maxPriorityFeePerGas") then hex(.maxPriorityFeePerGas) else null end),
               nonce: hex(.nonce),
               to: .to,
               value: hex(.value['"$transaction_value_index"']),
               v: "0x0",
               r: "0x0",
               s: "0x0",
               secretKey: .secretKey,
               hash: "0x0000000000000000000000000000000000000000000000000000000000000000",
               sender: .sender,
               accessList: .accessLists['"$transaction_data_index"']
             }
         ] |
         to_entries[] |
         .value |
         if .to == "" then del(.to) else . end |
         if .accessList == null then del(.accessList) else . end |
         if .gasPrice == null then del(.gasPrice) else . end |
         if .maxFeePerGas == null then del(.maxFeePerGas) else . end |
         if .maxPriorityFeePerGas == null then del(.maxPriorityFeePerGas) else . end
      ])}' "${TESTFILE}")

echo "$t8n_input" | jq -r .alloc >prestate.json
echo "$t8n_input" | jq -r .env >env.json
echo "$t8n_input" | jq -r .txs >txs.json

TEMP_ENV=$(mktemp)

if [[ "$fork_name" == "Frontier" ]] ||
	[[ "$fork_name" == "Homestead" ]] ||
	[[ "$fork_name" == "EIP150" ]] ||
	[[ "$fork_name" == "EIP158" ]] ||
	[[ "$fork_name" == "Byzantium" ]] ||
	[[ "$fork_name" == "Constantinople" ]] ||
	[[ "$fork_name" == "ConstantinopleFix" ]] ||
	[[ "$fork_name" == "Istanbul" ]] ||
	[[ "$fork_name" == "MuirGlacier" ]] ||
	[[ "$fork_name" == "FrontierToHomesteadAt5" ]] ||
	[[ "$fork_name" == "HomesteadToEIP150At5" ]] ||
	[[ "$fork_name" == "HomesteadToDaoAt5" ]] ||
	[[ "$fork_name" == "EIP158ToByzantiumAt5" ]] ||
	[[ "$fork_name" == "ByzantiumToConstantinopleAt5" ]] ||
	[[ "$fork_name" == "ByzantiumToConstantinopleFixAt5" ]] ||
	[[ "$fork_name" == "ConstantinopleFixToIstanbulAt5" ]] ||
	[[ "$fork_name" == "Berlin" ]] ||
	[[ "$fork_name" == "BerlinToLondonAt5" ]] ||
	[[ "$fork_name" == "London" ]]; then
	# currentRandom must not exist before merge to prevent t8n from choosing the wrong instruction table
	jq 'del(.currentRandom)' env.json >"$TEMP_ENV"
	mv "$TEMP_ENV" env.json
fi

if [ "$fork_name" == "Merge" ] || [ "$fork_name" == "Shanghai" ]; then
	# difficulty post merge must be zero or omitted in order for t8n to not exit
	jq 'del(.currentDifficulty)' env.json >"$TEMP_ENV"
	mv "$TEMP_ENV" env.json
fi

if [ "$fork_name" == "Shanghai" ]; then
	# Shanghai needs an empty withdrawals section in order for t8n to not exit
	jq '. += {withdrawals: []}' env.json >"$TEMP_ENV"
	mv "$TEMP_ENV" env.json
fi

$(which evm) t8n \
	--state.reward 0 \
	--state.chainid 1 \
	--trace \
	--state.reward 0 \
	--input.alloc prestate.json \
	--input.txs txs.json \
	--state.fork "$fork_name" \
	--output.alloc post.json \
	--output.result result.json # &>/dev/null

printf "\n" >>post.json
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

rm "$TESTFILE"

exit $return_code