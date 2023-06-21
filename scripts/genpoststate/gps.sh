#!/usr/bin/env bash

set -e

TESTFILE="/tmp/test.json"

cp /dev/stdin ${TESTFILE}

alloc=$(jq -r '[.[]][0].pre' ${TESTFILE})
env=$(jq -r '[.[]][0].env' ${TESTFILE})
txs=$(jq -r '[.[]][0].transaction | def hex(x): x | sub("^0x0*"; "0x") | sub("^0x$"; "0x0");

def hex_to_num(x): x[2:] | tonumber;

[ [ {
    input: .data[],
    gas: hex(.gasLimit[0]),
    gasPrice: hex(.gasPrice),
    nonce: .nonce,
    to: .to,
    value: hex(.value[0]),
    v: "0x0",
    r: "0x0",
    s: "0x0",
    secretKey: .secretKey,
    hash: "0x0000000000000000000000000000000000000000000000000000000000000000",
    sender: .sender
} ] | to_entries[] | .value.nonce = "0x\(hex_to_num(.value.nonce)+.key)" | .value ]' "${TESTFILE}")

printf "$alloc\n" > alloc.json
printf "$env\n" > env.json
printf "$txs\n" > txs.json

./evm t8n &> /dev/null

echo $(jq --sort-keys -r '
def lpadhex(n):
(if (. != null) then .[2:] else "" end) | "0x" + if (n > length) then ((n - length) * "0") + . else . end;

[ to_entries[] | { "\(.key)": {
    code: (if (.value.code == null) then "0x" else .value.code end),
    storage: (
        if (.value.storage == null or .value.storage == {}) then {}
        else (.value.storage | to_entries[] | { "\(.key | lpadhex(64))": (.value | lpadhex(64)) } ) end),
    balance: (.value.balance? | lpadhex(64)),
    nonce: (.value.nonce? | lpadhex(64))
} } ] | add' alloc.json)
