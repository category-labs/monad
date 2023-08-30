set -e

while IFS= read -r -d '' file
do
  echo "$file";
  forks=$(jq '[.[]][0].post | keys | .[]' -r $file)
  for fork in $(jq '[.[]][0].post | keys | .[]' -r "$file"); do
    num_transactions=$(jq '[.[]][0].post.'$fork' | length' "$file")
    for index in $(seq 0 $((num_transactions - 1))); do
      echo $file $fork $index
      ./scripts/genpoststate/wrap_gps.sh "$file" "$fork" "$index" > /dev/null
    done
  done

done < <(find ./third_party/ethereum-tests/GeneralStateTests -name '*.json' -print0)