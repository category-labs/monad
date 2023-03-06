# Script for running monad_exe
usage() {
 cat <<HELP
   Usage: "$0" [ -d DATA_DIR ] [ -b BLOCKS ] [ -p PER_MONAD ]
   options:
    d: directory where the erigon block data is located
    b: how many monad blocks to run
    p: how many silkworm blocks inside one monad block
    h: usage information
HELP
}

DATA_DIR=${HOME}/erigon
PER_MONAD=200
STAGE_TIME=false

while getopts "d:b:p:h:t" option; do
  case "${option}" in
    d)
      DATA_DIR="${OPTARG}"
      ;;
    b)
      BLOCKS="${OPTARG}"
      ;;
    p)
      PER_MONAD="${OPTARG}"
      ;;
    t)
      STAGE_TIME=true
    ;;
    h)
      usage
			exit 0
      ;;
    *)
			usage
			exit 1
      ;;
  esac
done

# Reset Erigon
rm -rf $DATA_DIR
cp -a /space/ssd_4tb_4/hunsaker/erigon-14M $DATA_DIR
chmod -R u+w $DATA_DIR

# Run and time the program
start_at=$(date +%s,%N)
if $STAGE_TIME;
then
  ./build/tmpsrc/cmd/monad_exe --datadir "${DATA_DIR}" --blocks $BLOCKS --per-monad $PER_MONAD --time-it
else
  ./build/tmpsrc/cmd/monad_exe --datadir "${DATA_DIR}" --blocks $BLOCKS --per-monad $PER_MONAD
fi
end_at=$(date +%s,%N)

# Calculate time per block
_s1=$(echo $start_at | cut -d',' -f1)   
_s2=$(echo $start_at | cut -d',' -f2) 
_e1=$(echo $end_at | cut -d',' -f1)
_e2=$(echo $end_at | cut -d',' -f2)
time_cost=$(bc <<< "scale=3; $((($_e1 - $_s1)/$BLOCKS)) + ($_e2 -$_s2)/$((1000000000 * $BLOCKS))")
echo $time_cost "s/monad block"