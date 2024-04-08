#!/bin/bash
echo "Rendering binary log $1 into text ..."
blkparse -i $1 -t | grep " C   R " > out.txt
