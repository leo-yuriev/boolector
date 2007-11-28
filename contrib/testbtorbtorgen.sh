#!/bin/bash
i=0
while true 
do 
  ((i++))
  echo -n "Test "$i": "
  btorgen 2> /dev/null > /tmp/test.btor
  boolector -rwl1 -rl 100000 /tmp/test.btor 
  retval=$?
  if [[ retval -ne 2 ]] && [[ retval -ne 3 ]]; then
    echo "ERROR"
    cp /tmp/test.btor ./error.btor
    exit
  fi
done
