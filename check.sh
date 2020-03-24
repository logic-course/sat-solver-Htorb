#!/bin/bash

TIMEOUT=60s
filename=sat-solver

correct=0
incorrect=0
timeout=0
total=0
score=0

for test in ./tests/test*.txt; do
	[ -e "$test" ] || continue
	
	if [[ "$test" =~ ^./tests/test(.*).txt ]]
	then
		n="${BASH_REMATCH[1]}"
	else
		printf "no match\n"
	fi
	
	answer="tests/result$n.txt"
	
	echo -n "Running test $n..."

	# run the solver with a timeout
	result=$(cat "$test" | timeout -sHUP $TIMEOUT ./"$filename")

	if (( $? == 0 )) ; then

		#call the tester if the solution completed within the timeout value
		(cat "$test" && echo "" && cat "$answer" && echo "" && echo "$result" ) | ./tester

		if (( $? == 0 )) ; then
			echo "OK"
			correct=$((correct+1))
			score=$((score+1))
		else
			echo "FAIL"
			score=$((score-1))
			incorrect=$((incorrect+1))
		fi

	else
		echo "TIMEOUT"
		timeout=$((timeout+1))
	fi

	total=$((total+1))
done
	
result="$score = 1 * ($correct correct) - 1 * ($incorrect incorrect) + 0 * ($timeout timeout) [$total total]"

echo "Score: $result"
echo "$result" > "score.txt"