if [ "$1" = "-r" ]; then
    if grep "SKIP_PROOF_OFF" */*.v > /dev/null;
    then
	echo "Already turned off"
    else
	for file in */*.v;
	do
	    grep "SKIP_PROOF" "$file" > /dev/null &&
		sed -i '' -e 's/(\* SKIP_PROOF_ON/(\* SKIP_PROOF_OFF \*)/g' \
		    -e 's/END_SKIP_PROOF_ON \*) apply cheat\./(\* END_SKIP_PROOF_OFF \*)/g' "$file"
	done
    fi
else
    if grep "SKIP_PROOF_ON" */*.v > /dev/null;
    then
	echo "Already turned on"
    else
	for file in */*.v
	do
	    grep "SKIP_PROOF" "$file" > /dev/null &&
		sed -i '' -e 's/(\* SKIP_PROOF_OFF \*)/(\* SKIP_PROOF_ON/g' \
		    -e 's/(\* END_SKIP_PROOF_OFF \*)/END_SKIP_PROOF_ON \*) apply cheat\./g' "$file"
	done
    fi
fi

