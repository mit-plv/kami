#!/bin/bash

PLATFORM=`uname`
SED="sed -i"
if [[ "$PLATFORM" == 'Darwin' ]]; then
	SED="$SED .orig"
fi

if [ "$1" = "-r" ]; then
	for file in Kami/Ex/*.v;
	do
		echo "Setting SKIP_PROOF_OFF in $file"
		$SED -e 's/(\* SKIP_PROOF_ON/(\* SKIP_PROOF_OFF \*)/g' \
			-e 's/END_SKIP_PROOF_ON \*) apply cheat\./(\* END_SKIP_PROOF_OFF \*)/g' "$file"
	done
else
	for file in Kami/Ex/*.v
	do
		echo "Setting SKIP_PROOF_ON in $file"
		#grep "SKIP_PROOF" "$file" > /dev/null &&
		$SED -e 's/(\* SKIP_PROOF_OFF \*)/(\* SKIP_PROOF_ON/g' \
			-e 's/(\* END_SKIP_PROOF_OFF \*)/END_SKIP_PROOF_ON \*) apply cheat\./g' "$file"
	done
fi

rm -f */*.orig
