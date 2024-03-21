for filename in ./*.smt2
do
	echo "${filename}"
	cvc5 "${filename}"
	time cvc5 --produce-models --dump-proofs --proof-format-mode=alethe --simplification=none --dag-thresh=0 --proof-granularity=theory-rewrite "${filename}" > /dev/null
	echo " "
	echo " "
done