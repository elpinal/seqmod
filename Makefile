mlkit: make_parser.sml
	mlkit --output seqmod-mlkit seqmod.mlb

mlton: make_parser.sml
	mlton -output seqmod-mlton -default-ann 'warnUnused true' -default-ann 'allowExtendedTextConsts true' seqmod.mlb

make_parser.sml: make_parser.cmyacc
	cmyacc -o make_parser.sml make_parser.cmyacc

test: mlkit
	go run test.go

update-test: mlkit
	go run test.go -update

.PHONY: mlkit mlton test update-test
