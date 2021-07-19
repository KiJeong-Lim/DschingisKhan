# DschingisKhan

My study notes for applied mathematics.

# Build

- With `make`:

```
coq_makefile -f _CoqProject *.v -o Makefile
make
```

- By hands:

```
coqc -Q . DschingisKhan pure/MyUtilities.v
coqc -Q . DschingisKhan pure/MyStructures.v
coqc -Q . DschingisKhan pure/DomainTheory.v
coqc -Q . DschingisKhan pure/UntypedLambdaCalculus.v
coqc -Q . DschingisKhan pure/SetTheory.v
coqc -Q . DschingisKhan classical/MyAxioms.v
coqc -Q . DschingisKhan classical/DomainTheory.v
```
