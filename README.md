# DschingisKhan

My study notes for applied mathematics.

# Build:

- With `make`:

```
coq_makefile -f _CoqProject *.v -o Makefile
make
```

- By hands:

```
coqc -Q . DschingisKhan theories/MyUtilities.v
coqc -Q . DschingisKhan theories/MyStructures.v
coqc -Q . DschingisKhan theories/DomainTheory.v
coqc -Q . DschingisKhan theories/ClassicalTheory.v
coqc -Q . DschingisKhan theories/UntypedLambdaCalculus.v
coqc -Q . DschingisKhan theories/SetTheory.v
```
