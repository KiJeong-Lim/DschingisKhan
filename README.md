# DschingisKhan

> He Reiter, Ho Reiter, He Reiter, Immer weiter!

## QUICK START

```
git clone https://github.com/KiJeong-Lim/DschingisKhan.git
cd DschingisKhan
coq_makefile -f _CoqProject -o Makefile
make
```

## COMPATIBLE COQ VERSIONS

- With `The Coq Proof Assistant, version 8.14.0 compiled with OCaml 4.12.0`, everything works fine in `Windows 10`.

## THANKS TO

- `Junyoung Jang` https://github.com/Ailrun

- `Taeseung Sohn` https://github.com/paulsohn

- `Hanul Jeon` https://github.com/hanuljeon95

- `Soonwon Moon` https://github.com/damhiya

- `Minki Cho` https://github.com/minkiminki

## BUILD BY HANDS

```
coqc -Q . DschingisKhan pure/MyUtilities.v
coqc -Q . DschingisKhan pure/FunFacts.v
coqc -Q . DschingisKhan pure/MyStructures.
coqc -Q . DschingisKhan pure/BasicAlgebra.v
coqc -Q . DschingisKhan pure/DomainTheory.v
coqc -Q . DschingisKhan pure/UntypedLambdaCalculus.v
coqc -Q . DschingisKhan pure/AczelSet.v
coqc -Q . DschingisKhan pure/CBA.v
coqc -Q . DschingisKhan pure/MyCoin.v
coqc -Q . DschingisKhan classical/ExclusiveMiddle.v
coqc -Q . DschingisKhan classical/DomainTheory.v
coqc -Q . DschingisKhan projects/PropositionalLogic/Base.v
coqc -Q . DschingisKhan projects/PropositionalLogic/ConstructiveMetaTheories.v
coqc -Q . DschingisKhan projects/PropositionalLogic/ClassicalMetaTheories.v
coqc -Q . DschingisKhan projects/PropositionalLogic.v
coqc -Q . DschingisKhan projects/SmullyanGIT/PA.v
coqc -Q . DschingisKhan projects/SmullyanGIT.v
```

## THE LICENSE

```
This is free and unencumbered software released into the public domain.

Anyone is free to copy, modify, publish, use, compile, sell, or
distribute this software, either in source code form or as a compiled
binary, for any purpose, commercial or non-commercial, and by any
means.

In jurisdictions that recognize copyright laws, the author or authors
of this software dedicate any and all copyright interest in the
software to the public domain. We make this dedication for the benefit
of the public at large and to the detriment of our heirs and
successors. We intend this dedication to be an overt act of
relinquishment in perpetuity of all present and future rights to this
software under copyright law.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
OTHER DEALINGS IN THE SOFTWARE.

For more information, please refer to <https://unlicense.org>
```
