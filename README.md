# seqmod

This repository presents a full implementation of F-ing Modules [Rossberg, Russo & Dreyer 2014].
By “full”, I mean it includes:

- the facility to package modules as first-class core values,
- (the novel) abstraction-safe applicative functors, and
- value and structure sharing.

In this implementation, the core language is an intuitionistic variant of polarized system L [Herbelin 2008; Munch-Maccagnoni 2009], which is computational interpretation of sequent calculus LK, pretending a call-by-name lambda calculus with Hindley-Milner type discipline.
By using polarized sequent calculus, it is possible to combine the eager module language and the lazy core language.

## Getting started

The program is implemented in Standard ML ’97, but only MLKit and MLton are supported
because other SML implementations does not support the ML Basis system.

Prerequisites:

- MLKit or MLton
- [cmyacc](http://www.cs.cmu.edu/~crary/cmtool/)

### Build with MLKit

```
$ make mlkit
$ ./seqmod-mlkit
```

### Build with MLton

```
$ make mlton
$ ./seqmod-mlton
```

## Examples

```
{
  ; + represents lazy sum.
  ; Like other lazy languages, this `bool` has 5 possible values,
  ; rather than 2, due to the bottom value.
  type bool = unit + unit
}
```

```
{
  signature S = {
    type t 'a

    ; & represents a lazy product.
    val foldl 'a 'b : ('a & 'b -> 'b) -> 'b -> t 'a -> 'b
  }
}
```

```
; An applicative functor.
fn X : {type t 'a} => {
  type u = X.t unit
}
```

### Packaged modules

```
{
  signature S = {
    type t
    val f : t -> t
  }

  val p = pack {type t = unit val f = fn x => x} : S

  module M = unpack p : S
}
```

```
; Unpacking makes the surrounding functor generative.
fn X : {} => unpack (pack {type t = unit} : {type t}) : {type t}
```

### Value and structure sharing

```
{
  signature S = {
    type t 'a
    type list 'a

    val to_asc_list 'a : t 'a -> list 'a
    val to_desc_list 'a : t 'a -> list 'a
    val to_list = to_asc_list
  }
}
```

```
{
  signature S = {
    module X : {
      type t
      val id : t -> t
    }
  }

  module M = {
    type u = unit
    type t = u & (u + u)
    val id = fn x => x
  }

  signature T = S where module X = M
  ; This is equivalent to:
  signature T = {
    module X : {
      type t = M.t
      val id : t -> t
    } where val id = M.id
  }
}
```

## References

### F-ing modules

Rossberg, Russo and Dreyer. JFP, 2014.

### Duality of computation and sequent calculus: a few more remarks

Herbelin. Manuscript, 2008.

### Focalisation and classical realisability

Munch-Maccagnoni. CSL, 2009.
