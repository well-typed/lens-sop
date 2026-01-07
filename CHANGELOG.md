# Change log

## 0.3.1 -- 2026-01-07

* Support `ghc-9.12` (Alexandre Esteves, #7) and `ghc-9.14` (#8)
* Drop unnecessary dependency on `transformers`

## 0.3 -- 2023-02-22

This release modernizes the library a bit (breaking backwards compatibility):
instead of providing interoperability with `fclabels`, it instead uses
`optics-core`, and instead of using arrows, it uses monads.
