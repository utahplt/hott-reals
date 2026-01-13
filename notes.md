- Auke Booij added some code for locators to the Coq-HoTT library in 2020
  - https://github.com/HoTT/Coq-HoTT/blob/master/theories/Analysis/Locator.v
- There is an unfinished draft PR for HoTT higher-inductive reals in the Agda
  cubical library
- TODO: find skyskimmers HIIT implementation
  - "Last I checked, we have SkySkimmer's implementation of the HoTT reals as an HIIT. I tried rebasing the inductive-recursive branch of coq a while ago that it relied on but ran into some issues. I also found out how sketchy the inner workings of that branch were, but obviously that is all experimental. So for now, those reals are stuck in the past."
  - I think they are here: https://github.com/SkySkimmer/HoTTClasses/tree/master/theories
  - This resulted in a paper:
    - https://dl.acm.org/doi/abs/10.1145/3018610.3018614?casa_token=HfndnsZGasUAAAAA:b1FWtLQ8p1aHoOTTQfRY4FSYN8mlNWm7o2kITZmk15_f5BWfJuA-Ar1BXGsdNcI5JgQlfU_go5k
  - Published at Certified Programs and Proofs in 2017
- From Booij: Remark 6.1.2. It should be possible to substitute for Q, throughout Chapters 6–9, the
  dyadic rationals, or other dense subsets of the reals satisfying suitable conditions, per-
  haps including approximate division as in Bauer and Taylor [13]. We use Q, rather than6.1. DEFINITION
  121 a computationally more convenient type, in order to stay close to the traditional mathematical development.

- What structure are we working on when we prove Lipschitz properties and such
  - It isn't a metric space because we need to reals for that
  - Booij premetric spaces but is there something more general?
  - Uniform spaces???
