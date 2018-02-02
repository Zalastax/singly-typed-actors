# Formalization of typed actors with selective receive

The source code for my Master's Thesis.  
The work takes inspiration from the lambda-calculus λact, defined in [Mixing Metaphors: Actors as Channels and Channels as Actors](https://arxiv.org/abs/1611.06276), and aims to provide a formalization of type safe Erlang-like actors. In my formalization Actors are modelled as indexed monads, in a style inspired by Effects from Idris and Koen Claessen's Poor Man's Concurrency Monad.


| Dependency       | Version                                  |
|------------------|------------------------------------------|
| Agda             | 2.5.3                                    |
| standard-library | de23244a73d6dab55715fd5a107a5de805c55764 |
| agda-prelude     | 7a4160fc7a1ee07b09afc2c68d27b58ce0b9962a |
