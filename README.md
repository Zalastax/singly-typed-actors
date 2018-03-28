# Formalization of typed actors with selective receive

The source code for my Master's Thesis.  
The work takes inspiration from the lambda-calculus λact, 
defined in [Mixing Metaphors: Actors as Channels and Channels as Actors](https://arxiv.org/abs/1611.06276),
and aims to provide a formalization of type safe Erlang-like actors.
In my formalization Actors are modelled as indexed monads,
in a style inspired by Effects from Idris and Koen Claessen's Poor Man's Concurrency Monad.


| Dependency       | Version                                  |
|------------------|------------------------------------------|
| Agda             | 8a7ad7f79c09d3a55110b6f92ab07267564601f0 |
| standard-library | 2a40a031e40042e72e245cce17956e5df49fcdd5 |

## How to build?
Agda and the standard library are nightlies for Agda 2.5.4.
The simplest way to build Agda is to clone the repo and run
`stack install --stack-yaml stack-8.2.2.yaml`.
The nightlies are used to get do-notation and solve some bugs with codata.

The project itself can be built with make or using agda-mode in emacs.
Latex files can be generated with `make latex`, but most of the thesis is kept in ShareLatex.

## Project structure

| File                  | Description                                              |
|-----------------------|----------------------------------------------------------|
| Simulate              | The main worker. Simulates the steps of an environment   |
| Runtime               | Converts a simulation to IO                              |
| ActorMonad            | The embedding you use to create different actor programs |
| SimulationEnvironment | The datastructures and proofs used in the simulation     |
| EnvironmentOperations | Functions modifying the simulation environment           |
| Examples              | Showcases patterns and code used in the thesis           |
| Selective             | Selective receive as a primary operation                 |
| unused                | Old code I didn't want to throw away yet                 |
