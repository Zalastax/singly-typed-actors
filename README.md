# Formalization of typed actors with selective receive

The source code for my Master's Thesis.  
The work takes inspiration from the lambda-calculus λact, 
defined in [Mixing Metaphors: Actors as Channels and Channels as Actors](https://arxiv.org/abs/1611.06276),
and aims to provide a formalization of type safe Erlang-like actors.
In my formalization Actors are modelled as parameterized monads,
in a style inspired by Effects from Idris and Koen Claessen's Poor Man's Concurrency Monad.


| Dependency       | Version                                  |
|------------------|---------|
| Agda             | 2.5.4.2 |
| standard-library | v0.17   |

## How to build?
You can follow [Agda's installation guide](http://agda.readthedocs.io/en/latest/getting-started/installation.html)
or build from source.
My preferred way is to to clone the repo, checkout the release-2.5.4.2 branch and run
`stack install --stack-yaml stack-8.2.2.yaml`.

The project itself can be built with make or using agda-mode in emacs.
Latex files can be generated with `make latex`, but most of the thesis is kept in ShareLatex.

## Project structure

| File                  | Description                                              |
|-----------------------|----------------------------------------------------------|
| Simulate              | The main worker. Simulates the steps of an environment   |
| Runtime               | Converts a simulation to IO                              |
| ActorMonad            | The embedding you use to create different actor programs |
| SimulationEnvironment | The data structures and proofs used in the simulation    |
| EnvironmentOperations | Functions modifying the simulation environment           |
| Examples              | Showcases patterns and code used in the thesis           |
| Selective             | Selective receive as a primary operation                 |
| unused                | Old code I didn't want to throw away yet                 |
