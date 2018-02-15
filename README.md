# Formalization of typed actors with selective receive

The source code for my Master's Thesis.  
The work takes inspiration from the lambda-calculus λact, 
defined in [Mixing Metaphors: Actors as Channels and Channels as Actors](https://arxiv.org/abs/1611.06276),
and aims to provide a formalization of type safe Erlang-like actors.
In my formalization Actors are modelled as indexed monads,
in a style inspired by Effects from Idris and Koen Claessen's Poor Man's Concurrency Monad.


| Dependency       | Version                                  |
|------------------|------------------------------------------|
| Agda             | 2.5.3                                    |
| standard-library | f6ae4f7ffe70e9f3f9c028fe341f7af91439d3a3 |

| File                  | Description                                              |
|-----------------------|----------------------------------------------------------|
| Simulate              | The main worker. Simulates the steps of an environment   |
| Runtime               | Converts a simulation to IO                              |
| ActorMonad            | The embedding you use to create different actor programs |
| SimulationEnvironment | The datastructures and proofs used in the simulation     |
| EnvironmentOperations | Functions modifying the simulation environment           |
| unused                | Old code I didn't want to throw away yet                 |
