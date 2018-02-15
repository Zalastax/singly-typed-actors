module Examples.Main where
import Examples.PingPong as PingPong
open import Runtime
open import SimulationEnvironment
import IO

spawnerEnv = singletonEnv PingPong.spawner

main = IO.run (runEnv trace+actors-logger  spawnerEnv)