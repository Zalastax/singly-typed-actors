module Examples.Main where
import Examples.PingPong as PingPong
open import Runtime
open import SimulationEnvironment
import IO

spawnerEnv = singleton-env PingPong.spawner

main = IO.run (run-env trace+actors-logger  spawnerEnv)