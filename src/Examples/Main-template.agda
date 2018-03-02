module Examples.Main-generated where
import Examples.PingPong as PingPong
import Examples.InfiniteBind as InfiniteBind
open import Runtime
open import SimulationEnvironment
import IO

pingpongEntry = singleton-env PingPong.spawner
infinitebindEntry = singleton-env InfiniteBind.binder

main = IO.run (run-env trace+actors-logger __ENTRY__)