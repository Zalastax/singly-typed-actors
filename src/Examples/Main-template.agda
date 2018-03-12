module Examples.Main-generated where
import Examples.PingPong as PingPong
import Examples.InfiniteBind as InfiniteBind
import Examples.SelectiveReceive as SelectiveReceive
open import Runtime
open import SimulationEnvironment
import IO

pingpongEntry = singleton-env PingPong.spawner
infinitebindEntry = singleton-env InfiniteBind.binder
selectiveReceiveEntry = singleton-env SelectiveReceive.spawner

main = IO.run (run-env trace+actors-logger __ENTRY__)