module Runtime where
open import Simulate
open import SimulationEnvironment

open import Data.Colist using (Colist ; [] ; _∷_)
open import Data.List using (List ; _∷_ ; [] ; map ; length)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String ; _++_)
open import Data.Unit using (⊤ ; tt)

open import Coinduction using (∞ ; ♯_ ; ♭)
import IO

Logger = (ℕ → EnvStep → IO.IO ⊤)

runEnv : Logger → Env → IO.IO ⊤
runEnv logger env = loop 1 (simulate env)
  where
    loop : ℕ → Colist EnvStep → IO.IO ⊤
    loop n [] = IO.putStrLn ("Done after " ++ (show n) ++ " steps.")
    loop n (x ∷ xs) = ♯ logger n x IO.>> ♯ loop (suc n) (♭ xs)

open EnvStep
open Env

showTrace : Trace → String
showTrace (Return name) = show name ++ " returned"
showTrace (Bind trace) = "Bind [ " ++ showTrace trace ++ " ]"
showTrace (BindDouble name) = "Bind " ++ (show name)
showTrace (Spawn spawner spawned) = (show spawner) ++ " spawned " ++ (show spawned)
showTrace (SendValue sender receiver) = (show sender) ++ " sent a value to " ++ (show receiver)
showTrace (SendReference sender receiver reference) = (show sender) ++ " sent a reference to " ++ (show receiver) ++ " forwarding " ++ (show reference)
showTrace (Receive name Nothing) = (show name) ++ " received nothing. It was put in the blocked list"
showTrace (Receive name Value) = (show name) ++ " received a value"
showTrace (Receive name (Reference reference)) = (show name) ++ " received a reference to " ++ (show reference)
showTrace (Receive name Dropped) = (show name) ++ " received something, but had no bind. It was dropped"
showTrace (TLift name) = (show name) ++ " was lifted"
showTrace (Self name) = (show name ++ " used self")

logTrace : Trace → IO.IO ⊤
logTrace trace = IO.putStrLn (showTrace trace ++ ".")

logInboxCount : List Inbox → IO.IO ⊤
logInboxCount inbs = IO.putStrLn ("There are " ++ (show (Data.List.length inbs)) ++ " inboxes.")

logMessageCounts : List Inbox → IO.IO ⊤
logMessageCounts [] = IO.return _
logMessageCounts (x ∷ xs) = ♯ IO.putStrLn ("Inbox #" ++ show (Inbox.name x) ++ " has " ++ (show (Data.List.length (Inbox.inb x))) ++ " messages.") IO.>> ♯ logMessageCounts xs

logInboxes : List Inbox → IO.IO ⊤
logInboxes inbs = ♯ logInboxCount inbs IO.>> ♯ logMessageCounts inbs

log-actors+blocked : Env → IO.IO ⊤
log-actors+blocked env = IO.putStrLn ("[A : " ++ show (length (acts env)) ++ " , B : " ++ show (length (blocked env)) ++ "]")


count-logger : Logger
count-logger n step = IO.putStrLn ((show n))

trace-logger : Logger
trace-logger n step = logTrace (trace step)

trace+inbox-logger : Logger
trace+inbox-logger n step = ♯ trace-logger n step IO.>> ♯ logInboxes (inbs (env step))

count+trace+inbox-logger : Logger
count+trace+inbox-logger n step = ♯ count-logger n step IO.>> ♯ trace+inbox-logger n step

actors-logger : Logger
actors-logger n step = log-actors+blocked (env step)

trace+actors-logger : Logger
trace+actors-logger n step = ♯ trace-logger n step IO.>> ♯ actors-logger n step
