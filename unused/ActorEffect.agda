module ActorEffect where

open import Sublist
import IO
import IO.Primitive as Prim
open import Data.String using (String ; _++_)
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Unit using (⊤ ; tt)
open import Category.Monad using (RawMonad)
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List using (List ; _∷_ ; [] ; map)
open import Data.List.All using (All ; lookup ; _∷_ ; []) renaming (map to ∀map)
import Data.List.All.Properties as ∀Prop
open import Data.List.Properties using (∷-injective)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)
open import Membership-equality using (_∈_)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)
open import Data.Nat using (ℕ ; zero ; suc ; _≟_ ; _<_)
open import Data.Nat.Properties using (<⇒≢ )
open import Data.Nat.Show using (show)
open import Coinduction
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Prelude.Equality using (Eq ; _==_ ; cong)
open import Prelude.Nat using ()
open import ActorMonad public
open import RuntimeEnvironment public
open import EnvironmentOperations public

nName : Name → String
nName name = " " ++ show name

aName : Actor → String
aName x = nName (Actor.name x)

printInboxes : List Inbox → IO.IO ⊤
printInboxes inbs = ♯ printHeader IO.>> ♯ loop inbs
  where
    printHeader : IO.IO ⊤
    printHeader = IO.putStrLn ("There are " ++ (show (Data.List.length inbs)) ++ " inboxes.")
    loop : List Inbox → IO.IO ⊤
    loop [] = IO.return tt
    loop (x ∷ xs) = ♯ IO.putStrLn ("The inbox" ++ nName (Inbox.name x) ++ " has " ++ (show (Data.List.length (Inbox.inb x))) ++ " messages.") IO.>> ♯ loop xs

runEnv : ℕ → Env → IO.IO ⊤
-- ===== OUT OF STEPS =====
runEnv zero env = ♯ IO.putStrLn "Out of steps" IO.>> ♯ IO.return tt
runEnv (suc n) env with (Env.acts env) | (Env.actorsValid env)
-- ===== OUT OF ACTORS
runEnv (suc n) env | [] | _ = ♯ IO.putStrLn "Out of actors" IO.>> ♯ printInboxes (Env.inbs env)
runEnv (suc n) env | x ∷ acts | _ with (Actor.act x)
-- ===== Value =====
runEnv (suc n) env | x ∷ acts | _ | Value val = ♯ IO.putStrLn ("Value" ++ (aName x)) IO.>> ♯ runEnv n (dropTop env) -- Actor is done, just drop it
-- ===== Bind =====
runEnv (suc n) env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ acts | _ | m >>= f with (♭ m)
-- ===== Bind Value =====
runEnv (suc n) env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ acts | w ∷ ws | m >>= f |
  Value val = ♯ IO.putStrLn ("Bind Value" ++ nName name) IO.>> ♯ runEnv n (topToBack env')
  where
    env' : Env
    env' = (record
                        { acts = record
                                   { IS = IS
                                   ; A = A
                                   ; references = references
                                   ; es = es
                                   ; esEqRefs = esEqRefs
                                   ; ce = ce
                                   ; act = ♭ (f val)
                                   ; name = name
                                   } ∷ acts
                        ; blocked = Env.blocked env
                        ; inbs = Env.inbs env
                        ; store = Env.store env
                        ; inbs=store = Env.inbs=store env
                        ; freshName = Env.freshName env
                        ; actorsValid = record { hasInb = ValidActor.hasInb w ; points = ValidActor.points w } ∷ ws
                        ; blockedValid = Env.blockedValid env
                        ; messagesValid = Env.messagesValid env
                        ; nameIsFresh = Env.nameIsFresh env
                        })
-- ===== Bind Bind =====
runEnv (suc n) env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ acts | w ∷ ww | m >>= f |
  mm >>= g = ♯ IO.putStrLn ("Bind Bind" ++ nName name) IO.>> ♯ runEnv n (topToBack env')
  where
    bindAct : Actor
    bindAct = record
                { IS = IS
                ; A = A
                ; references = references
                ; es = es
                ; esEqRefs = esEqRefs
                ; ce = ce
                ; act = mm >>= λ a → ♯ (g a >>= f)
                ; name = name
                }
    bindActValid : ValidActor (Env.store env) bindAct
    bindActValid = record { hasInb = ValidActor.hasInb w ; points = ValidActor.points w }
    env' : Env
    env' = record
             { acts = bindAct ∷ acts
             ; blocked = Env.blocked env
             ; inbs = Env.inbs env
             ; store = Env.store env
             ; inbs=store = Env.inbs=store env
             ; freshName = Env.freshName env
             ; actorsValid = bindActValid ∷ ww
             ; blockedValid = Env.blockedValid env
             ; messagesValid = Env.messagesValid env
             ; nameIsFresh = Env.nameIsFresh env
             }
-- ===== Bind Spawn
runEnv (suc n) env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ acts | w ∷ ws | m >>= f |
  Spawn {NewIS} {B} {_} {ceN} bm = ♯ IO.putStrLn ("Bind Spawn from" ++ nName name ++ " spawning" ++ nName (Env.freshName env))  IO.>> ♯ runEnv n (topToBack env')
  where
    ∷-refl : ∀ {ls ls'} → ∀ x → ls ≡ ls' → x ∷ ls ≡ x ∷ ls'
    ∷-refl x p rewrite p = refl
    newInb : Inbox
    newInb = record { IS = NewIS ; inb = [] ; name = Env.freshName env }
    newAct : Actor
    newAct = record
               { IS = NewIS
               ; A = B
               ; references = []
               ; es = []
               ; esEqRefs = refl
               ; ce = ceN
               ; act = bm
               ; name = Env.freshName env
               }
    newStoreEntry : NamedInbox
    newStoreEntry = (Env.freshName env) , NewIS
    newStore : Store
    newStore = newStoreEntry ∷ Env.store env
    newIsFresh : NameFresh newStore (suc (Env.freshName env))
    newIsFresh = Data.Nat.s≤s (Data.Nat.Properties.≤-reflexive refl) ∷ ∀map Data.Nat.Properties.≤-step (Env.nameIsFresh env)
    bindAct : Actor
    bindAct = record
                { IS = IS
                ; A = A
                ; references = newStoreEntry ∷ references
                ; es = NewIS ∷ es
                ; esEqRefs = ∷-refl NewIS esEqRefs
                ; ce = ce
                ; act = ♭ (f _)
                ; name = name
                }
    bindActValid : ValidActor newStore bindAct
    bindActValid = record {
      hasInb = suc {pr = sucHelper (ValidActor.hasInb w) (Env.nameIsFresh env) }(ValidActor.hasInb w)
      ; points = zero ∷ ∀map (λ x₁ → suc {pr = sucHelper x₁ (Env.nameIsFresh env)} x₁) (ValidActor.points w) }
    newActValid : ValidActor newStore newAct
    newActValid = record {
      hasInb = zero
      ; points = [] }
    newInbs=newStore : newStore ≡ inboxesToStore (newInb ∷ Env.inbs env)
    newInbs=newStore rewrite (Env.inbs=store env) = refl
    -- Here it would have been nice to use addTop / another helper for updating an actor.
    -- The problem is that for it to work, the actor returned by 'f' needs to be added after the spawned actor, since it needs a proof that the new actor is in the environment
    -- That would equate to something like dropTop -> addTop bm -> addTop f.
    -- It seemed simpler to just do it manually instead
    env' : Env
    env' = record
             { acts = newAct ∷ bindAct ∷ acts
             ; blocked = Env.blocked env
             ; inbs = newInb ∷ Env.inbs env
             ; store = newStore
             ; inbs=store = newInbs=newStore
             ; freshName = suc (Env.freshName env)
             ; actorsValid = newActValid ∷ bindActValid ∷ ∀map (ValidActorSuc (Env.nameIsFresh env)) ws
             ; blockedValid = ∀map (ValidActorSuc (Env.nameIsFresh env)) (Env.blockedValid env)
             ; messagesValid = [] ∷ ∀map (λ {x} mv → messagesValidSuc {_} {x} (Env.nameIsFresh env) mv) (Env.messagesValid env)
             ; nameIsFresh = newIsFresh
             }
-- ===== Bind send value =====
runEnv (suc n) env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ acts | w ∷ ww | m >>= f |
  SendValue {ToIS = ToIS} canSendTo msg with (lookupReference w canSendTo)
... | toName , toRef = ♯ IO.putStrLn ("Bind Send Value from" ++ nName name ++ " to" ++ nName toName) IO.>> ♯ runEnv n (topToBack withUnblocked)
  where
    bindAct : Actor
    bindAct = record
                { IS = IS
                ; A = A
                ; references = references
                ; es = es
                ; esEqRefs = esEqRefs
                ; ce = ce
                ; act = ♭ (f _)
                ; name = name
                }
    bindActValid : ValidActor (Env.store env) bindAct
    bindActValid = record { hasInb = ValidActor.hasInb w ; points = ValidActor.points w }
    withM : Env
    withM = record
             { acts = bindAct ∷ acts
             ; blocked = Env.blocked env
             ; inbs = Env.inbs env
             ; store = Env.store env
             ; inbs=store = Env.inbs=store env
             ; freshName = Env.freshName env
             ; actorsValid = bindActValid ∷ ww
             ; blockedValid = Env.blockedValid env
             ; messagesValid = Env.messagesValid env
             ; nameIsFresh = Env.nameIsFresh env
             }
    addMsg : Σ (List (NamedMessage ToIS)) (All (messageValid (Env.store env))) →
             Σ (List (NamedMessage ToIS)) (All (messageValid (Env.store env)))
    addMsg (messages , allValid) = (MsgV msg ∷ messages) , tt ∷ allValid
    withUpdatedInbox : Env
    withUpdatedInbox = updateInboxEnv withM toRef addMsg
    withUnblocked : Env
    withUnblocked = unblockActor withUpdatedInbox toName
-- ===== Bind send reference =====
runEnv (suc n) env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ acts | w ∷ ww | m >>= f |
  SendReference {ToIS = ToIS} {FwIS = FwIS} canSendTo canForward msg =
    ♯ IO.putStrLn ("Bind Send Reference from" ++ nName name ++ " to" ++ nName (Σ.proj₁ toRef) ++ " forwarding" ++ nName (Σ.proj₁ fwRef)) IO.>>
    ♯ runEnv n (topToBack withUnblocked)
  where
    bindAct : Actor
    bindAct = record
                { IS = IS
                ; A = A
                ; references = references
                ; es = es
                ; esEqRefs = esEqRefs
                ; ce = ce
                ; act = ♭ (f _)
                ; name = name
                }
    bindActValid : ValidActor (Env.store env) bindAct
    bindActValid = record { hasInb = ValidActor.hasInb w ; points = ValidActor.points w }
    withM : Env
    withM = record
              { acts = bindAct ∷ acts
              ; blocked = Env.blocked env
              ; inbs = Env.inbs env
              ; store = Env.store env
              ; inbs=store = Env.inbs=store env
              ; freshName = Env.freshName env
              ; actorsValid = bindActValid ∷ ww
              ; blockedValid = Env.blockedValid env
              ; messagesValid = Env.messagesValid env
              ; nameIsFresh = Env.nameIsFresh env
              }
    fwRef : Σ[ name ∈ Name ] name ↦ FwIS ∈e (Env.store env)
    fwRef = lookupReference w canForward
    toRef : Σ[ name ∈ Name ] name ↦ ToIS ∈e (Env.store env)
    toRef = lookupReference w canSendTo
    addMsg : Σ (List (NamedMessage ToIS)) (All (messageValid (Env.store env))) →
      Σ (List (NamedMessage ToIS)) (All (messageValid (Env.store env)))
    addMsg (messages , allValid) = (MsgR msg (Σ.proj₁ fwRef) ∷ messages) , Σ.proj₂ fwRef ∷ allValid
    withUpdatedInbox : Env
    withUpdatedInbox = updateInboxEnv withM (Σ.proj₂ toRef) addMsg
    withUnblocked : Env
    withUnblocked = unblockActor withUpdatedInbox (Σ.proj₁ toRef)
-- ===== Bind receive =====
runEnv (suc n) env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ acts | w ∷ ww | m >>= f |
  Receive = ♯ IO.putStrLn ("Bind Receive" ++ nName name) IO.>> ♯ runEnv n (topToBack (env' mInb))
  where
    mInb : Σ[ ls ∈ List (NamedMessage IS) ] All (messageValid (Env.store env)) ls
    mInb = getInbox env (ValidActor.hasInb w)
    myPoint : name ↦ IS ∈e inboxesToStore (Env.inbs env)
    myPoint rewrite (Env.inbs=store env) = ValidActor.hasInb w
    removeMsg : Σ[ inLs ∈ List (NamedMessage IS)] All (messageValid (Env.store env)) inLs → Σ[ outLs ∈ List (NamedMessage IS)] All (messageValid (Env.store env)) outLs
    removeMsg ([] , []) = [] , []
    removeMsg (x ∷ inls , px ∷ prfs) = inls , prfs
    inboxesAfter : Σ[ ls ∈ List Inbox ] All (allMessagesValid (Env.store env)) ls × (inboxesToStore (Env.inbs env) ≡ inboxesToStore ls)
    inboxesAfter = updateInboxes {name} {IS} (Env.store env) (Env.inbs env) (Env.messagesValid env) myPoint removeMsg
    sameStoreAfter : Env.store env ≡ inboxesToStore (Σ.proj₁ inboxesAfter)
    sameStoreAfter rewrite (sym (Σ.proj₂ (Σ.proj₂ inboxesAfter))) = Env.inbs=store env
    ∷-refl : ∀ {xs ys} → ∀ v → xs ≡ ys → v ∷ xs ≡ v ∷ ys
    ∷-refl v p rewrite p = refl
    env' : Σ[ ls ∈ List (NamedMessage IS) ] All (messageValid (Env.store env)) ls → Env
    env' ([] , proj₂) = record
                          { acts = acts
                          ; blocked = record
                                        { IS = IS
                                        ; A = A
                                        ; references = references
                                        ; es = es
                                        ; esEqRefs = esEqRefs
                                        ; ce = ce
                                        ; act = m >>= f
                                        ; name = name
                                        } ∷ Env.blocked env
                          ; inbs = Env.inbs env
                          ; store = Env.store env
                          ; inbs=store = Env.inbs=store env
                          ; freshName = Env.freshName env
                          ; actorsValid = ww
                          ; blockedValid = record { hasInb = ValidActor.hasInb w ; points = ValidActor.points w } ∷ Env.blockedValid env
                          ; messagesValid = Env.messagesValid env
                          ; nameIsFresh = Env.nameIsFresh env
                          }
    env' (MsgV x ∷ proj₁ , proj₂) = record
                                      { acts = record
                                                 { IS = IS
                                                 ; A = A
                                                 ; references = references
                                                 ; es = es
                                                 ; esEqRefs = esEqRefs
                                                 ; ce = ce
                                                 ; act = ♭ (f (MsgV x))
                                                 ; name = name
                                                 } ∷ acts
                                      ; blocked = Env.blocked env
                                      ; inbs = Σ.proj₁ inboxesAfter
                                      ; store = Env.store env
                                      ; inbs=store = sameStoreAfter
                                      ; freshName = Env.freshName env
                                      ; actorsValid = record { hasInb = ValidActor.hasInb w ; points = ValidActor.points w } ∷ ww
                                      ; blockedValid = Env.blockedValid env
                                      ; messagesValid = Σ.proj₁ (Σ.proj₂ inboxesAfter)
                                      ; nameIsFresh = Env.nameIsFresh env
                                      }
    env' (MsgR {Fw} x x₁ ∷ proj₁ , px ∷ proj₂) = record
                                         { acts = record
                                                    { IS = IS
                                                    ; A = A
                                                    ; references = (x₁ , Fw) ∷ references
                                                    ; es = Fw ∷ es
                                                    ; esEqRefs = ∷-refl Fw esEqRefs
                                                    ; ce = ce
                                                    ; act = ♭ (f (MsgR x))
                                                    ; name = name
                                                    } ∷ acts
                                         ; blocked = Env.blocked env
                                         ; inbs = Σ.proj₁ inboxesAfter
                                         ; store = Env.store env
                                         ; inbs=store = sameStoreAfter
                                         ; freshName = Env.freshName env
                                         ; actorsValid = record { hasInb = ValidActor.hasInb w ; points = px ∷ ValidActor.points w } ∷ ww
                                         ; blockedValid = Env.blockedValid env
                                         ; messagesValid = Σ.proj₁ (Σ.proj₂ inboxesAfter)
                                         ; nameIsFresh = Env.nameIsFresh env
                                         }
-- ===== Bind lift =====
runEnv (suc n) env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ acts | w ∷ ww | m >>= f |
  ALift {B} {esX} {ceX} inc x with (♭ x)
... | bx = ♯ IO.putStrLn ("Bind lift" ++ nName name) IO.>> ♯ runEnv n (topToBack env')
  where
    liftedRefs = liftRefs inc references esEqRefs
    liftedBx : ActorM IS B (map justInbox (Σ.proj₁ liftedRefs)) ceX
    liftedBx rewrite (sym (Σ.proj₂ (Σ.proj₂ liftedRefs))) = bx
    bindAct : Actor
    bindAct = record
                { IS = IS
                ; A = A
                ; references = Σ.proj₁ liftedRefs
                ; es = map justInbox (Σ.proj₁ liftedRefs)
                ; esEqRefs = refl
                ; ce = ce
                ; act = ♯ liftedBx >>= f
                ; name = name
                }
    bindActValid : ValidActor (Env.store env) bindAct
    bindActValid = record { hasInb = ValidActor.hasInb w ; points = All-⊆ (Σ.proj₁ (Σ.proj₂ liftedRefs)) (ValidActor.points w) }
    env' : Env
    env' = record
             { acts = bindAct ∷ acts
             ; blocked = Env.blocked env
             ; inbs = Env.inbs env
             ; store = Env.store env
             ; inbs=store = Env.inbs=store env
             ; freshName = Env.freshName env
             ; actorsValid = bindActValid ∷ ww
             ; blockedValid = Env.blockedValid env
             ; messagesValid = Env.messagesValid env
             ; nameIsFresh = Env.nameIsFresh env
             }
-- ===== Bind self =====
runEnv (suc n) env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ acts | w ∷ ws | m >>= f |
  Self = ♯ IO.putStrLn ("Bind self" ++ nName name) IO.>> ♯ runEnv n (topToBack env')
  where
    env' : Env
    env' = (record
                        { acts = record
                                   { IS = IS
                                   ; A = A
                                   ; references = (name , IS) ∷ references
                                   ; es = IS ∷ es
                                   ; esEqRefs = eqRefHelper esEqRefs refl
                                   ; ce = ce
                                   ; act = ♭ (f (lift tt))
                                   ; name = name
                                   } ∷ acts
                        ; blocked = Env.blocked env
                        ; inbs = Env.inbs env
                        ; store = Env.store env
                        ; inbs=store = Env.inbs=store env
                        ; freshName = Env.freshName env
                        ; actorsValid = record { hasInb = ValidActor.hasInb w ; points = ValidActor.hasInb w ∷ ValidActor.points w } ∷ ws
                        ; blockedValid = Env.blockedValid env
                        ; messagesValid = Env.messagesValid env
                        ; nameIsFresh = Env.nameIsFresh env
                        })
       where
         eqRefHelper : (map justInbox references ≡ es) → (justInbox (name , IS) ≡ IS) → justInbox (name , IS) ∷ map justInbox references ≡ IS ∷ es
         eqRefHelper refl refl = refl
-- ===== Spawn =====
runEnv (suc n) env | x ∷ acts | _ | Spawn act₁ = ♯ IO.putStrLn ("Spawn from" ++ aName x) IO.>> ♯ runEnv n (topToBack (addTop act₁ (dropTop env)))
-- ===== Send value =====
runEnv (suc n) env | record { IS = IS ; A = .(Lift ⊤) ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = .(λ _ → es) ; act = act ; name = name } ∷ acts | qq ∷ _ |
                            SendValue {ToIS = ToIS} canSendTo msg with (lookupReference qq canSendTo)
... | stName , sendTo = ♯ IO.putStrLn ("Send Value from" ++ nName name ++ " to" ++ nName stName) IO.>> ♯ runEnv n (topToBack withUnblocked)
  where
    addMsg : Σ (List (NamedMessage ToIS)) (All (messageValid (Env.store env))) →
      Σ (List (NamedMessage ToIS)) (All (messageValid (Env.store env)))
    addMsg (messages , allValid) = (MsgV msg ∷ messages) , tt ∷ allValid
    withUpdatedInbox : Env
    withUpdatedInbox = updateInboxEnv env sendTo addMsg
    withTopDropped : Env
    withTopDropped = dropTop withUpdatedInbox
    withUnblocked : Env
    withUnblocked = unblockActor withTopDropped stName
-- ===== Send reference =====
runEnv (suc n) env | record { IS = IS ; A = .(Lift ⊤) ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = .(λ _ → es) ; act = act ; name = name } ∷ acts | qq ∷ _ |
                            SendReference {_} {ToIS} {FwIS} canSendTo canForward msg with (lookupReference qq canSendTo) | (lookupReference qq canForward)
... | sendName , toRef | fwName , fwRef =
  ♯ IO.putStrLn ("Send reference from" ++ nName name ++ " to" ++ nName sendName ++ " forwarding" ++ nName fwName) IO.>>
  ♯ runEnv n (topToBack withUnblocked)
  where
    addMsg : Σ (List (NamedMessage ToIS)) (All (messageValid (Env.store env))) →
      Σ (List (NamedMessage ToIS)) (All (messageValid (Env.store env)))
    addMsg (messages , allValid) = (MsgR msg fwName ∷ messages) , fwRef ∷ allValid
    withUpdatedInbox : Env
    withUpdatedInbox = updateInboxEnv env toRef addMsg
    withTopDropped : Env
    withTopDropped = dropTop withUpdatedInbox
    withUnblocked : Env
    withUnblocked = unblockActor withTopDropped sendName
-- ===== Receive =====
runEnv (suc n) env | record { IS = IS ; A = .(Message IS) ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = .(addIfRef es) ; act = act ; name = name } ∷ acts | _ |
  Receive = ♯ IO.putStrLn ("Receive" ++ nName name) IO.>> ♯ runEnv n (dropTop env) -- Receive without follow up is like return, just drop it. If we care about what state the inboxes end up in, then we need to actually do something here
-- ===== Lift =====
runEnv (suc n) env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ acts | qq ∷ qqs | ALift {ys = ys} inc x with (♭ x)
... | bx = ♯ IO.putStrLn ("Lift" ++ nName name) IO.>> ♯ runEnv n (topToBack env')
  where
    liftedRefs = liftRefs inc references esEqRefs
    liftedBx : ActorM IS A (map justInbox (Σ.proj₁ liftedRefs)) ce
    liftedBx rewrite (sym (Σ.proj₂ (Σ.proj₂ liftedRefs))) = bx
    bxAct : Actor
    bxAct = record
              { IS = IS
              ; A = A
              ; references = Σ.proj₁ liftedRefs
              ; es = map justInbox (Σ.proj₁ liftedRefs)
              ; esEqRefs = refl
              ; ce = ce
              ; act = liftedBx
              ; name = name
              }
    bxValid : ValidActor (Env.store env) bxAct
    bxValid = record { hasInb = ValidActor.hasInb qq ; points = All-⊆ (Σ.proj₁ (Σ.proj₂ liftedRefs)) (ValidActor.points qq) }
    env' : Env
    env' = record { acts = bxAct ∷ acts
      ; blocked = Env.blocked env
      ; inbs = Env.inbs env
      ; store = Env.store env
      ; inbs=store = Env.inbs=store env
      ; freshName = Env.freshName env
      ; actorsValid = bxValid ∷ qqs
      ; blockedValid = Env.blockedValid env
      ; messagesValid = Env.messagesValid env
      ; nameIsFresh = Env.nameIsFresh env
      }
-- ===== Self =====
runEnv (suc n) env | record { IS = IS ; A = .(Lift ⊤) ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = .(λ _ → IS ∷ es) ; act = act ; name = name } ∷ acts | _ |
  Self = ♯ IO.putStrLn ("Self" ++ nName name) IO.>> ♯ runEnv n (dropTop env) -- Self without follow up is like return, just drop it

