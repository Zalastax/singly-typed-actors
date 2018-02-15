module Simulate where

open import Sublist using (_⊆_ ; [] ; keep ; skip ; All-⊆)
open import ActorMonad public
open import SimulationEnvironment
open import EnvironmentOperations

open import Data.Colist using (Colist ; [] ; _∷_)
open import Data.List using (List ; _∷_ ; [] ; map)
open import Data.List.All using (All ; _∷_ ; [] ; lookup) renaming (map to ∀map)
open import Data.Nat using (ℕ ; zero ; suc ; _≟_ ; _<_ ; s≤s)
open import Data.Nat.Properties using (≤-reflexive ; ≤-step)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)
open import Data.Unit using (⊤ ; tt)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)

open import Level using (Lift ; lift) renaming (suc to lsuc ; zero to lzero)
open import Coinduction using (∞ ; ♯_ ; ♭)

data ReceiveKind : Set where
  Nothing : ReceiveKind
  Value : ReceiveKind
  Reference : Name → ReceiveKind
  Dropped : ReceiveKind

data Trace : Set where
  Return : Name → Trace
  Bind : Trace → Trace
  BindDouble : Name → Trace -- If we encounter a bind and then a bind again...
  Spawn : (spawner : Name) → (spawned : Name) → Trace
  SendValue : (sender : Name) → (receiver : Name) → Trace
  SendReference : (sender : Name) → (receiver : Name) → (reference : Name) → Trace
  Receive : Name → ReceiveKind → Trace
  TLift : Name → Trace
  Self : Name → Trace

record EnvStep : Set₂ where
  field
    env : Env
    trace : Trace

private
  keepSimulating : Trace → Env → Colist EnvStep

open Actor
open ValidActor
open Env

∷-refl : ∀ {ls ls'} → ∀ x → ls ≡ ls' → x ∷ ls ≡ x ∷ ls'
∷-refl x refl = refl

simulate : Env → Colist EnvStep
simulate env with (acts env) | (actorsValid env)
-- ===== OUT OF ACTORS =====
simulate env | [] | _ = []
simulate env | actor ∷ rest | _ with (act actor)
-- ===== Value =====
simulate env | actor ∷ rest | _ |
  Value val = keepSimulating (Return (name actor)) (dropTop env) -- Actor is done, just drop it
-- ===== Bind =====
simulate env | actor ∷ rest | _ | m >>= f with (♭ m)
-- ===== Bind Value =====
simulate env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ rest | valid ∷ restValid | m >>= f |
  Value val = keepSimulating (Bind (Return name)) env'
  where
    bindAct : Actor
    bindAct = record
                { IS = IS
                ; A = A
                ; references = references
                ; es = es
                ; esEqRefs = esEqRefs
                ; ce = ce
                ; act = ♭ (f val)
                ; name = name
                }
    bindActValid : ValidActor (store env) bindAct
    bindActValid = record { hasInb = hasInb valid ; points = points valid }
    env' : Env
    env' = record
             { acts = bindAct ∷ rest
             ; blocked = blocked env
             ; inbs = inbs env
             ; store = store env
             ; inbs=store = inbs=store env
             ; freshName = freshName env
             ; actorsValid = bindActValid ∷ restValid
             ; blockedValid = blockedValid env
             ; messagesValid = messagesValid env
             ; nameIsFresh = nameIsFresh env
             }
-- ===== Bind Bind =====
simulate env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ rest | valid ∷ restValid | m >>= f |
  mm >>= g = keepSimulating (Bind (BindDouble name)) env'
  where
    bindAct : Actor
    bindAct = record
                { IS = IS
                ; A = A
                ; references = references
                ; es = es
                ; esEqRefs = esEqRefs
                ; ce = ce
                ; act = mm >>= λ x → ♯ (g x >>= f)
                ; name = name
                }
    bindActValid : ValidActor (store env) bindAct
    bindActValid = record { hasInb = hasInb valid ; points = points valid }
    env' : Env
    env' = record
             { acts = bindAct ∷ rest
             ; blocked = blocked env
             ; inbs = inbs env
             ; store = store env
             ; inbs=store = inbs=store env
             ; freshName = freshName env
             ; actorsValid = bindActValid ∷ restValid
             ; blockedValid = blockedValid env
             ; messagesValid = messagesValid env
             ; nameIsFresh = nameIsFresh env
             }
-- ===== Bind Spawn =====
simulate env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ rest | valid ∷ restValid | m >>= f |
  Spawn {NewIS} {B} {_} {ceN} bm = keepSimulating (Spawn name (freshName env)) (topToBack env') -- move the spawned to the back, keepSimulating will move bindAct. Doesn't really matter...
  where
    newStoreEntry : NamedInbox
    newStoreEntry = (freshName env) , NewIS
    newStore : Store
    newStore = newStoreEntry ∷ store env
    newInb : Inbox
    newInb = record { IS = NewIS ; inb = [] ; name = freshName env }
    newAct : Actor
    newAct = record
               { IS = NewIS
               ; A = B
               ; references = []
               ; es = []
               ; esEqRefs = refl
               ; ce = ceN
               ; act = bm
               ; name = freshName env
               }
    newActValid : ValidActor newStore newAct
    newActValid = record { hasInb = zero ; points = [] }
    newIsFresh : NameFresh newStore (suc (freshName env))
    newIsFresh = s≤s (≤-reflexive refl) ∷ ∀map ≤-step (nameIsFresh env)
    newInbs=newStore : store env ≡ inboxesToStore (inbs env) → newStore ≡ inboxesToStore (newInb ∷ inbs env)
    newInbs=newStore refl = refl
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
      hasInb = suc {pr =
        sucHelper (hasInb valid) (nameIsFresh env)
        } (hasInb valid)
      ; points = zero ∷ ∀map (λ x₁ → suc {pr =
        sucHelper x₁ (nameIsFresh env)
        } x₁) (points valid) }
    env' : Env
    env' = record
             { acts = newAct ∷ bindAct ∷ rest
             ; blocked = blocked env
             ; inbs = newInb ∷ inbs env
             ; store = newStore
             ; inbs=store = newInbs=newStore (inbs=store env)
             ; freshName = suc (freshName env)
             ; actorsValid = newActValid ∷ bindActValid ∷ ∀map (ValidActorSuc (nameIsFresh env)) restValid
             ; blockedValid = ∀map (ValidActorSuc (nameIsFresh env)) (blockedValid env)
             ; messagesValid = [] ∷ ∀map (λ {inb} mv → messagesValidSuc {_} {inb} (nameIsFresh env) mv) (messagesValid env)
             ; nameIsFresh = newIsFresh
             }
-- ===== Bind send value =====
simulate env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ rest | valid ∷ restValid | m >>= f |
  SendValue {ToIS = ToIS} canSendTo msg = keepSimulating (Bind (SendValue name toName)) withUnblocked
  where
    toLookedUp : Σ[ name ∈ Name ] name ↦ ToIS ∈e (store env)
    toLookedUp = lookupReference valid canSendTo
    toName : Name
    toName = Σ.proj₁ toLookedUp
    toRef : toName ↦ ToIS ∈e (store env)
    toRef = Σ.proj₂ toLookedUp
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
    bindActValid : ValidActor (store env) bindAct
    bindActValid = record { hasInb = hasInb valid ; points = points valid }
    withM : Env
    withM = record
              { acts = bindAct ∷ rest
              ; blocked = blocked env
              ; inbs = inbs env
              ; store = store env
              ; inbs=store = inbs=store env
              ; freshName = freshName env
              ; actorsValid = bindActValid ∷ restValid
              ; blockedValid = blockedValid env
              ; messagesValid = messagesValid env
              ; nameIsFresh = nameIsFresh env
              }
    addMsg : Σ (List (NamedMessage ToIS)) (All (messageValid (store env))) →
              Σ (List (NamedMessage ToIS)) (All (messageValid (store env)))
    addMsg (messages , allValid) = (MsgV msg ∷ messages) , tt ∷ allValid
    withUpdatedInbox : Env
    withUpdatedInbox = updateInboxEnv withM toRef addMsg
    withUnblocked : Env
    withUnblocked = unblockActor withUpdatedInbox toName
-- ===== Bind send reference =====
simulate env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ rest | valid ∷ restValid | m >>= f |
  SendReference {ToIS = ToIS} {FwIS = FwIS} canSendTo canForward msg = keepSimulating (Bind (SendReference name toName fwName)) withUnblocked
  where
    toLookedUp : Σ[ name ∈ Name ] name ↦ ToIS ∈e (store env)
    toLookedUp = lookupReference valid canSendTo
    toName : Name
    toName = Σ.proj₁ toLookedUp
    toRef : toName ↦ ToIS ∈e (store env)
    toRef = Σ.proj₂ toLookedUp
    fwLookedUp : Σ[ name ∈ Name ] name ↦ FwIS ∈e (store env)
    fwLookedUp = lookupReference valid canForward
    fwName : Name
    fwName = Σ.proj₁ fwLookedUp
    fwRef : fwName ↦ FwIS ∈e (store env)
    fwRef = Σ.proj₂ fwLookedUp
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
    bindActValid : ValidActor (store env) bindAct
    bindActValid = record { hasInb = hasInb valid ; points = points valid }
    withM : Env
    withM = record
              { acts = bindAct ∷ rest
              ; blocked = blocked env
              ; inbs = inbs env
              ; store = store env
              ; inbs=store = inbs=store env
              ; freshName = freshName env
              ; actorsValid = bindActValid ∷ restValid
              ; blockedValid = blockedValid env
              ; messagesValid = messagesValid env
              ; nameIsFresh = nameIsFresh env
              }
    addMsg : Σ (List (NamedMessage ToIS)) (All (messageValid (store env))) →
              Σ (List (NamedMessage ToIS)) (All (messageValid (store env)))
    addMsg (messages , allValid) = (MsgR msg fwName ∷ messages) , (fwRef ∷ allValid)
    withUpdatedInbox : Env
    withUpdatedInbox = updateInboxEnv withM toRef addMsg
    withUnblocked : Env
    withUnblocked = unblockActor withUpdatedInbox toName
-- ===== Bind receive =====
simulate env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ rest | valid ∷ restValid | m >>= f |
  Receive = keepSimulating (Bind (Receive name (receiveKind (Σ.proj₁ mInb)))) (env' mInb)
  where
    mInb : Σ[ ls ∈ List (NamedMessage IS) ] All (messageValid (store env)) ls
    mInb = getInbox env (hasInb valid)
    myPoint : (inboxesToStore (inbs env) ≡ store env) → name ↦ IS ∈e inboxesToStore (inbs env)
    myPoint refl = hasInb valid
    removeMsg : Σ[ inLs ∈ List (NamedMessage IS)] All (messageValid (store env)) inLs → Σ[ outLs ∈ List (NamedMessage IS)] All (messageValid (store env)) outLs
    removeMsg ([] , []) = [] , []
    removeMsg (x ∷ inls , px ∷ prfs) = inls , prfs
    inboxesAfter : Σ[ ls ∈ List Inbox ] All (allMessagesValid (store env)) ls × (inboxesToStore (inbs env) ≡ inboxesToStore ls)
    inboxesAfter = updateInboxes {name} {IS} (store env) (inbs env) (messagesValid env) (myPoint (sym (inbs=store env))) removeMsg
    -- I would like to not use rewrite, but I couldn't get something Agda liked working
    sameStoreAfter : store env ≡ inboxesToStore (Σ.proj₁ inboxesAfter)
    sameStoreAfter rewrite (sym (Σ.proj₂ (Σ.proj₂ inboxesAfter))) = Env.inbs=store env
    receiveKind : List (NamedMessage IS) → ReceiveKind
    receiveKind [] = Nothing
    receiveKind (MsgV x ∷ ls) = Value
    receiveKind (MsgR x x₁ ∷ ls) = Reference x₁
    env' : Σ[ ls ∈ List (NamedMessage IS) ] All (messageValid (Env.store env)) ls → Env
    env' ([] , proj₂) = record
                          { acts = rest
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
                          ; actorsValid = restValid
                          ; blockedValid = record { hasInb = hasInb valid ; points = ValidActor.points valid } ∷ Env.blockedValid env
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
                                                 } ∷ rest
                                      ; blocked = Env.blocked env
                                      ; inbs = Σ.proj₁ inboxesAfter
                                      ; store = Env.store env
                                      ; inbs=store = sameStoreAfter
                                      ; freshName = Env.freshName env
                                      ; actorsValid = record { hasInb = hasInb valid ; points = points valid } ∷ restValid
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
                                                    } ∷ rest
                                         ; blocked = Env.blocked env
                                         ; inbs = Σ.proj₁ inboxesAfter
                                         ; store = Env.store env
                                         ; inbs=store = sameStoreAfter
                                         ; freshName = Env.freshName env
                                         ; actorsValid = record { hasInb = hasInb valid ; points = px ∷ points valid } ∷ restValid
                                         ; blockedValid = Env.blockedValid env
                                         ; messagesValid = Σ.proj₁ (Σ.proj₂ inboxesAfter)
                                         ; nameIsFresh = Env.nameIsFresh env
                                         }
-- ===== Bind lift =====
simulate env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ rest | valid ∷ restValid | m >>= f |
  ALift {B} {esX} {ceX} inc x with (♭ x)
... | bx = keepSimulating (Bind (TLift name)) env'
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
    bindActValid : ValidActor (store env) bindAct
    bindActValid = record { hasInb = hasInb valid ; points = All-⊆ (Σ.proj₁ (Σ.proj₂ liftedRefs)) (points valid) }
    env' : Env
    env' = record
             { acts = bindAct ∷ rest
             ; blocked = Env.blocked env
             ; inbs = Env.inbs env
             ; store = Env.store env
             ; inbs=store = Env.inbs=store env
             ; freshName = Env.freshName env
             ; actorsValid = bindActValid ∷ restValid
             ; blockedValid = Env.blockedValid env
             ; messagesValid = Env.messagesValid env
             ; nameIsFresh = Env.nameIsFresh env
             }
-- ===== Bind self =====
simulate env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ rest | valid ∷ restValid | m >>= f |
  Self = keepSimulating (Bind (Self name)) env'
  where
    eqRefHelper : (map justInbox references ≡ es) → (justInbox (name , IS) ≡ IS) → justInbox (name , IS) ∷ map justInbox references ≡ IS ∷ es
    eqRefHelper refl refl = refl
    bindAct : Actor
    bindAct = record
                { IS = IS
                ; A = A
                ; references = (name , IS) ∷ references
                ; es = IS ∷ es
                ; esEqRefs = eqRefHelper esEqRefs refl
                ; ce = ce
                ; act = ♭ (f _)
                ; name = name
                }
    bindActValid : ValidActor (store env) bindAct
    bindActValid = record { hasInb = hasInb valid ; points = hasInb valid ∷ points valid }
    env' : Env
    env' = record
             { acts = bindAct ∷ rest
             ; blocked = blocked env
             ; inbs = inbs env
             ; store = store env
             ; inbs=store = inbs=store env
             ; freshName = freshName env
             ; actorsValid = bindActValid ∷ restValid
             ; blockedValid = blockedValid env
             ; messagesValid = messagesValid env
             ; nameIsFresh = nameIsFresh env
             }
-- ===== Spawn =====
simulate env | record { IS = IS ; A = .(Lift ⊤) ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = .(λ _ → _ ∷ es) ; act = act ; name = name } ∷ rest | valid ∷ restValid |
  Spawn act₁ = keepSimulating (Spawn name (freshName env)) (addTop act₁ (dropTop env))
-- ===== Send value =====
simulate env | record { IS = IS ; A = .(Lift ⊤) ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = .(λ _ → es) ; act = act ; name = name } ∷ rest | valid ∷ restValid |
  SendValue {ToIS = ToIS} canSendTo msg = keepSimulating (SendValue name toName) withUnblocked
  where
    toLookedUp : Σ[ name ∈ Name ] name ↦ ToIS ∈e (store env)
    toLookedUp = lookupReference valid canSendTo
    toName : Name
    toName = Σ.proj₁ toLookedUp
    toRef : toName ↦ ToIS ∈e (store env)
    toRef = Σ.proj₂ toLookedUp
    addMsg : Σ (List (NamedMessage ToIS)) (All (messageValid (store env))) →
      Σ (List (NamedMessage ToIS)) (All (messageValid (store env)))
    addMsg (messages , allValid) = (MsgV msg ∷ messages) , tt ∷ allValid
    withUpdatedInbox : Env
    withUpdatedInbox = updateInboxEnv env toRef addMsg
    withTopDropped : Env
    withTopDropped = dropTop withUpdatedInbox
    withUnblocked : Env
    withUnblocked = unblockActor withTopDropped toName
-- ===== Send reference =====
simulate env | record { IS = IS ; A = .(Lift ⊤) ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = .(λ _ → es) ; act = act ; name = name } ∷ rest | valid ∷ restValid |
  SendReference {ToIS = ToIS} {FwIS = FwIS} canSendTo canForward msg = keepSimulating (SendReference name toName fwName) withUnblocked
  where
    toLookedUp : Σ[ name ∈ Name ] name ↦ ToIS ∈e (store env)
    toLookedUp = lookupReference valid canSendTo
    toName : Name
    toName = Σ.proj₁ toLookedUp
    toRef : toName ↦ ToIS ∈e (store env)
    toRef = Σ.proj₂ toLookedUp
    fwLookedUp : Σ[ name ∈ Name ] name ↦ FwIS ∈e (store env)
    fwLookedUp = lookupReference valid canForward
    fwName : Name
    fwName = Σ.proj₁ fwLookedUp
    fwRef : fwName ↦ FwIS ∈e (store env)
    fwRef = Σ.proj₂ fwLookedUp
    addMsg : Σ (List (NamedMessage ToIS)) (All (messageValid (store env))) →
      Σ (List (NamedMessage ToIS)) (All (messageValid (store env)))
    addMsg (messages , allValid) = (MsgR msg fwName ∷ messages) , fwRef ∷ allValid
    withUpdatedInbox : Env
    withUpdatedInbox = updateInboxEnv env toRef addMsg
    withTopDropped : Env
    withTopDropped = dropTop withUpdatedInbox
    withUnblocked : Env
    withUnblocked = unblockActor withTopDropped toName
-- ===== Receive =====
simulate env | record { IS = IS ; A = .(Message IS) ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = .(addIfRef es) ; act = act ; name = name } ∷ rest | valid ∷ restValid |
  Receive = keepSimulating (Receive name Dropped) (dropTop env) -- Receive without follow up is like return, just drop it.
  -- If we care about what state the inboxes end up in, then we need to actually do something here
-- ===== Lift =====
simulate env | record { IS = IS ; A = A ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = ce ; act = act ; name = name } ∷ rest | valid ∷ restValid |
  ALift inc x with (♭ x)
... | bx = keepSimulating (TLift name) env'
  where
    liftedRefs = liftRefs inc references esEqRefs
    -- TODO: See if we can avoid using rewrite here
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
    bxValid = record { hasInb = hasInb valid ; points = All-⊆ (Σ.proj₁ (Σ.proj₂ liftedRefs)) (points valid) }
    env' : Env
    env' = record { acts = bxAct ∷ rest
      ; blocked = blocked env
      ; inbs = inbs env
      ; store = store env
      ; inbs=store = inbs=store env
      ; freshName = freshName env
      ; actorsValid = bxValid ∷ restValid
      ; blockedValid = blockedValid env
      ; messagesValid = messagesValid env
      ; nameIsFresh = nameIsFresh env
      }
simulate env | record { IS = IS ; A = .(Lift ⊤) ; references = references ; es = es ; esEqRefs = esEqRefs ; ce = .(λ _ → IS ∷ es) ; act = act ; name = name } ∷ rest | valid ∷ restValid |
  Self = keepSimulating (Self name) (dropTop env)


keepSimulating trace env = record { env = env ; trace = trace } ∷ ♯ simulate (topToBack env)
