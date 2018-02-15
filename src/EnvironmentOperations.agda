module EnvironmentOperations where
open import ActorMonad
open import SimulationEnvironment
open import Membership-equality using (_∈_)
open import Sublist using (_⊆_ ; [] ; keep ; skip)

open import Data.List using (List ; _∷_ ; [] ; map)
open import Data.List.All using (All ; _∷_ ; []; lookup) renaming (map to ∀map)
open import Data.List.All.Properties using (++⁺)
open import Data.List.Any using (here ; there)
open import Data.Nat using (ℕ ; zero ; suc ; _≟_ ; _<_)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)
open import Data.Unit using (⊤ ; tt)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong)
open import Relation.Nullary using (Dec ; yes ; no)


-- Update one of the inboxes in a list of inboxes.
-- All the inboxes have been proven to be valid in the context of a store,
-- and the goal is to return a new list of inboxes which are also valid for the same store.
-- We know what inbox to update via an index using the inbox name into the list.
-- The update function receives both a list of messages from the inbox we pointed out,
-- and a proof that all the messages are valid for the store.
-- The update function returns a new list of the same type,
-- and has to provide a proof that this list is also valid for the store
updateInboxes :  {name : Name} → ∀ {IS} →
          (store : Store) →
          (inbs : List Inbox) →
          (All (allMessagesValid store) inbs) →
          (name ↦ IS ∈e (inboxesToStore inbs)) →
          (f : Σ[ inLs ∈ List (NamedMessage IS)] All (messageValid store) inLs → Σ[ outLs ∈ List (NamedMessage IS)] All (messageValid store) outLs) →
          Σ[ ls ∈ List Inbox ] All (allMessagesValid store) ls × (inboxesToStore inbs ≡ inboxesToStore ls)
updateInboxes store [] prfs () f
updateInboxes store (x ∷ inbs) (px ∷ prfs) zero f with (f (Inbox.inb x , px))
... | msgs , msgsValid = record { IS = Inbox.IS x ; inb = msgs ; name = Inbox.name x } ∷ inbs , msgsValid ∷ prfs , refl
updateInboxes store (x ∷ inbs) (px ∷ prfs) (suc point) f with (updateInboxes store inbs prfs point f)
... | proj₁ , proj₂ , proj₃ = (x ∷ proj₁) , ((px ∷ proj₂) , cong (λ q → ((Inbox.name x) , Inbox.IS x) ∷ q) proj₃)

-- Move the actor that is at the top of the list, to the back of the list
-- This is done to create a round-robin system for the actors, since runEnv always picks the actor at the top
-- Uses the insight that the order of the inboxes soes not correspond to the order of the Actors,
-- and that moving an actor to the back doesn't change any of the proofs about actors being valid.
topToBack : Env → Env
topToBack env with (Env.acts env) | (Env.actorsValid env)
topToBack env | [] | _ = env
topToBack env | x ∷ acts | (y ∷ prfs) = record
                             { acts = acts Data.List.++ x ∷ []
                             ; blocked = Env.blocked env
                             ; inbs = Env.inbs env
                             ; store = Env.store env
                             ; inbs=store = Env.inbs=store env
                             ; freshName = Env.freshName env
                             ; actorsValid = ++⁺ prfs (y ∷ [])
                             ; blockedValid = Env.blockedValid env
                             ; messagesValid = Env.messagesValid env
                             ; nameIsFresh = Env.nameIsFresh env
                             }

-- Drop the actor that is at the top of the list completely.
-- This is used when handling some monadic operations, when there is no following bind.
-- The dropped actor is not put in the blocked list.
dropTop : Env → Env
dropTop env with (Env.acts env) | (Env.actorsValid env)
dropTop env | [] | prfs = env
dropTop env | _ ∷ rest | _ ∷ prfs = record
                                  { acts = rest
                                  ; blocked = Env.blocked env
                                  ; inbs = Env.inbs env
                                  ; store = Env.store env
                                  ; inbs=store = Env.inbs=store env
                                  ; freshName = Env.freshName env
                                  ; actorsValid = prfs
                                  ; blockedValid = Env.blockedValid env
                                  ; messagesValid = Env.messagesValid env
                                  ; nameIsFresh = Env.nameIsFresh env
                                  }

-- convert < to ¬≡
<-¬≡ : ∀ {n m} → n < m → n ¬≡ m
<-¬≡ {zero} {zero} ()
<-¬≡ {zero} {suc m} p = _
<-¬≡ {suc n} {zero} ()
<-¬≡ {suc n} {suc m} (Data.Nat.s≤s p) with (<-¬≡ p)
... | q with (n ≟ m)
<-¬≡ {suc n} {suc m} (Data.Nat.s≤s p) | () | yes p₁
<-¬≡ {suc n} {suc m} (Data.Nat.s≤s p) | q | no ¬p = _

-- If a name is fresh for a store (i.e. all names in the store are < than the name),
-- then none of the names in the store is equal to the name
Fresh¬≡ : ∀ {store name } → NameFresh store name → (All (λ m → (Σ.proj₁ m) ¬≡ name) store)
Fresh¬≡ ls = ∀map (λ frsh → <-¬≡ frsh) ls

-- helps show that all the names in the store are still valid if we add a new name on top,
-- if the new name is > than all the names already in the store.
sucHelper : ∀ {store name IS n} →
            name ↦ IS ∈e store →
            All (λ v → suc (Σ.proj₁ v) Data.Nat.≤ n) store →
            ¬[ name ≟ n ]
sucHelper zero (px ∷ p) = <-¬≡ px
sucHelper (suc q) (px ∷ p) = sucHelper q p

-- An actor is still valid if we add a new inbox to the store, as long as that name is not used in the store before
ValidActorSuc : ∀ {store actor n x} → (NameFresh store n) → ValidActor store actor → ValidActor ((n , x) ∷ store) actor
ValidActorSuc frsh va = record { hasInb = suc {pr = sucHelper (ValidActor.hasInb va) frsh} (ValidActor.hasInb va) ; points = ∀map (λ p → suc {pr = sucHelper p frsh} p) (ValidActor.points va) }

-- All the messages in an inbox are still valid if we add a new inbox to the store, as long as that name is not used in the store before
messagesValidSuc : ∀ {store inb n x} → (NameFresh store n) → allMessagesValid store inb → allMessagesValid ((n , x) ∷ store) inb
messagesValidSuc {store} {inb} {n} {x} frsh vi = ∀map msgValidSuc vi
  where
    msgValidSuc : {x₁ : NamedMessage (Inbox.IS inb)} →
                  messageValid store x₁ → messageValid ((n , x) ∷ store) x₁
    msgValidSuc {x₁ = Value _ _} mv = tt
    msgValidSuc {x₁ = Reference _ _} mv = suc {pr = sucHelper mv frsh} mv

-- Add a new actor to the environment.
-- The actor is added to the top of the list of actors.
addTop : ∀ {IS A ce} → ActorM IS A [] ce → Env → Env
addTop {IS} {A} {ce} act env = record
                                 { acts = record
                                            { IS = IS
                                            ; A = A
                                            ; references = []
                                            ; es = []
                                            ; esEqRefs = refl
                                            ; ce = ce
                                            ; act = act
                                            ; name = Env.freshName env
                                            } ∷ Env.acts env
                                 ; blocked = Env.blocked env
                                 ; inbs = record { IS = IS ; inb = [] ; name = Env.freshName env } ∷ Env.inbs env
                                 ; store = (Env.freshName env , IS) ∷ Env.store env
                                 ; inbs=store = ∷-refl (Env.freshName env , IS) (Env.inbs=store env)
                                 ; freshName = suc (Env.freshName env)
                                 ; actorsValid = record { hasInb = zero ; points = [] } ∷ ∀map (ValidActorSuc (Env.nameIsFresh env)) (Env.actorsValid env)
                                 ; blockedValid = ∀map (ValidActorSuc (Env.nameIsFresh env)) (Env.blockedValid env)
                                 ; messagesValid = [] ∷ ∀map (λ {x} vi → messagesValidSuc {_} {x} (Env.nameIsFresh env) vi) (Env.messagesValid env)
                                 ; nameIsFresh = Data.Nat.s≤s (≤-reflexive refl) ∷ ∀map  Data.Nat.Properties.≤-step (Env.nameIsFresh env)
                                 }
       where
         ∷-refl : ∀ {store store'} → ∀ w →
                store ≡ store' →
                w ∷ store ≡ w ∷ store'
         ∷-refl v p rewrite p = refl

-- Extracts the messages in an inbox from the environment, given a pointer to the store of that environment
getInbox : ∀ {name IS} → (env : Env) → name ↦ IS ∈e (Env.store env) → Σ[ ls ∈ List (NamedMessage IS) ] All (messageValid (Env.store env)) ls
getInbox {name} {IS} env point  = loop (Env.inbs env) (Env.messagesValid env) (fixThePoint point)
  where
    fixThePoint : name ↦ IS ∈e (Env.store env) → name ↦ IS ∈e (inboxesToStore (Env.inbs env))
    fixThePoint p rewrite (Env.inbs=store env) = p
    loop : ∀ {name IS} → (inbs : List Inbox) → All (allMessagesValid (Env.store env)) inbs → name ↦ IS ∈e (inboxesToStore inbs) → Σ[ ls ∈ List (NamedMessage IS) ] All (messageValid (Env.store env)) ls
    loop [] prfs ()
    loop (x ∷ inbs) (px ∷ prfs) zero = (Inbox.inb x) , px
    loop (x ∷ inbs) (px ∷ prfs) (suc point) = loop inbs prfs point

-- Updates an inbox in the environment
-- Just a wrapper arround 'updateInboxes'
updateInboxEnv : ∀ {name IS} → (env : Env) → name ↦ IS ∈e (Env.store env) →
                 (f : Σ[ inLs ∈ List (NamedMessage IS)] All (messageValid (Env.store env)) inLs → Σ[ outLs ∈ List (NamedMessage IS)] All (messageValid (Env.store env)) outLs) → Env
updateInboxEnv {name} {IS} env p f = record
                           { acts = Env.acts env
                           ; blocked = Env.blocked env
                           ; inbs = Σ.proj₁ updatedInboxes
                           ; store = Env.store env
                           ; inbs=store = sameStoreAfterUpdate (Env.inbs=store env) -- updSameStore (Env.store env) (Env.inbs env) (Env.inbs=store env) p f
                           ; freshName = Env.freshName env
                           ; actorsValid = Env.actorsValid env -- ∀map updateActVal (Env.actorsValid env)
                           ; blockedValid = Env.blockedValid env -- ∀map updateActVal (Env.blockedValid env)
                           ; messagesValid = Σ.proj₁ (Σ.proj₂ updatedInboxes) -- updateMessagesVal (Env.messagesValid env) -- updateMessagesVal (Env.messagesValid env)
                           ; nameIsFresh = Env.nameIsFresh env
                           }
  where
    -- Just some helpers to align the types
    pp : name ↦ IS ∈e (inboxesToStore (Env.inbs env))
    pp rewrite (Env.inbs=store env) = p
    updatedInboxes : Σ[ ls ∈ List Inbox ] All (allMessagesValid (Env.store env)) ls × (inboxesToStore (Env.inbs env) ≡ inboxesToStore ls)
    updatedInboxes = updateInboxes (Env.store env) (Env.inbs env) (Env.messagesValid env) pp f
    sameShapeAfterUpdate : inboxesToStore (Env.inbs env) ≡ inboxesToStore (Σ.proj₁ updatedInboxes)
    sameShapeAfterUpdate = Σ.proj₂ (Σ.proj₂ updatedInboxes)
    sameStoreAfterUpdate : (Env.store env ≡ (inboxesToStore (Env.inbs env))) → Env.store env ≡ inboxesToStore (Σ.proj₁ updatedInboxes)
    sameStoreAfterUpdate refl = sameShapeAfterUpdate

-- Move an actor from the blocked list to the actors list.
-- Simply looks through the names of all blocked actors and moves those (should be just 1 or 0) with the same name.
-- IF an actor still doesn't have a way to progress (should never happen),
-- it will just get added back to the blocked list the next time it is processed.
unblockActor : Env → Name → Env
unblockActor env name = newEnv (loop (Env.blocked env) (Env.blockedValid env))
  where
    loop : (blocked : List Actor) → (blockedValid : All (ValidActor (Env.store env)) blocked) →
           (Σ[ blockedAfter ∈ List Actor ] All (ValidActor (Env.store env)) blockedAfter) × (Σ[ unblocked ∈ List Actor ] All (ValidActor (Env.store env)) unblocked)
    loop [] [] = ([] , []) , ([] , [])
    loop (x ∷ blocked) (px ∷ blockedValid) with (loop blocked blockedValid)
    ... | (blockedAfter , baValid) , unblocked , unblockedValid with (Actor.name x ≟ name)
    ... | yes p = (blockedAfter , baValid) , ((x ∷ unblocked) , px ∷ unblockedValid)
    ... | no ¬p = ((x ∷ blockedAfter) , (px ∷ baValid)) , unblocked , unblockedValid
    newEnv : Σ (Σ (List Actor) (All (ValidActor (Env.store env))))
               (λ _ → Σ (List Actor) (All (ValidActor (Env.store env)))) → Env
    newEnv ((ba , baValid) , unblocked , unblockedValid) = record
                                                             { acts = unblocked Data.List.++ Env.acts env
                                                             ; blocked = ba
                                                             ; inbs = Env.inbs env
                                                             ; store = Env.store env
                                                             ; inbs=store = Env.inbs=store env
                                                             ; freshName = Env.freshName env
                                                             ; actorsValid = ++⁺ unblockedValid (Env.actorsValid env)
                                                             ; blockedValid = baValid
                                                             ; messagesValid = Env.messagesValid env
                                                             ; nameIsFresh = Env.nameIsFresh env
                                                             }

-- looks up the pointer for one of the references known by an actor
lookupReference : ∀ {store actor ToIS} → ValidActor store actor → ToIS ∈ (Actor.es actor) → Σ[ name ∈ Name ] name ↦ ToIS ∈e store
lookupReference {store} {actor} {ToIS} va ref = loop (Actor.es actor) (Actor.references actor) (ValidActor.points va) (Actor.esEqRefs actor) ref
  where
    loop : (es : List InboxShape) → (refs : List NamedInbox) → (All (λ ref → Σ.proj₁ ref ↦ Σ.proj₂ ref ∈e store) refs) → (map justInbox refs ≡ es) → ToIS ∈ es → Σ[ name ∈ Name ] name ↦ ToIS ∈e store
    loop .[] [] prfs refl ()
    loop _ ((name , IS) ∷ refs) (px₁ ∷ prfs) refl (here refl) = name , px₁
    loop _ (x ∷ refs) (px ∷ prfs) refl (there ref) = loop _ refs prfs refl ref

liftRefs : ∀ {yss ess} → yss ⊆ ess → (refs : List NamedInbox) → (map justInbox refs) ≡ ess → Σ[ refs' ∈ List NamedInbox ] refs' ⊆ refs × yss ≡ map justInbox refs'
liftRefs [] [] refl = [] , ([] , refl)
liftRefs [] (x ∷ refs) refl = [] , ([] , refl)
liftRefs (keep subs) [] ()
liftRefs (keep subs) (x ∷ refs) refl with (liftRefs subs refs refl)
... | refs' , subs' , refl = (x ∷ refs') , ((keep subs') , refl)
liftRefs (skip subs) [] ()
liftRefs (skip subs) (x ∷ refs) refl with (liftRefs subs refs refl)
... | refs' , subs' , refl = refs' , (skip subs' , refl)
