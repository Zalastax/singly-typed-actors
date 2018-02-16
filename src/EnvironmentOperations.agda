module EnvironmentOperations where
open import ActorMonad
open import SimulationEnvironment
open import Membership-equality using (_∈_)
open import Sublist using (_⊆_ ; [] ; keep ; skip)

open import Data.List using (List ; _∷_ ; [] ; map ; _++_ ; drop)
open import Data.List.All using (All ; _∷_ ; []; lookup) renaming (map to ∀map)
open import Data.List.All.Properties using (++⁺ ; drop⁺)
open import Data.List.Any using (here ; there)
open import Data.Nat using (ℕ ; zero ; suc ; _≟_ ; _<_)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)
open import Data.Unit using (⊤ ; tt)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; trans)
open import Relation.Nullary using (Dec ; yes ; no)

open import Level using (Lift ; lift)

open Actor
open ValidActor
open Env

new-actor : ∀ {IS A ce} → ActorM IS A [] ce → Name → Actor
new-actor {IS} {A} {ce} m name = record
                                        { IS = IS
                                        ; A = A
                                        ; references = []
                                        ; es = []
                                        ; esEqRefs = refl
                                        ; ce = ce
                                        ; act = m
                                        ; name = name
                                        }

lift-actor : (actor : Actor) → {es : List InboxShape} → (references : List NamedInbox) → (esEqRefs : (map justInbox references) ≡ es) → ActorM (IS actor) (A actor) es (ce actor) → Actor
lift-actor actor {es} references esEqRefs m = record
                                              { IS = IS actor
                                              ; A = A actor
                                              ; references = references
                                              ; es = es
                                              ; esEqRefs = esEqRefs
                                              ; ce = ce actor
                                              ; act = m
                                              ; name = name actor
                                              }

-- Replace the monadic part of an actor
replace-actorM : (actor : Actor) → ActorM (IS actor) (A actor) (es actor) (ce actor) → Actor
replace-actorM actor m = record
                           { IS = IS actor
                           ; A = A actor
                           ; references = references actor
                           ; es = es actor
                           ; esEqRefs = esEqRefs actor
                           ; ce = ce actor
                           ; act = m
                           ; name = name actor
                           }

add-reference : (actor : Actor) → (nm : NamedInbox) → ActorM (IS actor) (A actor) (Σ.proj₂ nm ∷ es actor) (ce actor) → Actor
add-reference actor nm m = record
                             { IS = IS actor
                             ; A = A actor
                             ; references = nm ∷ references actor
                             ; es = Σ.proj₂ nm ∷ es actor
                             ; esEqRefs = cong (_∷_ (Σ.proj₂ nm)) (esEqRefs actor)
                             ; ce = ce actor
                             ; act = m
                             ; name = name actor
                             }

record ValidMessageList (store : Store) (S : InboxShape) : Set₁ where
  field
    inbox : List (NamedMessage S)
    valid : All (messageValid store) inbox

record UpdatedInboxes (store : Store) (original : List Inbox) : Set₂ where
  field
    updated-inboxes : List Inbox
    inboxes-valid : All (allMessagesValid store) updated-inboxes
    same-store : inboxesToStore original ≡ inboxesToStore updated-inboxes

open ValidMessageList
open UpdatedInboxes

update-inboxes : {name : Name} → {IS : InboxShape} →
  (store : Store) →
  (inboxes : List Inbox) →
  (All (allMessagesValid store) inboxes) →
  (name ↦ IS ∈e (inboxesToStore inboxes)) →
  (f : ValidMessageList store IS → ValidMessageList store IS) →
  UpdatedInboxes store inboxes
update-inboxes store [] [] () f
update-inboxes store (x ∷ inboxes) (px ∷ proofs) zero f with (f (record { inbox = Inbox.inb x ; valid = px }))
... | updated = record {
  updated-inboxes = updatedInbox ∷ inboxes
  ; inboxes-valid = (valid updated) ∷ proofs
  ; same-store = refl }
  where
    updatedInbox : Inbox
    updatedInbox = record { IS = Inbox.IS x ; inb = inbox updated ; name = Inbox.name x }
update-inboxes store (x ∷ inboxes) (px ∷ proofs) (suc reference) f with (update-inboxes store inboxes proofs reference f)
... | updatedInboxes = record {
  updated-inboxes = x ∷ updated-inboxes updatedInboxes
  ; inboxes-valid = px ∷ inboxes-valid updatedInboxes
  ; same-store = cong (_∷_ ((Inbox.name x) , (Inbox.IS x))) (same-store updatedInboxes) }

-- Update one of the inboxes in a list of inboxes.
-- All the inboxes have been proven to be valid in the context of a store,
-- and the goal is to return a new list of inboxes which are also valid for the same store.
-- We know what inbox to update via an index using the inbox name into the list.
-- The update function receives both a list of messages from the inbox we pointed out,
-- and a proof that all the messages are valid for the store.
-- The update function returns a new list of the same type,
-- and has to provide a proof that this list is also valid for the store
{-updateInboxes :  {name : Name} → ∀ {IS} →
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
... | proj₁ , proj₂ , proj₃ = (x ∷ proj₁) , ((px ∷ proj₂) , cong (λ q → ((Inbox.name x) , Inbox.IS x) ∷ q) proj₃)-}

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
                                 ; inbs=store = cong (_∷_ ((freshName env) , IS)) (inbs=store env)
                                 ; freshName = suc (Env.freshName env)
                                 ; actorsValid = record { hasInb = zero ; points = [] } ∷ ∀map (ValidActorSuc (Env.nameIsFresh env)) (Env.actorsValid env)
                                 ; blockedValid = ∀map (ValidActorSuc (Env.nameIsFresh env)) (Env.blockedValid env)
                                 ; messagesValid = [] ∷ ∀map (λ {x} vi → messagesValidSuc {_} {x} (Env.nameIsFresh env) vi) (Env.messagesValid env)
                                 ; nameIsFresh = Data.Nat.s≤s (≤-reflexive refl) ∷ ∀map  Data.Nat.Properties.≤-step (Env.nameIsFresh env)
                                 }

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
                 (f : ValidMessageList (store env) IS → ValidMessageList (store env) IS) → Env
updateInboxEnv {name} {IS} env p f = record
                           { acts = acts env
                           ; blocked = blocked env
                           ; inbs = updated-inboxes updatedInboxes
                           ; store = store env
                           ; inbs=store = trans (inbs=store env) (same-store updatedInboxes)
                           ; freshName = freshName env
                           ; actorsValid = actorsValid env
                           ; blockedValid = blockedValid env
                           ; messagesValid = inboxes-valid updatedInboxes
                           ; nameIsFresh = nameIsFresh env
                           }
  where
    -- Just some helpers to align the types
    pp : name ↦ IS ∈e (inboxesToStore (Env.inbs env))
    pp rewrite (Env.inbs=store env) = p
    updatedInboxes = update-inboxes (Env.store env) (Env.inbs env) (Env.messagesValid env) pp f

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

record FoundReference (store : Store) (S : InboxShape) : Set₂ where
  field
    name : Name
    reference : name ↦ S ∈e store

-- looks up the pointer for one of the references known by an actor
lookupReference : ∀ {store actor ToIS} → ValidActor store actor → ToIS ∈ (Actor.es actor) → FoundReference store ToIS
lookupReference {store} {actor} {ToIS} va ref = loop (Actor.es actor) (Actor.references actor) (ValidActor.points va) (Actor.esEqRefs actor) ref
  where
    loop : (es : List InboxShape) → (refs : List NamedInbox) → (All (λ ref → Σ.proj₁ ref ↦ Σ.proj₂ ref ∈e store) refs) → (map justInbox refs ≡ es) → ToIS ∈ es → FoundReference store ToIS
    loop .[] [] prfs refl ()
    loop _ ((name , IS) ∷ refs) (reference ∷ prfs) refl (here refl) = record { name = name ; reference = reference }
    loop _ (x ∷ refs) (px ∷ prfs) refl (there ref) = loop _ refs prfs refl ref

record LiftedReferences (lss gss : List InboxShape) (references : List NamedInbox) : Set₂ where
  field
    subset-inbox : lss ⊆ gss
    contained : List NamedInbox
    subset : contained ⊆ references
    contained-eq-inboxes : lss ≡ map justInbox contained

open LiftedReferences

lift-references : ∀ {lss gss} → lss ⊆ gss → (references : List NamedInbox) → map justInbox references ≡ gss → LiftedReferences lss gss references
lift-references [] [] refl = record
                               { subset-inbox = []
                               ; contained = []
                               ; subset = []
                               ; contained-eq-inboxes = refl
                               }
lift-references (keep subs) [] ()
lift-references (skip subs) [] ()
lift-references [] (x ∷ references₁) refl = record
                                              { subset-inbox = []
                                              ; contained = []
                                              ; subset = []
                                              ; contained-eq-inboxes = refl
                                              }
lift-references (keep subs) (x ∷ references) refl with (lift-references subs references refl)
... | lifted = record
                 { subset-inbox = keep subs
                 ; contained = x ∷ contained lifted
                 ; subset = keep (subset lifted)
                 ; contained-eq-inboxes = cong (_∷_ (justInbox x)) (contained-eq-inboxes lifted)
                 }
lift-references (skip subs) (x ∷ references) refl with (lift-references subs references refl)
... | lifted = record
                 { subset-inbox = skip subs
                 ; contained = contained lifted
                 ; subset = skip (subset lifted)
                 ; contained-eq-inboxes = contained-eq-inboxes lifted
                 }

replace-actors : (env : Env) → (actors : List Actor) → All (ValidActor (store env)) actors → Env
replace-actors env actors actorsValid = record {
  acts = actors
  ; blocked = blocked env
  ; inbs = inbs env
  ; store = store env
  ; inbs=store = inbs=store env
  ; freshName = freshName env
  ; actorsValid = actorsValid
  ; blockedValid = blockedValid env
  ; messagesValid = messagesValid env
  ; nameIsFresh = nameIsFresh env
  }

replace-actors+blocked : (env : Env) →
                          (actors : List Actor) → All (ValidActor (store env)) actors →
                          (blocked : List Actor) → All (ValidActor (store env)) blocked → Env
replace-actors+blocked env actors actorsValid blocked blockedValid = record {
  acts = actors
  ; blocked = blocked
  ; inbs = inbs env
  ; store = store env
  ; inbs=store = inbs=store env
  ; freshName = freshName env
  ; actorsValid = actorsValid
  ; blockedValid = blockedValid
  ; messagesValid = messagesValid env
  ; nameIsFresh = nameIsFresh env
  }

add-message : {S : InboxShape} → {store : Store} → (message : NamedMessage S) → messageValid store message → (ValidMessageList store S → ValidMessageList store S)
add-message message valid vml = record { inbox = inbox vml ++ (message ∷ []) ; valid = ++⁺ (ValidMessageList.valid vml) (valid ∷ []) }

remove-message : {S : InboxShape} → {store : Store} → (ValidMessageList store S → ValidMessageList store S)
remove-message vml = record { inbox = drop 1 (inbox vml) ; valid = drop⁺ 1 (ValidMessageList.valid vml) }
