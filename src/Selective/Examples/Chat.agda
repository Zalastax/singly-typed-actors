module Selective.Examples.Chat where

open import Selective.ActorMonad public
open import Selective.Examples.Call using (UniqueTag ; call)
open import Data.List using (List ; _∷_ ; [] ; map ; _++_ ; reverse ; _∷ʳ_)
open import Data.List.All using (All ; _∷_ ; [])
open import Data.Bool using (Bool  ; false ; true)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _≟_)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Size
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Membership using (_∈_ ; _⊆_ ; S ; Z ; _∷_ ; [] ; ⊆-refl ; ⊆-suc)
open import Data.Unit using (⊤ ; tt)

open import Data.List.Properties

open import Category.Monad

open import Debug
open import Data.Nat.Show using (show)

RoomName = ℕ
ClientName = ℕ

ClientInterface : InboxShape
Client-to-Room : InboxShape
Room-to-Client : InboxShape

-- =============
--  JOIN ROOM
-- =============

data JoinRoomSuccess : Set where
  JR-SUCCESS : RoomName → JoinRoomSuccess

data JoinRoomFail : Set where
  JR-FAIL : RoomName → JoinRoomFail

data JoinRoomStatus : Set where
  JRS-SUCCESS JRS-FAIL : RoomName → JoinRoomStatus

JoinRoomSuccessReply : MessageType
JoinRoomSuccessReply = ValueType UniqueTag ∷ ValueType JoinRoomSuccess ∷ ReferenceType Client-to-Room ∷ []

JoinRoomFailReply : MessageType
JoinRoomFailReply = ValueType UniqueTag ∷ ValueType JoinRoomFail ∷ []

JoinRoomReplyInterface : InboxShape
JoinRoomReplyInterface = (JoinRoomSuccessReply ∷ JoinRoomFailReply ∷ []) ++ Room-to-Client

JoinRoom : MessageType
JoinRoom = ValueType UniqueTag ∷ ReferenceType JoinRoomReplyInterface ∷ ValueType RoomName ∷ ValueType ClientName ∷ []

-- =============
--  CREATE ROOM
-- =============

data CreateRoomResult : Set where
  CR-SUCCESS CR-EXISTS : RoomName → CreateRoomResult

CreateRoomReply : MessageType
CreateRoomReply = ValueType UniqueTag ∷ ValueType CreateRoomResult ∷ []

CreateRoom : MessageType
CreateRoom = ValueType UniqueTag ∷ ReferenceType (CreateRoomReply ∷ []) ∷ ValueType RoomName ∷ []

-- ============
--  LIST ROOMS
-- ============

RoomList : Set
RoomList = List RoomName

ListRoomsReply : MessageType
ListRoomsReply = ValueType UniqueTag ∷ ValueType RoomList ∷ []

ListRooms : MessageType
ListRooms = ValueType UniqueTag ∷ ReferenceType (ListRoomsReply ∷ []) ∷ []

-- ===
--
-- ===

Client-to-RoomManager : InboxShape
Client-to-RoomManager = JoinRoom ∷ CreateRoom ∷ ListRooms ∷ []

RoomManagerInterface : InboxShape
RoomManagerInterface = Client-to-RoomManager

GetRoomManagerReply : MessageType
GetRoomManagerReply = ValueType UniqueTag ∷ ReferenceType RoomManagerInterface ∷ []

GetRoomManager : MessageType
GetRoomManager = ValueType UniqueTag ∷ ReferenceType (GetRoomManagerReply ∷ []) ∷ []

RoomSupervisorInterface : InboxShape
RoomSupervisorInterface = GetRoomManager ∷ []

ClientSupervisorInterface : InboxShape
ClientSupervisorInterface =
  (ReferenceType RoomSupervisorInterface ∷ [])
  ∷ GetRoomManagerReply
  ∷ []


--
--
--

ChatMessage : MessageType
ChatMessage = ValueType ClientName ∷ ValueType String ∷ []

LeaveRoom : MessageType
LeaveRoom = ValueType ClientName ∷ []

Client-to-Room = ChatMessage ∷ LeaveRoom ∷ []

Room-to-Client = ChatMessage ∷ []

AddToRoom : MessageType
AddToRoom = ValueType ClientName ∷ ReferenceType Room-to-Client ∷ []

RoomManager-to-Room : InboxShape
RoomManager-to-Room = AddToRoom ∷ []

RoomInstanceInterface : InboxShape
RoomInstanceInterface = Client-to-Room ++ RoomManager-to-Room

ClientInterface = (ReferenceType RoomManagerInterface ∷ []) ∷ CreateRoomReply ∷ ListRoomsReply ∷ JoinRoomReplyInterface

-- ======
--  ROOM
-- ======

ClientList : Set
ClientList = List ClientName

record RoomState : Set₁ where
  field
    clients : ClientList


cl-to-context : ClientList → TypingContext
cl-to-context = map λ _ → Room-to-Client

rs-to-context : RoomState → TypingContext
rs-to-context rs = let open RoomState
  in cl-to-context (rs .clients)

record RoomLeave (rs : ClientList) (name : ClientName) : Set₁ where
  field
    filtered : ClientList
    subs : (cl-to-context filtered) ⊆ (cl-to-context rs)

++-temp-fix : (l r : ClientList) → (x : ClientName) → (l ++ (x ∷ r)) ≡ ((l ∷ʳ x) ++ r)
++-temp-fix [] r x = refl
++-temp-fix (x₁ ∷ l) r x = cong (_∷_ x₁) (++-temp-fix l r x)

room-instance : ∀ {i} → ActorM i RoomInstanceInterface RoomState [] rs-to-context
room-instance = begin (loop (record { clients = [] }))
  where
    -- only removes first occurance...
    leave-room : (cl : ClientList) → (name : ClientName) → RoomLeave cl name
    leave-room [] name = record { filtered = [] ; subs = [] }
    leave-room (x ∷ cl) name with (x ≟ name)
    ... | (yes _) = record { filtered = cl ; subs = ⊆-suc ⊆-refl }
    ... | (no _) = let
        rl = leave-room cl name
        open RoomLeave
      in record { filtered = x ∷ rl .filtered ; subs = Z ∷ ⊆-suc (rl .subs) }
    send-to-others : ∀ {i} → (cl : ClientList) →
                     ClientName →
                     String →
                     ∞ActorM i RoomInstanceInterface ⊤₁ (cl-to-context cl) (λ _ → cl-to-context cl)
    send-to-others [] _ _ = return _
    send-to-others cl@(_ ∷ _) name message = send-loop [] cl
      where
        build-pointer : (l r : ClientList) →
                      cl-to-context r ⊢ Room-to-Client →
                      (cl-to-context (l ++ r)) ⊢ Room-to-Client
        build-pointer [] r p = p
        build-pointer (x ∷ l) r p = S (build-pointer l r p)
        recurse : ∀ {i} → (l r : ClientList) → (x : ClientName) →
                  ∞ActorM i RoomInstanceInterface ⊤₁ (cl-to-context (l ++ (x ∷ r))) (λ _ → (cl-to-context (l ++ (x ∷ r))))
        send-loop : ∀ {i} → (l r : ClientList) →
          ∞ActorM i RoomInstanceInterface ⊤₁ (cl-to-context (l ++ r)) (λ _ → cl-to-context (l ++ r))
        send-loop l [] = return _
        send-loop l (x ∷ r) with (x ≟ name)
        ... | (yes _) = recurse l r x
        ... | (no _) = let p = build-pointer l (x ∷ r) Z
          in (p ![t: Z ] ((lift name) ∷ ((lift message) ∷ []))) >> recurse l r x
        recurse l r x rewrite ++-temp-fix l r x = send-loop (l ∷ʳ x) r
    handle-message : ∀ {i} → (rs : RoomState) →
                     (m : Message RoomInstanceInterface) →
                     ∞ActorM i RoomInstanceInterface RoomState (add-references (rs-to-context rs) m) rs-to-context
    -- chat message
    handle-message rs (Msg Z (client-name ∷ message ∷ [])) = do
      let open RoomState
      (send-to-others (rs .clients) client-name message)
      (return₁ rs)
    -- leave room
    handle-message rs (Msg (S Z) (client-name ∷ [])) = do
      let
        open RoomState
        open RoomLeave
        rl = leave-room (rs .clients) client-name
      (strengthen (rl .subs))
      (return₁ (record { clients = rl .filtered }))
    -- add to room
    handle-message rs (Msg (S (S Z)) (client-name ∷ _ ∷ [])) = do
      let open RoomState
      return₁ (record { clients = client-name ∷ rs .clients })
    handle-message rs (Msg (S (S (S ()))) _)
    loop : ∀ {i} →
           (rs : RoomState) →
           ∞ActorM i RoomInstanceInterface RoomState (rs-to-context rs) rs-to-context
    loop state .force = begin do
      m ← receive
      state' ← (handle-message state m)
      return₁ state'

-- ==============
--  ROOM MANAGER
-- ==============

record RoomManagerState : Set₁ where
  field
    rooms : RoomList

rms-to-context : RoomManagerState → TypingContext
rms-to-context rms = rl-to-context (rms .rooms)
  where
    open RoomManagerState
    rl-to-context : RoomList → TypingContext
    rl-to-context = map λ _ → RoomInstanceInterface

lookup-room : ∀ {i} → {Γ : TypingContext} →
              (rms : RoomManagerState) →
              RoomName →
              ∞ActorM i RoomManagerInterface (Maybe ((Γ ++ (rms-to-context rms)) ⊢ RoomInstanceInterface)) (Γ ++ (rms-to-context rms)) (λ _ → Γ ++ (rms-to-context rms))
lookup-room rms name =
  let open RoomManagerState
  in return₁ (loop _ (rms .rooms))
  where
    rl-to-context : RoomList → TypingContext
    rl-to-context = map λ _ → RoomInstanceInterface
    loop : (Γ : TypingContext) → (rl : RoomList) → Maybe ((Γ ++ rl-to-context rl) ⊢ RoomInstanceInterface)
    loop [] [] = nothing
    loop [] (x ∷ xs) with (x ≟ name)
    ... | (yes p) = just Z
    ... | (no _) = RawMonad._>>=_ Maybe.monad (loop [] xs) λ p → just (S p)
    loop (x ∷ Γ) rl = RawMonad._>>=_ Maybe.monad (loop Γ rl) (λ p → just (S p))

room-manager : ∀ {i} → ActorM i RoomManagerInterface RoomManagerState [] rms-to-context
room-manager = begin (loop (record { rooms = [] }))
  where
    handle-room-join : ∀ {i} → {Γ : TypingContext} →
                        UniqueTag →
                        RoomName →
                        ClientName →
                        (Γ ⊢ JoinRoomReplyInterface) →
                        (Maybe (Γ ⊢ RoomInstanceInterface)) →
                        ∞ActorM i RoomManagerInterface ⊤₁ Γ (λ _ → Γ)
    handle-room-join tag room-name client-name cp (just rp) = do
      cp ![t: Z ] ((lift tag) ∷ ((lift (JR-SUCCESS room-name)) ∷ (([ rp ]>: (Z ∷ ((S Z) ∷ []))) ∷ [])))
      rp ![t: S (S Z) ] (lift client-name ∷ ([ cp ]>: ((S (S Z)) ∷ [])) ∷ [])
    handle-room-join tag room-name client-name p nothing =
      p ![t: S Z ] (lift tag ∷ (lift (JR-FAIL room-name) ∷ []))
    handle-create-room : ∀ {i} →
                         (rms : RoomManagerState) →
                         UniqueTag →
                         RoomName →
                         Maybe (((CreateRoomReply ∷ []) ∷ rms-to-context rms) ⊢ RoomInstanceInterface) →
                         ∞ActorM i RoomManagerInterface RoomManagerState ((CreateRoomReply ∷ []) ∷ rms-to-context rms) rms-to-context
    handle-create-room rms tag name (just x) = do
      (Z ![t: Z ] ((lift tag) ∷ ((lift (CR-EXISTS name)) ∷ [])))
      (strengthen (⊆-suc ⊆-refl))
      (return₁ rms)
    handle-create-room rms tag name nothing = do
      (Z ![t: Z ] ((lift tag) ∷ ((lift (CR-SUCCESS name)) ∷ [])))
      (strengthen (⊆-suc ⊆-refl))
      spawn room-instance
      let
        rms' : RoomManagerState
        rms' = (record { rooms = name ∷ RoomManagerState.rooms rms })
      (return₁ rms')
    handle-message : ∀ {i} → (rms : RoomManagerState) →
                     (m : Message RoomManagerInterface) →
                     ∞ActorM i RoomManagerInterface RoomManagerState (add-references (rms-to-context rms) m) rms-to-context
    -- Jooin room
    handle-message state (Msg Z (tag ∷ _ ∷ room-name ∷ client-name ∷ [])) = do
      p ← (lookup-room state room-name)
      handle-room-join tag room-name client-name Z p
      (strengthen (⊆-suc ⊆-refl))
      (return₁ state)
    -- Create room
    handle-message state (Msg (S Z) (tag ∷ _ ∷ name ∷ [])) = do
      p ← lookup-room state name
      handle-create-room state tag name p
    -- List rooms
    handle-message state (Msg (S (S Z)) (tag ∷ _ ∷ [])) = do
      (Z ![t: Z ] ((lift tag) ∷ (lift (RoomManagerState.rooms state) ∷ [])))
      (strengthen (⊆-suc ⊆-refl))
      (return₁ state)
    handle-message state (Msg (S (S (S ()))) _)
    loop : ∀ {i} →
           (rms : RoomManagerState) →
           ∞ActorM i RoomManagerInterface RoomManagerState (rms-to-context rms) rms-to-context
    loop state .force = begin do
      m ← receive
      state' ← handle-message state m
      loop state'

-- =================
--  ROOM SUPERVISOR
-- =================

rs-context : TypingContext
rs-context = RoomManagerInterface ∷ []

-- room-supervisor spawns the room-manager
-- and provides an interface for getting a reference to the current room-manager
-- we don't ever change that instance, but we could if we want
room-supervisor : ∀ {i} → ActorM i RoomSupervisorInterface ⊤₁ [] (λ _ → rs-context)
room-supervisor = begin do
    (spawn room-manager)
    provide-manager-instance
  where
    provide-manager-instance : ∀ {i} → ∞ActorM i RoomSupervisorInterface ⊤₁ rs-context (λ _ → rs-context)
    provide-manager-instance .force = begin do
      (Msg Z (tag ∷ _ ∷ [])) ← receive
        where (Msg (S ()) _)
      (Z ![t: Z ] (lift tag ∷ (([ (S Z) ]>: ⊆-refl) ∷ [])))
      (strengthen (⊆-suc ⊆-refl))
      provide-manager-instance

-- ================
--  CLIENT GENERAL
-- ================


client-get-room-manager : ∀ {i} → ∞ActorM i ClientInterface ⊤₁ [] (λ _ → RoomManagerInterface ∷ [])
client-get-room-manager = do
  record { msg = Msg Z _} ← (selective-receive (λ {
    (Msg Z x₁) → true
    ; (Msg (S _) _) → false
    }))
    where
      record { msg = (Msg (S _) _) ; msg-ok = ()}
  return _

client-create-room : ∀ {i } →
                     {Γ : TypingContext} →
                     Γ ⊢ RoomManagerInterface →
                     UniqueTag →
                     RoomName →
                     ∞ActorM i ClientInterface (Lift CreateRoomResult) Γ (λ _ → Γ)
client-create-room p tag name = do
  record { msg = (Msg (S Z) (_ ∷ cr ∷ [])) } ← (call p (S Z) tag ((lift name) ∷ []) ((S Z) ∷ []) Z)
    where
      record { msg = (Msg Z (_ ∷ _)) ; msg-ok = () }
      record { msg = (Msg (S (S _)) _) ; msg-ok = () }
  return cr

add-if-join-success : TypingContext →
                      Lift {lzero} {lsuc lzero} JoinRoomStatus →
                      TypingContext
add-if-join-success Γ (lift (JRS-SUCCESS x)) = Client-to-Room ∷ Γ
add-if-join-success Γ (lift (JRS-FAIL x)) = Γ

client-join-room : ∀ {i Γ} →
                   Γ ⊢ RoomManagerInterface →
                   UniqueTag →
                   RoomName →
                   ClientName →
                   ∞ActorM i ClientInterface (Lift JoinRoomStatus) Γ (add-if-join-success Γ)
client-join-room p tag room-name client-name = do
    self
    S p ![t: Z ] ((lift tag) ∷ (([ Z ]>: ⊆-suc (⊆-suc (⊆-suc ⊆-refl))) ∷ (lift room-name) ∷ ((lift client-name) ∷ [])))
    (strengthen (⊆-suc ⊆-refl))
    m ← (selective-receive (select-join-reply tag))
    handle-message m
  where
    select-join-reply : UniqueTag → MessageFilter ClientInterface
    select-join-reply tag (Msg Z _) = false
    select-join-reply tag (Msg (S Z) _) = false
    select-join-reply tag (Msg (S (S Z)) _) = false
    select-join-reply tag (Msg (S (S (S Z))) (tag' ∷ _)) = ⌊ tag ≟ tag' ⌋
    select-join-reply tag (Msg (S (S (S (S Z)))) (tag' ∷ _)) = ⌊ tag ≟ tag' ⌋
    select-join-reply tag (Msg (S (S (S (S (S Z))))) x₁) = false
    select-join-reply tag (Msg (S (S (S (S (S (S ())))))) _)
    handle-message : ∀ {tag i Γ} → (m : SelectedMessage (select-join-reply tag)) →
                     ∞ActorM i ClientInterface (Lift JoinRoomStatus)
                       (add-selected-references Γ m) (add-if-join-success Γ)
    handle-message record { msg = (Msg Z _) ; msg-ok = () }
    handle-message record { msg = (Msg (S Z) _) ; msg-ok = () }
    handle-message record { msg = (Msg (S (S Z)) _) ; msg-ok = () }
    handle-message record { msg = (Msg (S (S (S Z))) (_ ∷ JR-SUCCESS room-name ∷ _ ∷ [])) } = return (JRS-SUCCESS room-name)
    handle-message record { msg = (Msg (S (S (S (S Z)))) (_ ∷ JR-FAIL room-name ∷ [])) } = return (JRS-FAIL room-name)
    handle-message record { msg = (Msg (S (S (S (S (S Z))))) _) ; msg-ok = () }
    handle-message record { msg = (Msg (S (S (S (S (S (S ())))))) _) }

client-send-message : ∀ {i  Γ} →
                      Γ ⊢ Client-to-Room →
                      UniqueTag →
                      ClientName →
                      String →
                      ∞ActorM i ClientInterface ⊤₁ Γ (λ _ → Γ)
client-send-message p tag client-name message = p ![t: Z ] ((lift client-name) ∷ ((lift message) ∷ []))
-- ==========
--  CLIENT 1
-- ==========

room1 = 1
name1 = 1

client1 : ∀ {i} → ActorM i ClientInterface ⊤₁ [] (λ _ → [])
client1 = begin do
  client-get-room-manager
  _ ← (client-create-room Z 0 room1)
  lift (JRS-SUCCESS joined-room) ← (client-join-room Z 1 room1 name1)
    where
      (lift (JRS-FAIL failed-room)) → strengthen []
  (client-send-message Z 2 name1 "hej hej")
  (strengthen [])

-- ===================
--  CLIENT SUPERVISOR
-- ===================

cs-context : TypingContext
cs-context = RoomManagerInterface ∷ []

client-supervisor : ∀ {i} → ActorM i ClientSupervisorInterface ⊤₁ [] (λ _ → cs-context)
client-supervisor = begin do
    get-room-manager
    spawn-clients
  where
    get-room-manager : ∀ {i} → ∞ActorM i ClientSupervisorInterface ⊤₁ [] (λ _ → cs-context)
    get-room-manager = do
      record { msg = Msg (S Z) f } ← (selective-receive (λ {
        (Msg Z _) → false
        ; (Msg (S Z) _) → true
        ; (Msg (S (S ())) _)
        }))
        where
          record { msg = (Msg Z _) ; msg-ok = () }
          record { msg = (Msg (S (S ())) _) }
      return _
    spawn-clients : ∀ {i} → ∞ActorM i ClientSupervisorInterface ⊤₁ cs-context (λ _ → cs-context)
    spawn-clients = do
      (spawn client1)
      (strengthen (⊆-suc ⊆-refl))

-- chat-supervisor is the top-most actor
-- it spawns and connects the ClientRegistry to the RoomRegistry
chat-supervisor : ∀ {i} → ∞ActorM i [] ⊤₁ [] (λ _ → [])
chat-supervisor = do
    (spawn room-supervisor)
    (spawn client-supervisor)
    (Z ![t: Z ] (([ (S Z) ]>: ⊆-refl) ∷ []))
    (strengthen [])
