module Selective.Examples.ChatAO where

open import Selective.ActorMonad
open import Selective.Libraries.Channel
open import Selective.Libraries.Call2
open import Selective.Libraries.ActiveObjects
open import Prelude
  hiding (Maybe)
open import Data.Maybe as Maybe
  hiding (map)

open import Data.List.Properties
open import Category.Monad

open import Debug
open import Data.Nat.Show using (show)

RoomName = ℕ
ClientName = ℕ

Room-to-Client : InboxShape

record Client : Set where
  field
    name : ClientName
    channel : UniqueTag

ClientList : Set
ClientList = List Client

record RoomState : Set₁ where
  field
    clients : ClientList

cl-to-context : ClientList → TypingContext
cl-to-context = map λ _ → Room-to-Client

rs-to-context : RoomState → TypingContext
rs-to-context rs = let open RoomState
  in cl-to-context (rs .clients)

record ChatMessageContent : Set where
  constructor chat-from_message:_
  field
    sender : ClientName
    message : String

SendChatMessage : MessageType
SendChatMessage = [ ValueType ChatMessageContent ]ˡ


ReceiveChatMessage : MessageType
ReceiveChatMessage = ValueType UniqueTag ∷ [ ValueType ChatMessageContent ]ˡ

chat-message-header : ActiveMethod
chat-message-header = VoidMethod [ SendChatMessage ]ˡ

Room-to-Client = [ ReceiveChatMessage ]ˡ

AddToRoom : MessageType
AddToRoom = ValueType UniqueTag ∷ ValueType ClientName ∷ [ ReferenceType Room-to-Client ]ˡ

add-to-room-header : ActiveMethod
add-to-room-header = VoidMethod [ AddToRoom ]ˡ

LeaveRoom : MessageType
LeaveRoom = [ ValueType ClientName ]ˡ

leave-room-header : ActiveMethod
leave-room-header = VoidMethod [ LeaveRoom ]ˡ

room-methods : List ActiveMethod
room-methods = chat-message-header ∷ leave-room-header ∷ [ add-to-room-header ]ˡ

room-inbox = methods-shape room-methods

add-to-room : (active-method room-inbox RoomState rs-to-context add-to-room-header)
add-to-room _ (Msg Z (tag ∷ client-name ∷ _ ∷ [])) state = do
  let
    open RoomState
    state' = record { clients = record { name = client-name ; channel = tag } ∷ state .clients }
  strengthen (Z ∷ ⊆-refl)
  return₁ state'
add-to-room _ (Msg (S ()) _)

record RoomLeave (rs : ClientList) (name : ClientName) : Set₁ where
  field
    filtered : ClientList
    subs : (cl-to-context filtered) ⊆ (cl-to-context rs)

leave-room : (active-method room-inbox RoomState rs-to-context leave-room-header)
leave-room _ (Msg Z (client-name ∷ [])) state = do
    let
      open RoomState
      open RoomLeave
      rl = remove-first-client (state .clients) client-name
      state' = record { clients = rl .filtered }
    debug ("client#" || show client-name || " left the room") (strengthen (rl .subs))
    return₁ state'
  where
    remove-first-client : (cl : ClientList) → (name : ClientName) → RoomLeave cl name
    remove-first-client [] name = record { filtered = [] ; subs = [] }
    remove-first-client (x ∷ cl) name with ((Client.name x) ≟ name)
    ... | (yes _) = record { filtered = cl ; subs = ⊆-suc ⊆-refl }
    ... | (no _) =
      let
        rec = remove-first-client cl name
        open RoomLeave
      in record { filtered = x ∷ rec .filtered ; subs = Z ∷ ⊆-suc (rec .subs) }
leave-room _ (Msg (S ()) _) _

chat-message : (active-method room-inbox RoomState rs-to-context chat-message-header)
chat-message _ (Msg Z ((chat-from sender message: message) ∷ [])) state = do
    let
      open RoomState
      debug-msg = ("room sending " || show (pred (length (state .clients))) ||  " messages from " || show sender || ": " || message)
    debug debug-msg (send-to-others (state .clients) sender message)
    return₁ state
  where
    ++-temp-fix : (l r : ClientList) → (x : Client) → (l ++ (x ∷ r)) ≡ ((l ∷ʳ x) ++ r)
    ++-temp-fix [] r x = refl
    ++-temp-fix (x₁ ∷ l) r x = cong (_∷_ x₁) (++-temp-fix l r x)
    send-to-others : ∀ {i} → (cl : ClientList) →
                     ClientName →
                     String →
                     ∞ActorM i room-inbox ⊤₁ (cl-to-context cl) (λ _ → cl-to-context cl)
    send-to-others [] _ _ = return _
    send-to-others cl@(_ ∷ _) name message = send-loop [] cl
      where
        build-pointer : (l r : ClientList) →
                      cl-to-context r ⊢ Room-to-Client →
                      (cl-to-context (l ++ r)) ⊢ Room-to-Client
        build-pointer [] r p = p
        build-pointer (x ∷ l) r p = S (build-pointer l r p)
        recurse : ∀ {i} → (l r : ClientList) → (x : Client) →
                  ∞ActorM i room-inbox ⊤₁ (cl-to-context (l ++ (x ∷ r))) (λ _ → (cl-to-context (l ++ (x ∷ r))))
        send-loop : ∀ {i} → (l r : ClientList) →
          ∞ActorM i room-inbox ⊤₁ (cl-to-context (l ++ r)) (λ _ → cl-to-context (l ++ r))
        send-loop l [] = return _
        send-loop l (x ∷ r) with ((Client.name x) ≟ name)
        ... | (yes _) = recurse l r x
        ... | (no _) = let p = build-pointer l (x ∷ r) Z
          in debug ("Sending to " || show (Client.name x) || ": " || message) (p ![t: Z ] (lift (Client.channel x) ∷ [ lift (chat-from name message: message) ]ᵃ) ) >> recurse l r x
        recurse l r x rewrite ++-temp-fix l r x = send-loop (l ∷ʳ x) r
chat-message _ (Msg (S ()) _) _

room : ActiveObject
room = record {
  state-type = RoomState
  ; vars = rs-to-context
  ; methods = room-methods
  ; extra-messages = []
  ; handlers = chat-message ∷ leave-room ∷ [ add-to-room ]ᵃ
  }

Client-to-Room : InboxShape
Client-to-Room = SendChatMessage ∷ [ LeaveRoom ]ˡ

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
JoinRoomSuccessReply = ValueType UniqueTag ∷ ValueType JoinRoomSuccess ∷ [ ReferenceType Client-to-Room ]ˡ

JoinRoomFailReply : MessageType
JoinRoomFailReply = ValueType UniqueTag ∷ [ ValueType JoinRoomFail ]ˡ

JoinRoomReplyInterface : InboxShape
JoinRoomReplyInterface = JoinRoomSuccessReply ∷ JoinRoomFailReply ∷ Room-to-Client

JoinRoom : MessageType
JoinRoom = ValueType UniqueTag ∷ ReferenceType JoinRoomReplyInterface ∷ ValueType RoomName ∷ [ ValueType ClientName ]ˡ

-- =============
--  CREATE ROOM
-- =============

data CreateRoomResult : Set where
  CR-SUCCESS CR-EXISTS : RoomName → CreateRoomResult

CreateRoomReply : MessageType
CreateRoomReply = ValueType UniqueTag ∷ [ ValueType CreateRoomResult ]ˡ

CreateRoom : MessageType
CreateRoom = ValueType UniqueTag ∷ ReferenceType [ CreateRoomReply ]ˡ ∷ [ ValueType RoomName ]ˡ

-- ============
--  LIST ROOMS
-- ============

RoomList : Set
RoomList = List RoomName

ListRoomsReply : MessageType
ListRoomsReply = ValueType UniqueTag ∷ [ ValueType RoomList ]ˡ

ListRooms : MessageType
ListRooms = ValueType UniqueTag ∷ [ ReferenceType [ ListRoomsReply ]ˡ ]ˡ

-- ===
--
-- ===

Client-to-RoomManager : InboxShape
Client-to-RoomManager = JoinRoom ∷ CreateRoom ∷ [ ListRooms ]ˡ

RoomManagerInterface : InboxShape
RoomManagerInterface = Client-to-RoomManager

GetRoomManagerReply : MessageType
GetRoomManagerReply = ValueType UniqueTag ∷ [ ReferenceType RoomManagerInterface ]ˡ

GetRoomManager : MessageType
GetRoomManager = ValueType UniqueTag ∷ [ ReferenceType [ GetRoomManagerReply ]ˡ ]ˡ

get-room-manager-ci : ChannelInitiation
get-room-manager-ci = record {
  request = [ GetRoomManager ]ˡ
  ; response = record {
    channel-shape = [ GetRoomManagerReply ]ˡ
    ; all-tagged = (HasTag _) ∷ [] }
  ; request-tagged = (HasTag+Ref _) ∷ []
  }

get-room-manager-header : ActiveMethod
get-room-manager-header = ResponseMethod get-room-manager-ci

RoomSupervisorInterface : InboxShape
RoomSupervisorInterface = [ GetRoomManager ]ˡ

ClientSupervisorInterface : InboxShape
ClientSupervisorInterface =
  [ ReferenceType RoomSupervisorInterface ]ˡ ∷ [ GetRoomManagerReply ]ˡ


--
--
--

-- ======================
--  ROOM MANAGER METHODS
-- ======================

join-room-header : ActiveMethod
join-room-header = VoidMethod [ JoinRoom ]ˡ

create-room-ci : ChannelInitiation
create-room-ci = record {
  request = [ CreateRoom ]ˡ
  ; response = record {
    channel-shape = [ CreateRoomReply ]ˡ
    ; all-tagged = (HasTag _) ∷ [] }
  ; request-tagged = (HasTag+Ref _) ∷ []
  }

create-room-header : ActiveMethod
create-room-header = ResponseMethod create-room-ci

list-rooms-header : ActiveMethod
list-rooms-header = ResponseMethod (record {
  request = [ ListRooms ]ˡ
  ; response = record {
    channel-shape = [ ListRoomsReply ]ˡ
    ; all-tagged = (HasTag _) ∷ []
    }
  ; request-tagged = (HasTag+Ref _) ∷ []
  })

record RoomManagerState : Set₁ where
  field
    rooms : RoomList

rms-to-context : RoomManagerState → TypingContext
rms-to-context rms =
  let
    open RoomManagerState
    rl-to-context : RoomList → TypingContext
    rl-to-context = map λ _ → room-inbox
  in rl-to-context (rms .rooms)

room-manager-methods : List ActiveMethod
room-manager-methods = join-room-header ∷ create-room-header ∷ [ list-rooms-header ]ˡ

room-manager-inbox = methods-shape room-manager-methods

list-rooms : active-method room-manager-inbox RoomManagerState rms-to-context list-rooms-header
list-rooms _ msg state =
  let
    open RoomManagerState
  in return₁ (record {
    new-state = state
    ; reply = SendM Z ((lift (state .rooms)) ∷ [])
    })

lookup-room : ∀ {i} → {Γ : TypingContext} →
              (rms : RoomManagerState) →
              RoomName →
              ∞ActorM i room-manager-inbox (Maybe ((Γ ++ (rms-to-context rms)) ⊢ room-inbox)) (Γ ++ (rms-to-context rms)) (λ _ → Γ ++ (rms-to-context rms))
lookup-room rms name =
    let open RoomManagerState
    in return₁ (loop _ (rms .rooms))
    where
      rl-to-context : RoomList → TypingContext
      rl-to-context = map λ _ → room-inbox
      loop : (Γ : TypingContext) → (rl : RoomList) → Maybe ((Γ ++ rl-to-context rl) ⊢ room-inbox)
      loop [] [] = nothing
      loop [] (x ∷ xs) with (x ≟ name)
      ... | (yes p) = just Z
      ... | (no _) = RawMonad._>>=_ Maybe.monad (loop [] xs) λ p → just (S p)
      loop (x ∷ Γ) rl = RawMonad._>>=_ Maybe.monad (loop Γ rl) (λ p → just (S p))

create-room : active-method room-manager-inbox RoomManagerState rms-to-context create-room-header
create-room _ input@(_ sent Msg Z (room-name ∷ [])) state = do
    p ← lookup-room state room-name
    handle-create-room p
  where
    open ResponseInput
    return-type = ActiveReply create-room-ci RoomManagerState rms-to-context input
    precondition = reply-state-vars rms-to-context input state
    postcondition = reply-vars rms-to-context input
    handle-create-room : ∀ {i} → Maybe (precondition ⊢ room-inbox) →
                         ∞ActorM i
                           room-manager-inbox
                           return-type
                           precondition
                           postcondition
    handle-create-room (just x) = return₁ (record { new-state = state ; reply = SendM Z ((lift (CR-EXISTS room-name)) ∷ []) })
    handle-create-room nothing = do
      spawn∞ (run-active-object room (record { clients = [] }))
      let
        open RoomManagerState
        state' : RoomManagerState
        state' = record { rooms = room-name ∷ state .rooms}
      strengthen ((S Z) ∷ (Z ∷ (⊆-suc (⊆-suc ⊆-refl))))
      return₁ (record { new-state = state' ; reply = SendM Z ((lift (CR-SUCCESS room-name)) ∷ []) })
create-room _ (_ sent Msg (S ()) _) _

join-room : active-method room-manager-inbox RoomManagerState rms-to-context join-room-header
join-room _ (Msg Z (tag ∷ _ ∷ room-name ∷ client-name ∷ [])) state = do
    p ← lookup-room state room-name
    handle-join-room p Z
    return₁ state
  where
    handle-join-room : ∀ {i Γ} → Maybe (Γ ⊢ room-inbox) → Γ ⊢ JoinRoomReplyInterface → ∞ActorM i room-manager-inbox ⊤₁ Γ (λ _ → Γ)
    handle-join-room (just rp) cp = do
      (rp ![t: S (S Z) ] ((lift tag) ∷ ((lift client-name) ∷ (([ cp ]>: [ S (S Z) ]ᵐ) ∷ []))))
      (cp ![t: Z ] ((lift tag) ∷ ((lift (JR-SUCCESS room-name)) ∷ (([ rp ]>: (Z ∷ [ S Z ]ᵐ)) ∷ []))))
    handle-join-room nothing cp = cp ![t: S Z ] ((lift tag) ∷ ((lift (JR-FAIL room-name)) ∷ []))
join-room _ (Msg (S ()) _) _

room-manager : ActiveObject
room-manager = record {
  state-type = RoomManagerState
  ; vars = rms-to-context
  ; methods = room-manager-methods
  ; extra-messages = []
  ; handlers = join-room ∷ (create-room ∷ (list-rooms ∷ []))
  }

-- =================
--  ROOM SUPERVISOR
-- =================

rs-context : TypingContext
rs-context = [ room-manager-inbox ]ˡ

rs-vars : ⊤₁ → TypingContext
rs-vars _ = rs-context

room-supervisor-methods : List ActiveMethod
room-supervisor-methods = [ get-room-manager-header ]ˡ

rs-inbox = methods-shape room-supervisor-methods

get-room-manager-handler : active-method rs-inbox ⊤₁ rs-vars get-room-manager-header
get-room-manager-handler _ (_ sent Msg Z received-fields) _ = return₁ (record { new-state = _ ; reply = SendM Z [ [ (S Z) ]>: ⊆-refl ]ᵃ })
get-room-manager-handler _ (_ sent Msg (S ()) _) _

room-supervisor-ao : ActiveObject
room-supervisor-ao = record
                       { state-type = ⊤₁
                       ; vars = λ _ → rs-context
                       ; methods = room-supervisor-methods
                       ; extra-messages = []
                       ; handlers = [ get-room-manager-handler ]ᵃ
                       }

-- room-supervisor spawns the room-manager
-- and provides an interface for getting a reference to the current room-manager
-- we don't ever change that instance, but we could if we want
room-supervisor : ∀ {i} → ActorM i RoomSupervisorInterface ⊤₁ [] (λ _ → rs-context)
room-supervisor = begin do
    spawn∞ (run-active-object room-manager (record { rooms = [] }))
    run-active-object room-supervisor-ao _

-- ================
--  CLIENT GENERAL
-- ================
ClientInterface : InboxShape
ClientInterface = [ ReferenceType RoomManagerInterface ]ˡ ∷ CreateRoomReply ∷ ListRoomsReply ∷ JoinRoomReplyInterface

busy-wait : ∀ {i IS Γ} → ℕ → ∞ActorM i IS ⊤₁ Γ (λ _ → Γ)
busy-wait zero = return _
busy-wait (suc n) = return tt >> busy-wait n

client-get-room-manager : ∀ {i} → ∞ActorM i ClientInterface ⊤₁ [] (λ _ → [ RoomManagerInterface ]ˡ)
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
                     ∞ActorM i ClientInterface (Lift (lsuc lzero) CreateRoomResult) Γ (λ _ → Γ)
client-create-room p tag name = do
  Msg Z (_ ∷ cr ∷ []) ← (call create-room-ci (record {
    var = p
    ; chosen-field = Z
    ; fields = (lift name) ∷ []
    ; session = record {
      can-request = (S Z) ∷ []
      ; response-session = record {
      can-receive = (S Z) ∷ []
      ; tag = tag
      }
      }
      }))
    where
      Msg (S ()) _
  return cr

add-if-join-success : TypingContext →
                      Lift (lsuc lzero) JoinRoomStatus →
                      TypingContext
add-if-join-success Γ (lift (JRS-SUCCESS x)) = Client-to-Room ∷ Γ
add-if-join-success Γ (lift (JRS-FAIL x)) = Γ

client-join-room : ∀ {i Γ} →
                   Γ ⊢ RoomManagerInterface →
                   UniqueTag →
                   RoomName →
                   ClientName →
                   ∞ActorM i ClientInterface (Lift (lsuc lzero) JoinRoomStatus) Γ (add-if-join-success Γ)
client-join-room p tag room-name client-name = do
    self
    S p ![t: Z ] (lift tag ∷ (([ Z ]>: ⊆-suc (⊆-suc (⊆-suc ⊆-refl))) ∷ (lift room-name) ∷ [ lift client-name ]ᵃ))
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
                     ∞ActorM i ClientInterface (Lift (lsuc lzero) JoinRoomStatus)
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
                      ClientName →
                      String →
                      ∞ActorM i ClientInterface ⊤₁ Γ (λ _ → Γ)
client-send-message p client-name message = p ![t: Z ] ([ lift (chat-from client-name message: message) ]ᵃ)

client-receive-message : ∀ {i Γ} →
                         ∞ActorM i ClientInterface (Lift (lsuc lzero) ChatMessageContent) Γ (λ _ → Γ)
client-receive-message = do
    m ← (selective-receive select-message)
    handle-message m
  where
    select-message : MessageFilter ClientInterface
    select-message (Msg (S (S (S (S (S Z))))) _) = true
    select-message (Msg _ _) = false
    handle-message : ∀ {i Γ} → (m : SelectedMessage select-message) →
                     ∞ActorM i ClientInterface (Lift (lsuc lzero) ChatMessageContent) (add-selected-references Γ m) (λ _ → Γ)
    handle-message record { msg = (Msg Z _) ; msg-ok = () }
    handle-message record { msg = (Msg (S Z) _) ; msg-ok = () }
    handle-message record { msg = (Msg (S (S Z)) _) ; msg-ok = () }
    handle-message record { msg = (Msg (S (S (S Z))) x₁) ; msg-ok = () }
    handle-message record { msg = (Msg (S (S (S (S Z)))) _) ; msg-ok = () }
    handle-message record { msg = (Msg (S (S (S (S (S Z))))) (_ ∷ m ∷ f)) ; msg-ok = _ } = return m
    handle-message record { msg = (Msg (S (S (S (S (S (S ())))))) _) }

client-leave-room : ∀ {i Γ} →
                    Γ ⊢ Client-to-Room →
                    ClientName →
                    ∞ActorM i ClientInterface ⊤₁ Γ (λ _ → Γ)
client-leave-room p name = p ![t: S Z ] [ lift name ]ᵃ

debug-chat : {a : Level} {A : Set a} → ClientName → ChatMessageContent → A → A
debug-chat client-name content = let open ChatMessageContent
  in debug ("client#" || show client-name || " received \"" || content .message || "\" from client#" || show (content .sender))

-- ==========
--  CLIENT 1
-- ==========

room1-2 = 1
room2-3 = 2
room3-1 = 3
room1-2-3 = 4
name1 = 1

client1 : ∀ {i} → ActorM i ClientInterface ⊤₁ [] (λ _ → [])
client1 = begin do
  client-get-room-manager
  _ ← (client-create-room Z 0 room1-2)
  _ ← (client-create-room Z 1 room3-1)
  _ ← (client-create-room Z 2 room1-2-3)
  lift (JRS-SUCCESS joined-room) ← (client-join-room Z 3 room3-1 name1)
    where
      (lift (JRS-FAIL failed-room)) → strengthen []
  lift (JRS-SUCCESS joined-room) ← (client-join-room (S Z) 4 room1-2 name1)
    where
      (lift (JRS-FAIL failed-room)) → strengthen []
  lift (JRS-SUCCESS joined-room) ← (client-join-room (S (S Z)) 5 room1-2-3 name1)
    where
      (lift (JRS-FAIL failed-room)) → strengthen []
  busy-wait 100
  (client-send-message (S Z) name1 "hi from 1 to 2")
  (client-send-message Z name1 "hi from 1 to 2-3")
  let open ChatMessageContent
  lift m1 ← client-receive-message
  lift m2 ← debug-chat name1 m1 client-receive-message
  lift m3 ← debug-chat name1 m2 client-receive-message
  debug-chat name1 m3 (client-send-message Z name1 "hi1 from 1 to 2-3")
  (client-send-message Z name1 "hi2 from 1 to 2-3")
  (client-send-message Z name1 "hi3 from 1 to 2-3")
  client-leave-room (S Z) name1
  client-leave-room (Z) name1
  (strengthen [])

-- ==========
--  CLIENT 2
-- ==========

name2 = 2

client2 : ∀ {i} → ActorM i ClientInterface ⊤₁ [] (λ _ → [])
client2 = begin do
  client-get-room-manager
  _ ← (client-create-room Z 0 room1-2)
  _ ← (client-create-room Z 1 room2-3)
  _ ← (client-create-room Z 2 room1-2-3)
  lift (JRS-SUCCESS joined-room) ← (client-join-room Z 3 room1-2 name2)
    where
    (lift (JRS-FAIL failed-room)) → strengthen []
  lift (JRS-SUCCESS joined-room) ← (client-join-room (S Z) 4 room2-3 name2)
    where
      (lift (JRS-FAIL failed-room)) → strengthen []
  lift (JRS-SUCCESS joined-room) ← (client-join-room (S (S Z)) 5 room1-2-3 name2)
    where
      (lift (JRS-FAIL failed-room)) → strengthen []
  busy-wait 100
  debug "client2 send message" (client-send-message (S Z) name2 "hi from 2 to 3")
  debug "client2 send message" (client-send-message Z name2 "hi from 2 to 1-3")
  let open ChatMessageContent
  lift m1 ← client-receive-message
  lift m2 ← debug-chat name2 m1 client-receive-message
  lift m3 ← debug-chat name2 m2 client-receive-message
  client-leave-room (S Z) name2
  client-leave-room (Z) name2
  debug-chat name2 m3 (strengthen [])

-- ==========
--  CLIENT 3
-- ==========

name3 = 3

client3 : ∀ {i} → ActorM i ClientInterface ⊤₁ [] (λ _ → [])
client3 = begin do
  client-get-room-manager
  _ ← (client-create-room Z 0 room2-3)
  _ ← (client-create-room Z 1 room3-1)
  _ ← (client-create-room Z 2 room1-2-3)
  lift (JRS-SUCCESS joined-room) ← (client-join-room Z 3 room2-3 name3)
    where
    (lift (JRS-FAIL failed-room)) → strengthen []
  lift (JRS-SUCCESS joined-room) ← (client-join-room (S Z) 4 room3-1 name3)
    where
      (lift (JRS-FAIL failed-room)) → strengthen []
  lift (JRS-SUCCESS joined-room) ← (client-join-room (S (S Z)) 5 room1-2-3 name3)
    where
      (lift (JRS-FAIL failed-room)) → strengthen []
  busy-wait 100
  debug "client3 send message" (client-send-message (S Z) name3 "hi from 3 to 1")
  debug "client3 send message" (client-send-message Z name3 "hi from 3 to 1-2")
  let open ChatMessageContent
  lift m1 ← client-receive-message
  lift m2 ← debug-chat name3 m1 client-receive-message
  lift m3 ← debug-chat name3 m2 client-receive-message
  debug-chat name3 m3 (client-leave-room Z name3)
  client-leave-room (S Z) name3
  client-leave-room Z name3
  (strengthen [])

-- ===================
--  CLIENT SUPERVISOR
-- ===================

cs-context : TypingContext
cs-context = RoomManagerInterface ∷ RoomSupervisorInterface ∷ []

client-supervisor : ∀ {i} → ActorM i ClientSupervisorInterface ⊤₁ [] (λ _ → cs-context)
client-supervisor = begin do
    wait-for-room-supervisor
    (get-room-manager Z 0)
    spawn-clients
  where
    wait-for-room-supervisor : ∀ {i Γ} → ∞ActorM i ClientSupervisorInterface ⊤₁ Γ (λ _ → RoomSupervisorInterface ∷ Γ)
    wait-for-room-supervisor = do
      record { msg = Msg Z f } ← (selective-receive (λ {
        (Msg Z _) → true
        ; (Msg (S _) _) → false
        }))
        where
          record { msg = (Msg (S _) _) ; msg-ok = () }
      return _
    get-room-manager : ∀ {i Γ} →
                     Γ ⊢ RoomSupervisorInterface →
                     UniqueTag →
                      ∞ActorM i ClientSupervisorInterface ⊤₁ Γ (λ _ → RoomManagerInterface ∷ Γ)
    get-room-manager p tag = do
      Msg Z f ← (call get-room-manager-ci (record {
          var = p
          ; chosen-field = Z
          ; fields = []
          ; session = record {
            can-request = ⊆-refl
            ; response-session = record {
            can-receive = (S Z) ∷ []
            ; tag = tag }
            }
          }))
        where
          Msg (S ()) _
      return _
    spawn-clients : ∀ {i} → ∞ActorM i ClientSupervisorInterface ⊤₁ cs-context (λ _ → cs-context)
    spawn-clients = do
      spawn client1
      Z ![t: Z ] [ [ S Z ]>: ⊆-refl ]ᵃ
      (strengthen (⊆-suc ⊆-refl))
      (spawn client2)
      Z ![t: Z ] [ [ S Z ]>: ⊆-refl ]ᵃ
      (strengthen (⊆-suc ⊆-refl))
      (spawn client3)
      Z ![t: Z ] [ [ S Z ]>: ⊆-refl ]ᵃ
      (strengthen (⊆-suc ⊆-refl))

-- chat-supervisor is the top-most actor
-- it spawns and connects the ClientRegistry to the RoomRegistry
chat-supervisor : ∀ {i} → ∞ActorM i [] ⊤₁ [] (λ _ → [])
chat-supervisor = do
    spawn room-supervisor
    spawn client-supervisor
    Z ![t: Z ] [ [ S Z ]>: ⊆-refl ]ᵃ
    strengthen []

