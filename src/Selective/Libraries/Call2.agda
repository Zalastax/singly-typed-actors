module Selective.Libraries.Call2 where

open import Selective.Libraries.Channel public
open import Prelude

open ChannelType
open ChannelInitiation

call : ∀ {Γ i caller} →
        ∀ protocol →
        Request Γ caller protocol →
        ∞ActorM i caller (Message (protocol .response .channel-shape)) Γ (add-references Γ)
call protocol request =
  let
    open ChannelInitiationSession
    open Request
    open ChannelSession
  in do
    initiate-channel _ request
    let rs = request .session .response-session
    from-channel (protocol .response) rs
