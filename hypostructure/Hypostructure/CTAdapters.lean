import Hypostructure.Core.Strategy
import Hypostructure.CT1.Automation
import Hypostructure.CT2.Automation
import Hypostructure.CT3.Automation
import Hypostructure.CT4.Automation
import Hypostructure.CT5.Automation
import Hypostructure.CT6.Automation
import Hypostructure.CT7.Automation
import Hypostructure.CT8.Automation
import Hypostructure.CT9.Automation
import Hypostructure.CT10.Automation
import Hypostructure.CT11.Automation
import Hypostructure.CT12.Automation
import Hypostructure.CT13.Automation
import Hypostructure.CT14.Automation
import Hypostructure.CT15.Automation
import Hypostructure.CT16.Automation
import Hypostructure.CT17.Automation

/-!
# CT execution adapters

Each canonical CT runner exposes one sealed execution result.  This module
projects only the runner's own terminal and exact check count into Core's
typed `CTExecution`; it does not select a route, rebuild a payload, or accept
an application-provided output.
-/

namespace Hypostructure.CTAdapters

open Hypostructure

universe u

noncomputable def ct1 {Previous : Type u}
    {spec : CT1.Spec Previous} (capability : CT1.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT1.Terminal
  Output := fun _ => CT1.ExecutionResult spec capability
  run := CT1.execute spec capability
  terminal _ result := result.terminal
  checks := fun previous => (CT1.execute spec capability previous).checks
  work := fun previous => (CT1.execute spec capability previous).checks

noncomputable def ct2 {Previous : Type u} {P : Core.Problem}
    {Target : P.Ambient -> Prop} {progress : Core.Progress P}
    {spec : CT2.Spec P Previous}
    (capability : CT2.Capability Target progress spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT2.Terminal
  Output := fun _ => CT2.ExecutionResult capability
  run := CT2.execute capability
  terminal _ result := result.terminal
  checks := fun previous => (CT2.execute capability previous).checks
  work := fun previous => (CT2.execute capability previous).checks

noncomputable def ct3 {Previous : Type u}
    {spec : CT3.Spec Previous} (capability : CT3.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT3.Terminal
  Output := fun _ => CT3.ExecutionResult spec capability
  run := CT3.execute spec capability
  terminal _ result := result.terminal
  checks := fun previous => (CT3.execute spec capability previous).checks
  work := fun previous => (CT3.execute spec capability previous).checks

noncomputable def ct4 {Previous : Type u}
    {spec : CT4.Spec Previous} (capability : CT4.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT4.Terminal
  Output := fun _ => CT4.ExecutionResult spec capability
  run := CT4.execute spec capability
  terminal _ result := result.terminal
  checks := fun previous => (CT4.execute spec capability previous).checks
  work := fun previous => (CT4.execute spec capability previous).checks

noncomputable def ct5 {Previous : Type u}
    {spec : CT5.Spec Previous} (capability : CT5.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT5.Terminal
  Output := fun _ => CT5.ExecutionResult spec capability
  run := CT5.execute spec capability
  terminal _ result := result.terminal
  checks := fun previous => (CT5.execute spec capability previous).checks
  work := fun previous => (CT5.execute spec capability previous).checks

noncomputable def ct6 {Previous : Type u}
    {spec : CT6.Spec Previous} (capability : CT6.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT6.Terminal
  Output := fun _ => CT6.ExecutionResult spec capability
  run := CT6.execute spec capability
  terminal _ result := result.terminal
  checks := fun previous => (CT6.execute spec capability previous).checks
  work := fun previous => (CT6.execute spec capability previous).checks

noncomputable def ct7 {Previous : Type u}
    {spec : CT7.Spec Previous} (capability : CT7.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT7.Terminal
  Output := fun _ => CT7.ExecutionResult spec capability
  run := CT7.execute spec capability
  terminal _ result := result.terminal
  checks := fun previous => (CT7.execute spec capability previous).checks
  work := fun previous => (CT7.execute spec capability previous).checks

noncomputable def ct8 {Previous : Type u}
    {spec : CT8.Spec Previous} (capability : CT8.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT8.Terminal
  Output := fun _ => CT8.ExecutionResult spec capability
  run := CT8.execute capability
  terminal _ result := result.terminal
  checks := fun previous => (CT8.execute capability previous).checks
  work := fun previous => (CT8.execute capability previous).checks

noncomputable def ct9 {Previous : Type u}
    {spec : CT9.Spec Previous} (capability : CT9.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT9.Terminal
  Output := fun _ => CT9.ExecutionResult spec capability
  run := CT9.execute spec capability
  terminal _ result := result.terminal
  checks := fun previous => (CT9.execute spec capability previous).checks
  work := fun previous => (CT9.execute spec capability previous).checks

noncomputable def ct10 {Previous : Type u}
    {spec : CT10.Spec Previous} (capability : CT10.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT10.Terminal
  Output := fun _ => CT10.ExecutionResult spec capability
  run := CT10.execute capability
  terminal _ result := result.terminal
  checks := fun previous => (CT10.execute capability previous).checks
  work := fun previous => (CT10.execute capability previous).checks

noncomputable def ct11 {Previous : Type u}
    {spec : CT11.Spec Previous} (capability : CT11.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT11.Terminal
  Output := fun _ => CT11.ExecutionResult spec capability
  run := CT11.execute spec capability
  terminal _ result := result.terminal
  checks := fun previous => (CT11.execute spec capability previous).checks
  work := fun previous => (CT11.execute spec capability previous).checks

noncomputable def ct12 {Previous : Type u}
    {spec : CT12.Spec Previous} (capability : CT12.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT12.Terminal
  Output := fun _ => CT12.ExecutionResult spec capability
  run := CT12.execute spec capability
  terminal _ result := result.terminal
  checks := fun previous => (CT12.execute spec capability previous).checks
  work := fun previous => (CT12.execute spec capability previous).checks

noncomputable def ct13 {Previous : Type u}
    {spec : CT13.Spec Previous} (capability : CT13.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT13.Terminal
  Output := fun _ => CT13.ExecutionResult spec capability
  run := CT13.execute spec capability
  terminal _ result := result.terminal
  checks := fun previous => (CT13.execute spec capability previous).checks
  work := fun previous => (CT13.execute spec capability previous).checks

noncomputable def ct14 {Previous : Type u}
    {spec : CT14.Spec Previous} (capability : CT14.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT14.Terminal
  Output := fun _ => CT14.ExecutionResult spec capability
  run := CT14.execute spec capability
  terminal _ result := result.terminal
  checks := fun previous => (CT14.execute spec capability previous).checks
  work := fun previous => (CT14.execute spec capability previous).checks

noncomputable def ct15 {Previous : Type u}
    {spec : CT15.Spec Previous} (capability : CT15.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT15.Terminal
  Output := fun _ => CT15.ExecutionResult spec capability
  run := CT15.execute spec capability
  terminal _ result := result.terminal
  checks := fun previous => (CT15.execute spec capability previous).checks
  work := fun previous => (CT15.execute spec capability previous).checks

noncomputable def ct16 {Previous : Type u}
    {spec : CT16.Spec Previous} (capability : CT16.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT16.Terminal
  Output := fun _ => CT16.ExecutionResult spec capability
  run := CT16.execute spec capability
  terminal _ result := result.terminal
  checks := fun previous => (CT16.execute spec capability previous).checks
  work := fun previous => (CT16.execute spec capability previous).checks

noncomputable def ct17 {Previous : Type u}
    {spec : CT17.Spec Previous} (capability : CT17.Capability spec) :
    Core.Strategy.CTExecution Previous where
  Terminal := CT17.Terminal
  Output := fun _ => CT17.ExecutionResult spec capability
  run := CT17.execute spec capability
  terminal _ result := result.terminal
  checks := fun previous => (CT17.execute spec capability previous).checks
  work := fun previous => (CT17.execute spec capability previous).checks

end Hypostructure.CTAdapters
