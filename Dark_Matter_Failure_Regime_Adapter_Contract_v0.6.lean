/-!
===============================================================================
DARK-MATTER FAILURE-REGIME ADAPTER / CONTRACT v0.6
===============================================================================

PUBLIC PACKAGE ARCHITECTURE
---------------------------
This is the single cumulative dark-matter experiment adapter / contract Lean file.
The Structural Flow Universal Kernel is a separate file in the same release package.

LOAD ORDER
----------
1. compatible Structural Flow Universal Kernel supplied with the release package;
2. THIS FILE.

The release manifest owns the exact compatible file identities, versions, and hashes.
This adapter does not hard-code an anchor edition merely because a later compatible
scientific edition is released.

SCIENTIFIC AUTHORITY
--------------------
Five Failure Regimes in Dark-Matter Light Probes:
An Open-Source Pre-Result Demonstration Protocol.

Use the governing accepted edition supplied with the release package. The stable
anchor title identifies the scientific authority; exact release identity belongs to
the package manifest.

MACHINE ROLE
------------
The Universal Kernel supplies reusable universal theorems. This file supplies the
dark-matter experiment's domain-owned adapters, contracts, blockers, result routes,
and conditional certificates. It does not modify or replace the Universal Kernel,
adjudicate empirical truth, or manufacture scientific premises.

INTERNAL PARTITIONS
-------------------
Layers A-D are audit / code-organization partitions inside this one public adapter.
They are not separate release artifacts.
===============================================================================
-/
/-!
===============================================================================
DARK-MATTER FAILURE-REGIME ADAPTER / CONTRACT — INTERNAL LAYER A
===============================================================================

INTERNAL ROLE
-------------
Layer A is the route-admission / first-break partition of the cumulative adapter.
Its semantics are governed by the accepted scientific anchor named in the release
header and by the compatible Universal Kernel supplied with the package.

ROLE
----
Layer A formalizes the route-admission / first-break interface only.
It is intentionally narrower than the complete dark-matter experiment.

The central integration problem is that the scientific anchor uses a four-state
condition vocabulary:

  PASS / FAIL / NOT-LIVE / UNRESOLVED

while StructuralFlow.FailureClosure.RouteSnapshot uses propositions.
This append therefore does NOT coerce NOT-LIVE or UNRESOLVED to false.
Instead it provides:

1. experiment-owned four-state route records;
2. prefix-sensitive first-break evidence;
3. explicit admission / freeze burdens;
4. a compatibility relation to kernel snapshots that constrains only
   scientifically adjudicated PASS / FAIL conditions;
5. a separate fully-live / resolved projection for the anchor's derived
   first-break depth d(pi);
6. firewalls separating route classification, J_ROUTE, object identity,
   primary-scale confirmatory claims, and held-out-probe evidence.

SCIENTIFIC NON-CLAIMS
---------------------
A Lean proof in this append does not establish:
* that a dark-matter candidate is physically warranted;
* that a registered route is scientifically admissible;
* that any empirical route has a particular condition status;
* that J_ROUTE was competently measured;
* that a held-out probe was genuinely excluded from classification;
* that a route-level class applies to an entire dark-matter object;
* that a secondary diagnostic scale owns the confirmatory closure result;
* that PASS is universal immunity from later failure;
* that a route-level residual is an SRW;
* that five-regime closure has survived or been reopened empirically.
===============================================================================
-/

open StructuralFlow.UniversalTranslationContract

namespace StructuralFlow
namespace DarkMatterFailureRegimeLayerA

/-! --------------------------------------------------------------------------
Experiment-owned status vocabulary
---------------------------------------------------------------------------- -/

/--
Scientific state of one registered first-break condition.

`notLive` is intentionally distinct from both `pass` and `fail`.
`unresolved` is intentionally distinct from all three adjudicated states.
-/
inductive ConditionStatus where
  | pass
  | fail
  | notLive
  | unresolved
  deriving DecidableEq, Repr

/-- Domain-native J_ROUTE result. -/
inductive JRouteStatus where
  | pass
  | fail
  | unresolved
  deriving DecidableEq, Repr

/-- The five registered condition seats in prerequisite order. -/
inductive Condition where
  | p0
  | pl
  | boundary
  | cascade
  | authorization
  deriving DecidableEq, Repr

/-- The five named first-break classes already owned universally by the kernel. -/
inductive FirstBreakClass where
  | dissolution
  | shear
  | drift
  | echo
  | lock
  deriving DecidableEq, Repr

/--
Scale role of one route-level result.
A secondary result remains reportable but cannot replace the registered primary
confirmatory result.
-/
inductive ScaleRole where
  | primary
  | secondary
  deriving DecidableEq, Repr

/-- Experimental four-state vector G = (P0, Pl, B, C, A). -/
structure StateVector where
  p0 : ConditionStatus
  pl : ConditionStatus
  boundary : ConditionStatus
  cascade : ConditionStatus
  authorization : ConditionStatus
  deriving Repr

/-- Read one named condition from G. -/
def statusAt (g : StateVector) : Condition -> ConditionStatus
  | .p0 => g.p0
  | .pl => g.pl
  | .boundary => g.boundary
  | .cascade => g.cascade
  | .authorization => g.authorization

/-- One route-level experimental record. Object and route identifiers are typed separately. -/
structure RouteRecord (ObjectId RouteId ScaleId : Type) where
  objectId : ObjectId
  routeId : RouteId
  scaleId : ScaleId
  scaleRole : ScaleRole
  produced : Prop
  jRoute : JRouteStatus
  g : StateVector

/-! --------------------------------------------------------------------------
Layer-A entry / freeze contract
---------------------------------------------------------------------------- -/

/--
Pre-outcome burdens that must be discharged before a route-level first-break
classification is licensed as confirmatory machine input.

The scientific protocol supplies the evidence. Lean checks only the encoded
burden state and the consequences attached to it.
-/
inductive EntryBurden where
  | physicalCandidateWarrant
  | mechanismAdmission
  | participationRelationPinned
  | minimumAdmissibleRoute
  | primaryScaleOwnershipFrozen
  | jRouteCriterionFrozen
  | capacityTestsFrozen
  | intrinsicInputBoundaryPinned
  | heldOutProbeExcluded
  | preTargetFreezeIntact
  deriving DecidableEq, Repr

/-- Layer-A contract packet. -/
structure Contract (ObjectId RouteId ScaleId : Type) where
  record : RouteRecord ObjectId RouteId ScaleId
  entryState : EntryBurden -> Disposition
  entryEvidence : EntryBurden -> Disposition -> Prop
  entryWarrant : forall b, entryEvidence b (entryState b)

/-- Every Layer-A entry burden is discharged. -/
def EntryReady {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId) : Prop :=
  forall b, c.entryState b = Disposition.discharged

/-- A located violated entry burden makes the confirmatory entry surface unusable. -/
def EntryViolated {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId) : Prop :=
  exists b, c.entryState b = Disposition.violated

/-- A located open entry burden leaves the confirmatory entry surface unresolved. -/
def EntryOpen {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId) : Prop :=
  exists b, c.entryState b = Disposition.open

theorem violated_entry_blocks_ready
    {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId)
    (h : EntryViolated c) :
    ¬ EntryReady c := by
  intro hReady
  rcases h with ⟨b, hb⟩
  have hDischarged := hReady b
  rw [hb] at hDischarged
  contradiction

theorem open_entry_blocks_ready
    {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId)
    (h : EntryOpen c) :
    ¬ EntryReady c := by
  intro hReady
  rcases h with ⟨b, hb⟩
  have hDischarged := hReady b
  rw [hb] at hDischarged
  contradiction

/-! --------------------------------------------------------------------------
Status semantics and primitive firewalls
---------------------------------------------------------------------------- -/

def LiveResolved (s : ConditionStatus) : Prop :=
  s = .pass ∨ s = .fail

/-- A live condition carries no first break exactly when it passes. A NOT-LIVE condition is separately acceptable for the domain-level no-break control. -/
def NoBreakAtSeat (s : ConditionStatus) : Prop :=
  s = .pass ∨ s = .notLive

/-- All five condition seats are live and resolved. -/
def FullyLiveResolved (g : StateVector) : Prop :=
  LiveResolved g.p0
  ∧ LiveResolved g.pl
  ∧ LiveResolved g.boundary
  ∧ LiveResolved g.cascade
  ∧ LiveResolved g.authorization

/-- No known first break occurs among the physically live registered conditions. -/
def NoLiveFoundationalBreak (g : StateVector) : Prop :=
  NoBreakAtSeat g.p0
  ∧ NoBreakAtSeat g.pl
  ∧ NoBreakAtSeat g.boundary
  ∧ NoBreakAtSeat g.cascade
  ∧ NoBreakAtSeat g.authorization

/-- Positive prerequisite consistency stated in the anchor for fully live / resolved routes. -/
def PrerequisiteConsistent (g : StateVector) : Prop :=
  (g.pl = .pass -> g.p0 = .pass)
  ∧ (g.boundary = .pass -> g.pl = .pass)
  ∧ (g.cascade = .pass -> g.boundary = .pass)
  ∧ (g.authorization = .pass -> g.cascade = .pass)

/-- A condition is live for the registered route exactly when it is not marked NOT-LIVE. -/
def LiveAtSeat (s : ConditionStatus) : Prop :=
  s ≠ .notLive

/--
Pressure-repair A-02. The declared set of live first-break conditions must be
prerequisite-closed. A downstream condition cannot be live for confirmatory
classification when its structural predecessor is declared NOT-LIVE.
-/
def LivenessPrerequisiteClosed (g : StateVector) : Prop :=
  (LiveAtSeat g.pl -> LiveAtSeat g.p0)
  ∧ (LiveAtSeat g.boundary -> LiveAtSeat g.pl)
  ∧ (LiveAtSeat g.cascade -> LiveAtSeat g.boundary)
  ∧ (LiveAtSeat g.authorization -> LiveAtSeat g.cascade)

/-- Combined registration-consistency burden used by Layer-A public licenses. -/
def RegistrationConsistent (g : StateVector) : Prop :=
  PrerequisiteConsistent g ∧ LivenessPrerequisiteClosed g

theorem notLive_is_not_pass :
    ConditionStatus.notLive ≠ ConditionStatus.pass := by
  decide

theorem unresolved_is_not_pass :
    ConditionStatus.unresolved ≠ ConditionStatus.pass := by
  decide

theorem fail_is_not_pass :
    ConditionStatus.fail ≠ ConditionStatus.pass := by
  decide

theorem noBreakAtSeat_is_not_fail
    {s : ConditionStatus}
    (h : NoBreakAtSeat s) :
    s ≠ ConditionStatus.fail := by
  rcases h with hPass | hNotLive
  · rw [hPass]
    decide
  · rw [hNotLive]
    decide

/-! --------------------------------------------------------------------------
Prefix-sensitive first-break evidence
---------------------------------------------------------------------------- -/

/-- Break seat associated with one named class. -/
def breakCondition : FirstBreakClass -> Condition
  | .dissolution => .p0
  | .shear => .pl
  | .drift => .boundary
  | .echo => .cascade
  | .lock => .authorization

/--
A condition seat required to adjudicate one named first break.
This is prefix-sensitive: later conditions are not required after an earlier
first break has already been established.
-/
def RequiredForClass : FirstBreakClass -> Condition -> Prop
  | .dissolution, .p0 => True
  | .shear, .p0 => True
  | .shear, .pl => True
  | .drift, .p0 => True
  | .drift, .pl => True
  | .drift, .boundary => True
  | .echo, .p0 => True
  | .echo, .pl => True
  | .echo, .boundary => True
  | .echo, .cascade => True
  | .lock, .p0 => True
  | .lock, .pl => True
  | .lock, .boundary => True
  | .lock, .cascade => True
  | .lock, .authorization => True
  | _, _ => False

/-- Strict predecessor relation for one proposed first-break class. -/
def PredecessorForClass : Condition -> FirstBreakClass -> Prop
  | .p0, .shear => True
  | .p0, .drift => True
  | .pl, .drift => True
  | .p0, .echo => True
  | .pl, .echo => True
  | .boundary, .echo => True
  | .p0, .lock => True
  | .pl, .lock => True
  | .boundary, .lock => True
  | .cascade, .lock => True
  | _, _ => False

/--
Anchor-faithful evidence for a named first break.
Later condition seats are intentionally absent from earlier classes.
-/
def FirstBreakEvidence
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId) :
    FirstBreakClass -> Prop
  | .dissolution =>
      r.produced ∧ r.g.p0 = .fail
  | .shear =>
      r.produced
      ∧ r.g.p0 = .pass
      ∧ r.g.pl = .fail
  | .drift =>
      r.produced
      ∧ r.g.p0 = .pass
      ∧ r.g.pl = .pass
      ∧ r.g.boundary = .fail
  | .echo =>
      r.produced
      ∧ r.g.p0 = .pass
      ∧ r.g.pl = .pass
      ∧ r.g.boundary = .pass
      ∧ r.g.cascade = .fail
  | .lock =>
      r.produced
      ∧ r.g.p0 = .pass
      ∧ r.g.pl = .pass
      ∧ r.g.boundary = .pass
      ∧ r.g.cascade = .pass
      ∧ r.g.authorization = .fail

theorem first_break_condition_is_fail
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (k : FirstBreakClass)
    (h : FirstBreakEvidence r k) :
    statusAt r.g (breakCondition k) = .fail := by
  cases k with
  | dissolution => exact h.2
  | shear => exact h.2.2
  | drift => exact h.2.2.2
  | echo => exact h.2.2.2.2
  | lock => exact h.2.2.2.2.2

theorem predecessor_for_class_is_pass
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (q : Condition)
    (k : FirstBreakClass)
    (hPred : PredecessorForClass q k)
    (h : FirstBreakEvidence r k) :
    statusAt r.g q = .pass := by
  cases k <;> cases q <;>
    simp [PredecessorForClass, FirstBreakEvidence, statusAt] at hPred h ⊢ <;>
    simp_all

/--
A confirmatory named first-break assignment requires a clean entry surface,
J_ROUTE = FAIL, prerequisite consistency, and the corresponding prefix-sensitive
first-break evidence.

No total classifier over every syntactically possible four-state vector is
introduced here. Malformed or unlicensed records are not forced into the nearest
scientific disposition.
-/
def LicensedFirstBreak
    {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId)
    (k : FirstBreakClass) : Prop :=
  EntryReady c
  ∧ c.record.jRoute = .fail
  ∧ RegistrationConsistent c.record.g
  ∧ FirstBreakEvidence c.record k

/-- Primary-scale confirmatory ownership is an additional burden. -/
def PrimaryConfirmatoryFirstBreak
    {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId)
    (k : FirstBreakClass) : Prop :=
  LicensedFirstBreak c k
  ∧ c.record.scaleRole = .primary

/-- Domain-level PASS control: J_ROUTE succeeds and no physically live condition breaks. -/
def RoutePassControl
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId) : Prop :=
  r.jRoute = .pass
  ∧ RegistrationConsistent r.g
  ∧ NoLiveFoundationalBreak r.g

/-- Confirmatory PASS control requires the same clean entry surface. -/
def LicensedRoutePassControl
    {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId) : Prop :=
  EntryReady c ∧ RoutePassControl c.record

/--
Route-failure / no-known-break surface.
This is intentionally NOT called an SRW. Layer B/C ordinary-model, mixture,
measurement, replication, and completeness gates are not yet represented here.
-/
def RouteFailureWithoutKnownBreak
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId) : Prop :=
  r.jRoute = .fail
  ∧ RegistrationConsistent r.g
  ∧ NoLiveFoundationalBreak r.g

/-! --------------------------------------------------------------------------
Adversarial blockers
---------------------------------------------------------------------------- -/

theorem jRoute_pass_blocks_named_first_break_license
    {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId)
    (hPass : c.record.jRoute = .pass)
    (k : FirstBreakClass) :
    ¬ LicensedFirstBreak c k := by
  intro hLicensed
  have hFail : c.record.jRoute = .fail := hLicensed.2.1
  rw [hPass] at hFail
  contradiction

theorem jRoute_unresolved_blocks_named_first_break_license
    {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId)
    (hOpen : c.record.jRoute = .unresolved)
    (k : FirstBreakClass) :
    ¬ LicensedFirstBreak c k := by
  intro hLicensed
  have hFail : c.record.jRoute = .fail := hLicensed.2.1
  rw [hOpen] at hFail
  contradiction

theorem prerequisite_inconsistency_blocks_named_first_break_license
    {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId)
    (hInconsistent : ¬ PrerequisiteConsistent c.record.g)
    (k : FirstBreakClass) :
    ¬ LicensedFirstBreak c k := by
  intro hLicensed
  exact hInconsistent hLicensed.2.2.1.1

theorem liveness_inconsistency_blocks_named_first_break_license
    {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId)
    (hInconsistent : ¬ LivenessPrerequisiteClosed c.record.g)
    (k : FirstBreakClass) :
    ¬ LicensedFirstBreak c k := by
  intro hLicensed
  exact hInconsistent hLicensed.2.2.1.2

theorem secondary_scale_blocks_primary_confirmatory_assignment
    {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId)
    (k : FirstBreakClass)
    (hSecondary : c.record.scaleRole = .secondary) :
    ¬ PrimaryConfirmatoryFirstBreak c k := by
  intro hPrimary
  have hRole : c.record.scaleRole = .primary := hPrimary.2
  rw [hSecondary] at hRole
  contradiction

theorem required_unresolved_blocks_class
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (k : FirstBreakClass)
    (q : Condition)
    (hRequired : RequiredForClass k q)
    (hUnresolved : statusAt r.g q = .unresolved) :
    ¬ FirstBreakEvidence r k := by
  cases k <;> cases q <;>
    simp [RequiredForClass, FirstBreakEvidence, statusAt] at hRequired hUnresolved ⊢ <;>
    simp_all

theorem required_notLive_blocks_class
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (k : FirstBreakClass)
    (q : Condition)
    (hRequired : RequiredForClass k q)
    (hNotLive : statusAt r.g q = .notLive) :
    ¬ FirstBreakEvidence r k := by
  cases k <;> cases q <;>
    simp [RequiredForClass, FirstBreakEvidence, statusAt] at hRequired hNotLive ⊢ <;>
    simp_all

theorem predecessor_failure_blocks_later_class
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (q : Condition)
    (k : FirstBreakClass)
    (hPred : PredecessorForClass q k)
    (hFail : statusAt r.g q = .fail) :
    ¬ FirstBreakEvidence r k := by
  cases k <;> cases q <;>
    simp [PredecessorForClass, FirstBreakEvidence, statusAt] at hPred hFail ⊢ <;>
    simp_all

theorem no_live_break_blocks_any_named_first_break
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (hNoBreak : NoLiveFoundationalBreak r.g)
    (k : FirstBreakClass) :
    ¬ FirstBreakEvidence r k := by
  rcases hNoBreak with ⟨hP0, hPl, hB, hC, hA⟩
  cases k with
  | dissolution =>
      intro h
      exact (noBreakAtSeat_is_not_fail hP0) h.2
  | shear =>
      intro h
      exact (noBreakAtSeat_is_not_fail hPl) h.2.2
  | drift =>
      intro h
      exact (noBreakAtSeat_is_not_fail hB) h.2.2.2
  | echo =>
      intro h
      exact (noBreakAtSeat_is_not_fail hC) h.2.2.2.2
  | lock =>
      intro h
      exact (noBreakAtSeat_is_not_fail hA) h.2.2.2.2.2

theorem route_pass_control_is_not_a_named_failure_regime
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (hPass : RoutePassControl r)
    (k : FirstBreakClass) :
    ¬ FirstBreakEvidence r k := by
  exact no_live_break_blocks_any_named_first_break r hPass.2.2 k

/-! --------------------------------------------------------------------------
Compatibility bridge to the existing FailureClosure kernel
---------------------------------------------------------------------------- -/

/--
Compatibility between one experiment-owned condition status and one kernel
capacity proposition.

PASS constrains the proposition to hold.
FAIL constrains the proposition not to hold.
NOT-LIVE and UNRESOLVED deliberately impose no truth-value constraint.
-/
def ConditionCompatible (st : ConditionStatus) (p : Prop) : Prop :=
  match st with
  | .pass => p
  | .fail => ¬ p
  | .notLive => True
  | .unresolved => True

/--
A kernel snapshot is compatible with the scientifically adjudicated content of
one route record. This is a relation, not a coercion.
-/
structure KernelCompatible
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (s : FailureClosure.RouteSnapshot) : Prop where
  produced_iff : s.produced ↔ r.produced
  p0 : ConditionCompatible r.g.p0 s.persistenceEstablished
  pl : ConditionCompatible r.g.pl s.persistenceCarriesUnderLoad
  boundary : ConditionCompatible r.g.boundary s.boundaryDiscriminates
  cascade : ConditionCompatible r.g.cascade s.cascadeInherits
  authorization : ConditionCompatible r.g.authorization s.authorizationIncorporates

theorem compatible_pass
    {st : ConditionStatus}
    {p : Prop}
    (hCompat : ConditionCompatible st p)
    (hPass : st = .pass) :
    p := by
  subst st
  simpa [ConditionCompatible] using hCompat

theorem compatible_fail
    {st : ConditionStatus}
    {p : Prop}
    (hCompat : ConditionCompatible st p)
    (hFail : st = .fail) :
    ¬ p := by
  subst st
  simpa [ConditionCompatible] using hCompat

/--
A live/resolved scientific state is compatible with its own Boolean PASS
projection. This helper avoids asking simplification to reconstruct dependent
field equalities inside `resolvedKernelProjection`.
-/
theorem liveResolved_compatible_own_pass
    (st : ConditionStatus)
    (hLive : LiveResolved st) :
    ConditionCompatible st (st = .pass) := by
  rcases hLive with hPass | hFail
  · subst st
    simp [ConditionCompatible]
  · subst st
    simp [ConditionCompatible]

/-- Kernel regime predicate selected by one experiment-owned named class. -/
def KernelRegime
    (k : FirstBreakClass)
    (s : FailureClosure.RouteSnapshot) : Prop :=
  match k with
  | .dissolution => FailureClosure.Dissolution s
  | .shear => FailureClosure.Shear s
  | .drift => FailureClosure.Drift s
  | .echo => FailureClosure.Echo s
  | .lock => FailureClosure.Lock s

/--
Core Layer-A bridge.
Any kernel snapshot compatible with the scientifically adjudicated prefix of a
named first break occupies the corresponding existing kernel regime predicate.
No truth value is manufactured for NOT-LIVE or UNRESOLVED later seats.
-/
theorem first_break_evidence_maps_to_existing_kernel_regime
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (k : FirstBreakClass)
    (s : FailureClosure.RouteSnapshot)
    (hClass : FirstBreakEvidence r k)
    (hCompat : KernelCompatible r s) :
    KernelRegime k s := by
  cases k with
  | dissolution =>
      rcases hClass with ⟨hProducedR, hP0Fail⟩
      have hProducedS : s.produced := (hCompat.produced_iff).2 hProducedR
      exact ⟨hProducedS, compatible_fail hCompat.p0 hP0Fail⟩
  | shear =>
      rcases hClass with ⟨hProducedR, hP0Pass, hPlFail⟩
      have hProducedS : s.produced := (hCompat.produced_iff).2 hProducedR
      exact
        ⟨hProducedS,
         compatible_pass hCompat.p0 hP0Pass,
         compatible_fail hCompat.pl hPlFail⟩
  | drift =>
      rcases hClass with ⟨hProducedR, _hP0Pass, hPlPass, hBFail⟩
      have hProducedS : s.produced := (hCompat.produced_iff).2 hProducedR
      exact
        ⟨hProducedS,
         compatible_pass hCompat.pl hPlPass,
         compatible_fail hCompat.boundary hBFail⟩
  | echo =>
      rcases hClass with ⟨hProducedR, _hP0Pass, _hPlPass, hBPass, hCFail⟩
      have hProducedS : s.produced := (hCompat.produced_iff).2 hProducedR
      exact
        ⟨hProducedS,
         compatible_pass hCompat.boundary hBPass,
         compatible_fail hCompat.cascade hCFail⟩
  | lock =>
      rcases hClass with ⟨hProducedR, _hP0Pass, _hPlPass, _hBPass, hCPass, hAFail⟩
      have hProducedS : s.produced := (hCompat.produced_iff).2 hProducedR
      exact
        ⟨hProducedS,
         compatible_pass hCompat.cascade hCPass,
         compatible_fail hCompat.authorization hAFail⟩

/-- Licensed scientific classification inherits the same kernel mapping. -/
theorem licensed_first_break_maps_to_existing_kernel_regime
    {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId)
    (k : FirstBreakClass)
    (s : FailureClosure.RouteSnapshot)
    (hLicensed : LicensedFirstBreak c k)
    (hCompat : KernelCompatible c.record s) :
    KernelRegime k s := by
  exact
    first_break_evidence_maps_to_existing_kernel_regime
      c.record k s hLicensed.2.2.2 hCompat

/-! --------------------------------------------------------------------------
Fully-live / resolved projection for d(pi)
---------------------------------------------------------------------------- -/

/--
Boolean kernel projection used only where the scientific state is separately
proved fully live and resolved.

Outside that burden this definition must not be read as mapping NOT-LIVE or
UNRESOLVED to scientific FAIL. The named-class bridge above is the lawful
partial-state interface.
-/
def resolvedKernelProjection
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId) :
    FailureClosure.RouteSnapshot where
  produced := r.produced
  persistenceEstablished := r.g.p0 = .pass
  persistenceCarriesUnderLoad := r.g.pl = .pass
  boundaryDiscriminates := r.g.boundary = .pass
  cascadeInherits := r.g.cascade = .pass
  authorizationIncorporates := r.g.authorization = .pass

/-- A fully-live / resolved projection preserves all adjudicated PASS / FAIL states. -/
theorem resolved_projection_is_compatible
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (hLive : FullyLiveResolved r.g) :
    KernelCompatible r (resolvedKernelProjection r) := by
  rcases hLive with ⟨hP0, hPl, hB, hC, hA⟩
  constructor
  · rfl
  · exact liveResolved_compatible_own_pass r.g.p0 hP0
  · exact liveResolved_compatible_own_pass r.g.pl hPl
  · exact liveResolved_compatible_own_pass r.g.boundary hB
  · exact liveResolved_compatible_own_pass r.g.cascade hC
  · exact liveResolved_compatible_own_pass r.g.authorization hA

/-- Anchor prerequisite consistency yields the kernel's WellFormedRoute burden. -/
theorem resolved_projection_well_formed
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (hConsistent : PrerequisiteConsistent r.g) :
    FailureClosure.WellFormedRoute (resolvedKernelProjection r) := by
  rcases hConsistent with ⟨hPlP0, hBP1, hCB, hAC⟩
  constructor
  · intro hPl
    exact hPlP0 hPl
  · intro hB
    exact hBP1 hB
  · intro hC
    exact hCB hC
  · intro hA
    exact hAC hA

/-- Derived depth associated with each named first-break class. -/
def classDepth : FirstBreakClass -> Nat
  | .dissolution => 0
  | .shear => 1
  | .drift => 2
  | .echo => 3
  | .lock => 4

/--
For a fully-live / resolved, prerequisite-consistent experimental route, the
anchor's prefix-sensitive class maps to the existing kernel first-break depth.
-/
theorem fully_live_first_break_maps_to_kernel_depth
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (k : FirstBreakClass)
    (hLive : FullyLiveResolved r.g)
    (hConsistent : PrerequisiteConsistent r.g)
    (hClass : FirstBreakEvidence r k) :
    FailureClosure.firstBreakDepth (resolvedKernelProjection r) = classDepth k := by
  have hCompat := resolved_projection_is_compatible r hLive
  have hRegime :=
    first_break_evidence_maps_to_existing_kernel_regime
      r k (resolvedKernelProjection r) hClass hCompat
  have hWf := resolved_projection_well_formed r hConsistent
  cases k with
  | dissolution =>
      exact FailureClosure.dissolution_depth (resolvedKernelProjection r) hRegime
  | shear =>
      exact FailureClosure.shear_depth (resolvedKernelProjection r) hRegime
  | drift =>
      exact FailureClosure.drift_depth (resolvedKernelProjection r) hWf hRegime
  | echo =>
      exact FailureClosure.echo_depth (resolvedKernelProjection r) hWf hRegime
  | lock =>
      exact FailureClosure.lock_depth (resolvedKernelProjection r) hWf hRegime

/-- All-five PASS is the exact fully-live / resolved no-break case mapped to depth 5. -/
def AllFivePass (g : StateVector) : Prop :=
  g.p0 = .pass
  ∧ g.pl = .pass
  ∧ g.boundary = .pass
  ∧ g.cascade = .pass
  ∧ g.authorization = .pass

theorem all_five_pass_maps_to_kernel_depth_five
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (hAll : AllFivePass r.g) :
    FailureClosure.firstBreakDepth (resolvedKernelProjection r) = 5 := by
  apply (FailureClosure.depth_five_iff (resolvedKernelProjection r)).2
  simpa [AllFivePass, resolvedKernelProjection] using hAll

/-- Any NOT-LIVE seat blocks use of the all-five fully-live depth interface. -/
theorem notLive_blocks_fully_live_resolved
    (g : StateVector)
    (q : Condition)
    (hNotLive : statusAt g q = .notLive) :
    ¬ FullyLiveResolved g := by
  intro hLive
  rcases hLive with ⟨hP0, hPl, hB, hC, hA⟩
  cases q with
  | p0 =>
      have hNL : g.p0 = .notLive := by simpa [statusAt] using hNotLive
      rcases hP0 with hPass | hFail
      · rw [hNL] at hPass
        contradiction
      · rw [hNL] at hFail
        contradiction
  | pl =>
      have hNL : g.pl = .notLive := by simpa [statusAt] using hNotLive
      rcases hPl with hPass | hFail
      · rw [hNL] at hPass
        contradiction
      · rw [hNL] at hFail
        contradiction
  | boundary =>
      have hNL : g.boundary = .notLive := by simpa [statusAt] using hNotLive
      rcases hB with hPass | hFail
      · rw [hNL] at hPass
        contradiction
      · rw [hNL] at hFail
        contradiction
  | cascade =>
      have hNL : g.cascade = .notLive := by simpa [statusAt] using hNotLive
      rcases hC with hPass | hFail
      · rw [hNL] at hPass
        contradiction
      · rw [hNL] at hFail
        contradiction
  | authorization =>
      have hNL : g.authorization = .notLive := by simpa [statusAt] using hNotLive
      rcases hA with hPass | hFail
      · rw [hNL] at hPass
        contradiction
      · rw [hNL] at hFail
        contradiction

/-- Any UNRESOLVED seat blocks use of the all-five fully-live depth interface. -/
theorem unresolved_blocks_fully_live_resolved
    (g : StateVector)
    (q : Condition)
    (hOpen : statusAt g q = .unresolved) :
    ¬ FullyLiveResolved g := by
  intro hLive
  rcases hLive with ⟨hP0, hPl, hB, hC, hA⟩
  cases q with
  | p0 =>
      have hU : g.p0 = .unresolved := by simpa [statusAt] using hOpen
      rcases hP0 with hPass | hFail
      · rw [hU] at hPass
        contradiction
      · rw [hU] at hFail
        contradiction
  | pl =>
      have hU : g.pl = .unresolved := by simpa [statusAt] using hOpen
      rcases hPl with hPass | hFail
      · rw [hU] at hPass
        contradiction
      · rw [hU] at hFail
        contradiction
  | boundary =>
      have hU : g.boundary = .unresolved := by simpa [statusAt] using hOpen
      rcases hB with hPass | hFail
      · rw [hU] at hPass
        contradiction
      · rw [hU] at hFail
        contradiction
  | cascade =>
      have hU : g.cascade = .unresolved := by simpa [statusAt] using hOpen
      rcases hC with hPass | hFail
      · rw [hU] at hPass
        contradiction
      · rw [hU] at hFail
        contradiction
  | authorization =>
      have hU : g.authorization = .unresolved := by simpa [statusAt] using hOpen
      rcases hA with hPass | hFail
      · rw [hU] at hPass
        contradiction
      · rw [hU] at hFail
        contradiction

/-- A NOT-LIVE predecessor cannot support a live immediate downstream seat under A-02. -/
theorem notLive_predecessor_blocks_live_successor
    (g : StateVector)
    (hLiveClosed : LivenessPrerequisiteClosed g) :
    (g.p0 = .notLive -> g.pl = .notLive)
    ∧ (g.pl = .notLive -> g.boundary = .notLive)
    ∧ (g.boundary = .notLive -> g.cascade = .notLive)
    ∧ (g.cascade = .notLive -> g.authorization = .notLive) := by
  rcases hLiveClosed with ⟨hPlP0, hBPl, hCB, hAC⟩
  constructor
  · intro hP0
    by_cases hPl : g.pl = .notLive
    · exact hPl
    · exact False.elim (hPlP0 hPl hP0)
  constructor
  · intro hPl
    by_cases hB : g.boundary = .notLive
    · exact hB
    · exact False.elim (hBPl hB hPl)
  constructor
  · intro hB
    by_cases hC : g.cascade = .notLive
    · exact hC
    · exact False.elim (hCB hC hB)
  · intro hC
    by_cases hA : g.authorization = .notLive
    · exact hA
    · exact False.elim (hAC hA hC)

/-! --------------------------------------------------------------------------
Route / object / scale firewalls
---------------------------------------------------------------------------- -/

/--
A route-level certificate carries the RouteId and class only.
The owning ObjectId remains metadata in the contract record and is not promoted
to an object-level failure-class conclusion by this constructor.
-/
structure FirstBreakCertificate
    {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId) where
  firstBreakClass : FirstBreakClass
  licensed : LicensedFirstBreak c firstBreakClass

/-- Primary confirmatory certificate. -/
structure PrimaryFirstBreakCertificate
    {ObjectId RouteId ScaleId : Type}
    (c : Contract ObjectId RouteId ScaleId) where
  firstBreakClass : FirstBreakClass
  licensed : PrimaryConfirmatoryFirstBreak c firstBreakClass

/-! --------------------------------------------------------------------------
Layer-A public checkpoint
---------------------------------------------------------------------------- -/

/--
Layer A establishes the intended interface shape:
* four-state scientific condition records remain four-state;
* licensed named first breaks require J_ROUTE failure, clean entry, and registration consistency;
* NOT-LIVE / UNRESOLVED are not coerced into kernel booleans;
* prefix-sensitive class evidence maps into existing kernel regimes;
* derived kernel depth is used only for fully-live / resolved routes;
* all-five PASS maps to depth 5;
* domain PASS with NOT-LIVE remains outside that all-five depth interface;
* liveness declarations are prerequisite-closed under pressure repair A-02;
* route and primary-scale certificates remain typed separately from ObjectId.
-/
theorem layer_a_checkpoint :
    ConditionStatus.notLive ≠ ConditionStatus.pass
    ∧ ConditionStatus.unresolved ≠ ConditionStatus.pass := by
  exact ⟨notLive_is_not_pass, unresolved_is_not_pass⟩

end DarkMatterFailureRegimeLayerA
end StructuralFlow


/-!
===============================================================================
DARK-MATTER FAILURE-REGIME ADAPTER / CONTRACT — INTERNAL LAYER B
===============================================================================

INTERNAL ROLE
-------------
Layer B is the branch-adjudication partition of the cumulative adapter. Its
semantics are governed by the accepted scientific anchor named in the release
header. Machine-proof repairs in this partition do not create scientific states.

ROLE
----
Layer B formalizes the branch-level one-way adjudication chain after Layer A:

  search adequacy
  -> declared-class physicalization
  -> source bridge
  -> ordinary-gravity / light bridge
  -> measurement recovery
  -> O2 comparison / U1 disposition.

Layer B does NOT formalize the novelty-to-SRW-to-FR6 reopening path. That is
reserved for Layer C. In particular, a route failure with no known first break
is not silently promoted here to SRW or foundational pressure.

SCIENTIFIC NON-CLAIMS
---------------------
A Lean proof in this append does not establish:
* that any branch exists in nature;
* that a physical target is adequate;
* that any source, light, or measurement prediction is physically correct;
* that O2 is scientifically strong enough merely because its freeze burden is
  encoded as discharged;
* that U1 has been empirically earned in any execution;
* that a lower-layer branch failure weakens or reopens five-regime closure;
* that a route-level residual is an SRW;
* that closure survived merely because a branch prediction or U1 result survived.
===============================================================================
-/

open StructuralFlow.UniversalTranslationContract

namespace StructuralFlow
namespace DarkMatterFailureRegimeLayerB

open DarkMatterFailureRegimeLayerA

/-! --------------------------------------------------------------------------
Layer-B branch setup and result vocabulary
---------------------------------------------------------------------------- -/

/--
Pre-target branch burdens added after the Layer-A route/classification freeze.
These are machine-state declarations, not empirical truth supplied by Lean.
-/
inductive BranchBurden where
  | matchedControlFrozen
  | sourcePredictionFrozen
  | lightPredictionFrozen
  | measurementPipelineFrozen
  | ordinaryComparatorFrozen
  | utilityCriterionFrozen
  | targetHoldoutIntact
  | branchFreezeVerified
  deriving DecidableEq, Repr

/-- Outcome of the frozen O2 comparison after the branch survives measurement. -/
inductive ComparatorOutcome where
  | sfWins
  | o2Wins
  | tie
  | unresolved
  deriving DecidableEq, Repr

/--
Layer-B primary terminal states.

`u1Earned` is the explicit positive terminal required by the governing anchor's
rule that an SF-organized prediction earns U1 only when it beats O2 on the frozen
primary utility criterion.

Novelty / SRW / FR6 states are intentionally absent here and belong to Layer C.
-/
inductive PrimaryResult where
  | searchFailure
  | physicalizationFailure
  | sourceBridgeFailure
  | lightBridgeFailure
  | measurementFailure
  | u1Fail
  | u1NotEarned
  | u1Earned
  | unresolved
  deriving DecidableEq, Repr

/-- Foundational-closure consequence available to Layer-B terminal states. -/
inductive ClosureEffect where
  | unchanged
  | untestedByBranch
  | noResult
  deriving DecidableEq, Repr

/--
One branch-level adjudication packet.

The Layer-A contract remains the authority surface for route admission and
first-break classification. Layer B adds only branch identity, the declared
class the branch was built to instantiate, pre-target branch burdens, and the
post-target downstream stage outcomes.
-/
structure BranchContract
    (ObjectId RouteId ScaleId BranchId : Type) where
  branchId : BranchId
  routeContract : DarkMatterFailureRegimeLayerA.Contract ObjectId RouteId ScaleId
  declaredClass : FirstBreakClass
  branchState : BranchBurden -> Disposition
  searchState : Disposition
  sourceBridgeState : Disposition
  lightBridgeState : Disposition
  measurementState : Disposition
  comparatorOutcome : ComparatorOutcome

/-- Every branch-specific pre-target burden is discharged. -/
def BranchSetupReady
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  ∀ q, b.branchState q = .discharged

/-- Search adequacy is a separate experimental gate from route classification. -/
def SearchAdequate
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  b.searchState = .discharged

/-- The registered search / target burden failed to place the branch under pressure. -/
def SearchFailed
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  b.searchState = .violated

/-- Search adequacy itself remains unresolved. -/
def SearchOpen
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  b.searchState = .open

/-! --------------------------------------------------------------------------
Physicalization interface back into Layer A
---------------------------------------------------------------------------- -/


/-- Clean Layer-A surface required before branch physicalization is scientifically adjudicable. -/
def PhysicalizationAdjudicationReady
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  EntryReady b.routeContract
  ∧ b.routeContract.record.scaleRole = .primary
  ∧ RegistrationConsistent b.routeContract.record.g

/-- The route cleanly instantiates the class for which the branch was registered. -/
def DeclaredPhysicalizationConfirmed
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  PrimaryConfirmatoryFirstBreak b.routeContract b.declaredClass

/--
A resolved known mismatch is positive evidence that the branch's declared class
was not instantiated. It is either a primary PASS control or a different known
primary first break. An unresolved route is not converted into a mismatch.
-/
def KnownPhysicalizationMismatch
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  PhysicalizationAdjudicationReady b
  ∧ (
      (¬ b.routeContract.record.produced)
      ∨ RoutePassControl b.routeContract.record
      ∨ (∃ k : FirstBreakClass,
          k ≠ b.declaredClass
          ∧ PrimaryConfirmatoryFirstBreak b.routeContract k)
    )

/--
A route whose intrinsic adjudication is still open cannot be reported as a
physicalization failure merely because the declared class was not confirmed.

The predicate deliberately names only scientifically unresolved route states.
Malformed registration or violated entry burdens are not converted into a
scientific `UNRESOLVED` result; they remain invalid inputs upstream.
-/
def IntrinsicClassificationOpen
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  PhysicalizationAdjudicationReady b
  ∧ b.routeContract.record.produced
  ∧ (
      b.routeContract.record.jRoute = .unresolved
      ∨ (b.routeContract.record.jRoute = .fail
          ∧ ¬ (∃ k : FirstBreakClass,
              LicensedFirstBreak b.routeContract k)
          ∧ ¬ RouteFailureWithoutKnownBreak b.routeContract.record)
    )

/--
Layer-B handoff surface for a route failure that the known first-break map does
not classify. This is NOT an SRW. Layer C must still discharge the ordinary
model, mixture, measurement, replication, and completeness gates.
-/
def RouteUnknownHandoff
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  BranchSetupReady b
  ∧ SearchAdequate b
  ∧ PhysicalizationAdjudicationReady b
  ∧ b.routeContract.record.produced
  ∧ RouteFailureWithoutKnownBreak b.routeContract.record

/-! --------------------------------------------------------------------------
Sequential branch result licenses
---------------------------------------------------------------------------- -/

/-- Search failure is terminal before any branch-specific physical claim is placed under pressure. -/
def SearchFailureResult
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  BranchSetupReady b ∧ SearchFailed b

/-- Resolved mismatch of the declared class after an adequate search. -/
def PhysicalizationFailureResult
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  BranchSetupReady b
  ∧ SearchAdequate b
  ∧ KnownPhysicalizationMismatch b

/-- The declared class is clean, but its frozen source consequence fails. -/
def SourceBridgeFailureResult
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  BranchSetupReady b
  ∧ SearchAdequate b
  ∧ DeclaredPhysicalizationConfirmed b
  ∧ b.sourceBridgeState = .violated

/-- The source consequence survives, but ordinary-gravity / probe translation fails. -/
def LightBridgeFailureResult
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  BranchSetupReady b
  ∧ SearchAdequate b
  ∧ DeclaredPhysicalizationConfirmed b
  ∧ b.sourceBridgeState = .discharged
  ∧ b.lightBridgeState = .violated

/-- Truth-level light consequence survives, but the registered recovery pipeline fails. -/
def MeasurementFailureResult
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  BranchSetupReady b
  ∧ SearchAdequate b
  ∧ DeclaredPhysicalizationConfirmed b
  ∧ b.sourceBridgeState = .discharged
  ∧ b.lightBridgeState = .discharged
  ∧ b.measurementState = .violated

/-- O2 outperforms the SF-organized prediction after the physical branch survives measurement. -/
def U1FailResult
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  BranchSetupReady b
  ∧ SearchAdequate b
  ∧ DeclaredPhysicalizationConfirmed b
  ∧ b.sourceBridgeState = .discharged
  ∧ b.lightBridgeState = .discharged
  ∧ b.measurementState = .discharged
  ∧ b.comparatorOutcome = .o2Wins

/-- O2 ties the SF-organized prediction; derivational convergence may remain, U1 does not. -/
def U1NotEarnedResult
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  BranchSetupReady b
  ∧ SearchAdequate b
  ∧ DeclaredPhysicalizationConfirmed b
  ∧ b.sourceBridgeState = .discharged
  ∧ b.lightBridgeState = .discharged
  ∧ b.measurementState = .discharged
  ∧ b.comparatorOutcome = .tie

/--
Positive Layer-B terminal: the registered branch survives through measurement
and the SF-organized prediction beats O2 on the frozen primary utility criterion.
This earns U1 only for the declared branch / metric. It does not establish
foundational closure survival.
-/
def U1EarnedResult
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  BranchSetupReady b
  ∧ SearchAdequate b
  ∧ DeclaredPhysicalizationConfirmed b
  ∧ b.sourceBridgeState = .discharged
  ∧ b.lightBridgeState = .discharged
  ∧ b.measurementState = .discharged
  ∧ b.comparatorOutcome = .sfWins

/--
Scientific UNRESOLVED is permitted only at the earliest live branch gate whose
predecessors have survived. This avoids using UNRESOLVED as a generic escape for
an already-failed earlier stage.
-/
def UnresolvedResult
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : Prop :=
  BranchSetupReady b
  ∧ (
      SearchOpen b
      ∨ (SearchAdequate b ∧ IntrinsicClassificationOpen b)
      ∨ (SearchAdequate b
          ∧ DeclaredPhysicalizationConfirmed b
          ∧ b.sourceBridgeState = .open)
      ∨ (SearchAdequate b
          ∧ DeclaredPhysicalizationConfirmed b
          ∧ b.sourceBridgeState = .discharged
          ∧ b.lightBridgeState = .open)
      ∨ (SearchAdequate b
          ∧ DeclaredPhysicalizationConfirmed b
          ∧ b.sourceBridgeState = .discharged
          ∧ b.lightBridgeState = .discharged
          ∧ b.measurementState = .open)
      ∨ (SearchAdequate b
          ∧ DeclaredPhysicalizationConfirmed b
          ∧ b.sourceBridgeState = .discharged
          ∧ b.lightBridgeState = .discharged
          ∧ b.measurementState = .discharged
          ∧ b.comparatorOutcome = .unresolved)
    )

/-- Public result-evidence router for Layer B. -/
def ResultEvidence
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) : PrimaryResult -> Prop
  | .searchFailure => SearchFailureResult b
  | .physicalizationFailure => PhysicalizationFailureResult b
  | .sourceBridgeFailure => SourceBridgeFailureResult b
  | .lightBridgeFailure => LightBridgeFailureResult b
  | .measurementFailure => MeasurementFailureResult b
  | .u1Fail => U1FailResult b
  | .u1NotEarned => U1NotEarnedResult b
  | .u1Earned => U1EarnedResult b
  | .unresolved => UnresolvedResult b

/-! --------------------------------------------------------------------------
Closure firewalls
---------------------------------------------------------------------------- -/

/--
Layer-B result states do not themselves suspend or reopen foundational closure.
Search failure never tests it; unresolved returns no result; all other Layer-B
terminal states leave it unchanged.
-/
def closureEffect : PrimaryResult -> ClosureEffect
  | .searchFailure => .untestedByBranch
  | .unresolved => .noResult
  | .physicalizationFailure => .unchanged
  | .sourceBridgeFailure => .unchanged
  | .lightBridgeFailure => .unchanged
  | .measurementFailure => .unchanged
  | .u1Fail => .unchanged
  | .u1NotEarned => .unchanged
  | .u1Earned => .unchanged

theorem layer_b_never_suspends_or_reopens_closure
    (r : PrimaryResult) :
    closureEffect r = .unchanged
    ∨ closureEffect r = .untestedByBranch
    ∨ closureEffect r = .noResult := by
  cases r <;> simp [closureEffect]

/-! --------------------------------------------------------------------------
Sequential anti-collapse theorems
---------------------------------------------------------------------------- -/

/-- Two clean named first-break evidence records for one route identify the same class. -/
theorem first_break_evidence_unique
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (k1 k2 : FirstBreakClass)
    (h1 : FirstBreakEvidence r k1)
    (h2 : FirstBreakEvidence r k2) :
    k1 = k2 := by
  cases k1 <;> cases k2 <;>
    simp [FirstBreakEvidence] at h1 h2 ⊢ <;>
    simp_all

/-- Every named first-break evidence record includes occurrence of the relevant
interaction-produced difference E.  This helper keeps dependent class matching
local to the explicit class argument rather than projecting through a field. -/
theorem first_break_evidence_implies_produced
    {ObjectId RouteId ScaleId : Type}
    (r : RouteRecord ObjectId RouteId ScaleId)
    (k : FirstBreakClass)
    (h : FirstBreakEvidence r k) :
    r.produced := by
  cases k with
  | dissolution => exact h.1
  | shear => exact h.1
  | drift => exact h.1
  | echo => exact h.1
  | lock => exact h.1

/-- Any clean declared-class confirmation includes the interaction-produced difference E. -/
theorem declared_confirmation_implies_produced
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId)
    (h : DeclaredPhysicalizationConfirmed b) :
    b.routeContract.record.produced := by
  have hEvidence : FirstBreakEvidence b.routeContract.record b.declaredClass :=
    h.1.2.2.2
  exact first_break_evidence_implies_produced
    b.routeContract.record b.declaredClass hEvidence

/-- A source-bridge failure cannot simultaneously be the physicalization mismatch result. -/
theorem source_failure_excludes_known_physicalization_mismatch
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId)
    (hSource : SourceBridgeFailureResult b) :
    ¬ KnownPhysicalizationMismatch b := by
  intro hMismatch
  rcases hSource with ⟨_, _, hConfirmed, _⟩
  rcases hMismatch with ⟨_, hMismatchCore⟩
  rcases hMismatchCore with hNoE | hRest
  · exact hNoE (declared_confirmation_implies_produced b hConfirmed)
  · rcases hRest with hPass | hOther
    · have hJPass : b.routeContract.record.jRoute = .pass := hPass.1
      have hJFail : b.routeContract.record.jRoute = .fail := hConfirmed.1.2.1
      rw [hJPass] at hJFail
      contradiction
    · rcases hOther with ⟨k, hNe, hOtherClass⟩
      have hEq : b.declaredClass = k :=
        first_break_evidence_unique
          b.routeContract.record
          b.declaredClass
          k
          hConfirmed.1.2.2.2
          hOtherClass.1.2.2.2
      exact hNe hEq.symm

/-- A light-bridge failure can only be reached after the source bridge survived. -/
theorem light_failure_requires_source_survival
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId)
    (h : LightBridgeFailureResult b) :
    b.sourceBridgeState = .discharged := by
  exact h.2.2.2.1

/-- A measurement failure can only be reached after source and light survived. -/
theorem measurement_failure_requires_prior_survival
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId)
    (h : MeasurementFailureResult b) :
    b.sourceBridgeState = .discharged
    ∧ b.lightBridgeState = .discharged := by
  exact ⟨h.2.2.2.1, h.2.2.2.2.1⟩

/-- U1 failure can only be adjudicated after the physical prediction survives measurement. -/
theorem u1_fail_requires_measurement_survival
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId)
    (h : U1FailResult b) :
    b.measurementState = .discharged := by
  exact h.2.2.2.2.2.1

/-- U1 tie can only be adjudicated after the physical prediction survives measurement. -/
theorem u1_not_earned_requires_measurement_survival
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId)
    (h : U1NotEarnedResult b) :
    b.measurementState = .discharged := by
  exact h.2.2.2.2.2.1

/-- U1 earned can only be adjudicated after the physical prediction survives measurement. -/
theorem u1_earned_requires_measurement_survival
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId)
    (h : U1EarnedResult b) :
    b.measurementState = .discharged := by
  exact h.2.2.2.2.2.1

/-- O2 win, tie, and SF win are mutually exclusive terminal utility outcomes. -/
theorem u1_terminal_states_are_pairwise_distinct :
    ComparatorOutcome.o2Wins ≠ ComparatorOutcome.tie
    ∧ ComparatorOutcome.o2Wins ≠ ComparatorOutcome.sfWins
    ∧ ComparatorOutcome.tie ≠ ComparatorOutcome.sfWins := by
  decide

/-- Search failure cannot also satisfy the adequate-search precondition used downstream. -/
theorem search_failure_blocks_adequate_branch_results
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId)
    (hFail : SearchFailed b) :
    ¬ SearchAdequate b := by
  intro hAdequate
  unfold SearchFailed at hFail
  unfold SearchAdequate at hAdequate
  rw [hFail] at hAdequate
  contradiction

/-! --------------------------------------------------------------------------
Result certificate and public checkpoint
---------------------------------------------------------------------------- -/

structure ResultCertificate
    {ObjectId RouteId ScaleId BranchId : Type}
    (b : BranchContract ObjectId RouteId ScaleId BranchId) where
  primaryResult : PrimaryResult
  licensed : ResultEvidence b primaryResult

/--
Layer B closes the branch-adjudication ordering while preserving the foundational
firewall: lower-level loss stays local, utility comparison occurs only after
physical survival through measurement, and route-unknown cases are handed to
Layer C without being promoted to SRW.
-/
theorem layer_b_checkpoint :
    closureEffect .physicalizationFailure = .unchanged
    ∧ closureEffect .sourceBridgeFailure = .unchanged
    ∧ closureEffect .lightBridgeFailure = .unchanged
    ∧ closureEffect .measurementFailure = .unchanged
    ∧ closureEffect .u1Fail = .unchanged
    ∧ closureEffect .u1NotEarned = .unchanged
    ∧ closureEffect .u1Earned = .unchanged := by
  decide

end DarkMatterFailureRegimeLayerB
end StructuralFlow


/-!
===============================================================================
DARK-MATTER FAILURE-REGIME ADAPTER / CONTRACT — INTERNAL LAYER C
===============================================================================

INTERNAL ROLE
-------------
Layer C is the residual / foundational-reopening partition of the cumulative
adapter. Its semantics are governed by the accepted scientific anchor named in
the release header.

ROLE
----
Layer C formalizes the experiment's ordered residual / reopening pathway:

observable novelty
-> route-level SRW candidate
-> SRW replication
-> pre-frozen state-completeness exhaustion
-> maximal-state structural residual
-> CLOSURE SUSPENDED
-> positive FR6 candidate
-> full foundational newness audit
-> FR6 EARNED / closure reopened at the tested architecture and scale.

This layer does NOT add a sixth constructor to the Universal Kernel. The kernel's
five-regime theorem remains the theorem for the current foundational architecture.
An experimentally earned FR6 is represented here as a scoped reopening result that
requires upstream architectural re-adjudication; it is not smuggled into the
existing five-regime datatype.
===============================================================================
-/

open StructuralFlow.UniversalTranslationContract

namespace StructuralFlow
namespace DarkMatterFailureRegimeLayerC

open DarkMatterFailureRegimeLayerA
open DarkMatterFailureRegimeLayerB

/-! --------------------------------------------------------------------------
Layer-C freeze / audit burdens
---------------------------------------------------------------------------- -/

inductive ResidualBurden where
  | observableLibraryFrozen
  | noveltyThresholdFrozen
  | nonFoundationalRecheckRuleFrozen
  | srwReplicationRuleFrozen
  | stateCompletenessLadderFrozenPreTarget
  | candidateAuditRuleFrozen
  | interventionAvailabilityRuleFrozen
  | completeResultReplicationRuleFrozen
  | independentReproductionRuleFrozen
  deriving DecidableEq, Repr

inductive ResidualResult where
  | novelObservablePressure
  | srwCandidate
  | replicatedSRW
  | stateIncompletenessResolved
  | closureSuspended
  | fr6Candidate
  | knownCapacityReductionResolved
  | fr6Earned
  deriving DecidableEq, Repr

inductive FoundationalClosureStatus where
  | unchanged
  | suspended
  | restoredAtTestedScope
  | reopenedAtTestedScope
  deriving DecidableEq, Repr

/--
Layer-C residual / newness packet.  All empirical propositions are supplied by
an executor; Lean checks only the encoded conditional route among them.
-/
structure ResidualContract
    (ObjectId RouteId ScaleId BranchId : Type) where
  branch : BranchContract ObjectId RouteId ScaleId BranchId
  residualState : ResidualBurden -> Disposition

  /- Observable-library and ordinary-explanation gates. -/
  ruAboveThreshold : Prop
  nonFoundationalExplanationsCleared : Prop

  /- SRW and state-completeness gates. -/
  srwReplicationSucceeded : Prop
  stateCompletenessExhausted : Prop
  richerOrdinaryStateResolves : Prop
  maximalStateResidualPersists : Prop

  /- Positive candidate / foundational-newness content. -/
  candidateProposed : Prop
  /- Summary state of the candidate-newness adjudication: open / violated / discharged. -/
  candidateNewnessState : Disposition
  distinctPhysicalJob : Prop
  physicalCarrierIdentified : Prop
  passTestAvailable : Prop
  failTestAvailable : Prop
  predecessorRelationsPinned : Prop
  downstreamCapabilityDepends : Prop
  necessityEstablished : Prop

  /- Intervention is conditional on domain-owned physical availability. -/
  interventionAvailabilityAdjudicated : Prop
  interventionAvailable : Prop
  removalTestPassed : Prop
  restorationTestPassed : Prop

  /- Reduction / irreducibility / reproduction gates. -/
  reducesToKnownFive : Prop
  functionallyEquivalentToKnown : Prop
  /- Positive adjudication that a known-capacity reduction actually resolves the witness. -/
  knownCapacityReductionResolvesWitness : Prop
  uniqueRemovalOrIrreducible : Prop
  completeResultReplicated : Prop
  independentlyReproduced : Prop

/-- Every Layer-C protocol burden required before adjudication is discharged. -/
def ResidualEntryReady
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) : Prop :=
  forall b, c.residualState b = .discharged

/-- Observable-library novelty only.  This is not yet route-level novelty. -/
def NovelObservablePressure
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) : Prop :=
  ResidualEntryReady c ∧ c.ruAboveThreshold

/--
SRW entry requires the governing anchor condition: E is present, J_ROUTE fails, and
no physically live known first break remains.  Ordinary / measurement / mixture
explanations must also have been cleared.
-/
def SRWCandidate
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) : Prop :=
  NovelObservablePressure c
  ∧ c.nonFoundationalExplanationsCleared
  ∧ RouteUnknownHandoff c.branch

/-- Replication is a separate gate from initial SRW admission. -/
def ReplicatedSRW
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) : Prop :=
  SRWCandidate c ∧ c.srwReplicationSucceeded

/-- A richer pre-frozen ordinary state resolves the apparent structural residual. -/
def StateIncompletenessResolved
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) : Prop :=
  ReplicatedSRW c
  ∧ c.richerOrdinaryStateResolves

/--
Maximal-state residual: replicated SRW, full pre-frozen state ladder exhausted,
no richer admitted ordinary state resolves it, and the residual persists.
-/
def MaximalStateStructuralResidual
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) : Prop :=
  ReplicatedSRW c
  ∧ c.stateCompletenessExhausted
  ∧ ¬ c.richerOrdinaryStateResolves
  ∧ c.maximalStateResidualPersists

/-- Closure suspension is exactly the maximal-state residual state at R_PRIMARY. -/
def ClosureSuspended
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) : Prop :=
  MaximalStateStructuralResidual c

/--
FR6 candidate entry is downstream of maximal-state residual / closure
suspension, not merely downstream of one replicated SRW.
-/
def FR6Candidate
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) : Prop :=
  ClosureSuspended c ∧ c.candidateProposed

/--
A known-capacity reduction restores closure only when the domain-owned reduction
adjudication says that the reduction actually resolves the residual witness. Merely
reducing a candidate name or representation to known structure is not enough.
-/
def KnownCapacityReductionResolved
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) : Prop :=
  FR6Candidate c
  ∧ c.candidateNewnessState = .violated
  ∧ (c.reducesToKnownFive ∨ c.functionallyEquivalentToKnown)
  ∧ c.knownCapacityReductionResolvesWitness

/-- Conditional intervention burden preserves "where physically available" without
turning absence of intervention into an automatic, unrecorded waiver. -/
def InterventionBurdenSatisfied
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) : Prop :=
  c.interventionAvailabilityAdjudicated
  ∧ (c.interventionAvailable -> c.removalTestPassed ∧ c.restorationTestPassed)

/-- Full positive newness burden required after an FR6 candidate has been opened. -/
structure NewnessAuditComplete
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) : Prop where
  distinctJob : c.distinctPhysicalJob
  physicalCarrier : c.physicalCarrierIdentified
  passTest : c.passTestAvailable
  failTest : c.failTestAvailable
  predecessors : c.predecessorRelationsPinned
  downstreamDependence : c.downstreamCapabilityDepends
  necessity : c.necessityEstablished
  intervention : InterventionBurdenSatisfied c
  nonReduction : ¬ c.reducesToKnownFive
  nonEquivalence : ¬ c.functionallyEquivalentToKnown
  irreducibility : c.uniqueRemovalOrIrreducible
  completeReplication : c.completeResultReplicated
  independentReproduction : c.independentlyReproduced

/-- FR6 EARNED requires both the candidate state and the entire positive newness audit. -/
def FR6Earned
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) : Prop :=
  FR6Candidate c
  ∧ c.candidateNewnessState = .discharged
  ∧ NewnessAuditComplete c

/-! --------------------------------------------------------------------------
Result evidence and closure status
---------------------------------------------------------------------------- -/

def ResidualResultEvidence
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) : ResidualResult -> Prop
  | .novelObservablePressure => NovelObservablePressure c
  | .srwCandidate => SRWCandidate c
  | .replicatedSRW => ReplicatedSRW c
  | .stateIncompletenessResolved => StateIncompletenessResolved c
  | .closureSuspended => ClosureSuspended c
  | .fr6Candidate => FR6Candidate c
  | .knownCapacityReductionResolved => KnownCapacityReductionResolved c
  | .fr6Earned => FR6Earned c

/--
Diagnostic milestone certificate. This proves that a milestone has been reached; it
is NOT a final-report license because stronger residual states may also be active.
Use `ResidualReportingCertificate` for the primary scientific residual result.
-/
structure ResidualMilestoneCertificate
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) where
  milestone : ResidualResult
  licensed : ResidualResultEvidence c milestone

/--
Strongest/final reporting evidence. Each constructor excludes every stronger state
that would make that lower report an under-report. This is the machine surface for
the anchor's conservative strongest-supported reporting rule.
-/
def PrimaryResidualResultEvidence
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) : ResidualResult -> Prop
  | .novelObservablePressure =>
      NovelObservablePressure c ∧ ¬ SRWCandidate c
  | .srwCandidate =>
      SRWCandidate c ∧ ¬ ReplicatedSRW c
  | .replicatedSRW =>
      ReplicatedSRW c ∧ ¬ StateIncompletenessResolved c ∧ ¬ ClosureSuspended c
  | .stateIncompletenessResolved =>
      StateIncompletenessResolved c
  | .closureSuspended =>
      ClosureSuspended c
      ∧ (¬ c.candidateProposed
         ∨ (c.candidateProposed
             ∧ c.candidateNewnessState = .violated
             ∧ ¬ KnownCapacityReductionResolved c))
  | .fr6Candidate =>
      FR6Candidate c ∧ c.candidateNewnessState = .open
  | .knownCapacityReductionResolved =>
      KnownCapacityReductionResolved c
  | .fr6Earned =>
      FR6Earned c

/-- Public final residual-report certificate. -/
structure ResidualReportingCertificate
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId) where
  result : ResidualResult
  licensed : PrimaryResidualResultEvidence c result

/-- Scientific closure consequence of one residual result constructor. -/
def residualResultClosureStatus : ResidualResult -> FoundationalClosureStatus
  | .novelObservablePressure => .unchanged
  | .srwCandidate => .unchanged
  | .replicatedSRW => .unchanged
  | .stateIncompletenessResolved => .unchanged
  | .closureSuspended => .suspended
  | .fr6Candidate => .suspended
  | .knownCapacityReductionResolved => .restoredAtTestedScope
  | .fr6Earned => .reopenedAtTestedScope

/-- Closure status licensed by the strongest/final residual report. -/
def reportingClosureStatus
    {ObjectId RouteId ScaleId BranchId : Type}
    {c : ResidualContract ObjectId RouteId ScaleId BranchId}
    (cert : ResidualReportingCertificate c) : FoundationalClosureStatus :=
  residualResultClosureStatus cert.result

/-- A closure-survived report is unavailable while suspension or reopening is active. -/
def ClosureSurvivalReportAllowed : FoundationalClosureStatus -> Prop
  | .unchanged => True
  | .restoredAtTestedScope => True
  | .suspended => False
  | .reopenedAtTestedScope => False

/-! --------------------------------------------------------------------------
Ordered blockers and anti-shortcut theorems
---------------------------------------------------------------------------- -/

/-- Observable novelty alone contains no route-failure conclusion. -/
theorem srw_requires_route_failure
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (h : SRWCandidate c) :
    c.branch.routeContract.record.jRoute = .fail := by
  rcases h with ⟨_, _, hHandoff⟩
  exact hHandoff.2.2.2.2.1

/-- SRW requires occurrence of the relevant interaction-produced difference E. -/
theorem srw_requires_produced
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (h : SRWCandidate c) :
    c.branch.routeContract.record.produced := by
  rcases h with ⟨_, _, hHandoff⟩
  exact hHandoff.2.2.2.1

/-- J_ROUTE = PASS blocks SRW. -/
theorem route_pass_blocks_srw
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hPass : c.branch.routeContract.record.jRoute = .pass) :
    ¬ SRWCandidate c := by
  intro h
  have hFail := srw_requires_route_failure c h
  rw [hPass] at hFail
  contradiction

/-- Absence of E blocks SRW entry. -/
theorem absent_produced_blocks_srw
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hNoE : ¬ c.branch.routeContract.record.produced) :
    ¬ SRWCandidate c := by
  intro h
  exact hNoE (srw_requires_produced c h)

/-- A known first-break evidence record blocks SRW on the same route. -/
theorem known_first_break_blocks_srw
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (k : FirstBreakClass)
    (hKnown : FirstBreakEvidence c.branch.routeContract.record k) :
    ¬ SRWCandidate c := by
  intro h
  rcases h with ⟨_, _, hHandoff⟩
  have hRoute : RouteFailureWithoutKnownBreak c.branch.routeContract.record :=
    hHandoff.2.2.2.2
  have hNoBreak : NoLiveFoundationalBreak c.branch.routeContract.record.g := hRoute.2.2
  exact (no_live_break_blocks_any_named_first_break
    c.branch.routeContract.record hNoBreak k) hKnown

/-- Any unresolved registered condition prevents the all-known-capacities-pass SRW gate. -/
theorem unresolved_condition_blocks_no_live_break
    (g : StateVector)
    (q : Condition)
    (hOpen : statusAt g q = .unresolved) :
    ¬ NoLiveFoundationalBreak g := by
  cases q <;> simp_all [statusAt, NoLiveFoundationalBreak, NoBreakAtSeat]

/-- Therefore an unresolved first-break condition blocks SRW. -/
theorem unresolved_live_condition_blocks_srw
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (q : Condition)
    (hOpen : statusAt c.branch.routeContract.record.g q = .unresolved) :
    ¬ SRWCandidate c := by
  intro h
  rcases h with ⟨_, _, hHandoff⟩
  have hRoute : RouteFailureWithoutKnownBreak c.branch.routeContract.record :=
    hHandoff.2.2.2.2
  exact (unresolved_condition_blocks_no_live_break
    c.branch.routeContract.record.g q hOpen) hRoute.2.2

/-- SRW cannot originate on a secondary diagnostic scale. -/
theorem secondary_scale_blocks_srw
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hSecondary : c.branch.routeContract.record.scaleRole = .secondary) :
    ¬ SRWCandidate c := by
  intro h
  have hPrimary : c.branch.routeContract.record.scaleRole = .primary :=
    h.2.2.2.2.1.2.1
  rw [hSecondary] at hPrimary
  cases hPrimary

/-- Search failure cannot be promoted into SRW. -/
theorem search_failure_blocks_srw
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hSearchFail : SearchFailed c.branch) :
    ¬ SRWCandidate c := by
  intro h
  have hAdequate : SearchAdequate c.branch := h.2.2.2.1
  exact (search_failure_blocks_adequate_branch_results c.branch hSearchFail) hAdequate

/-- Broken branch setup cannot be promoted into SRW. -/
theorem branch_setup_not_ready_blocks_srw
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hNotReady : ¬ BranchSetupReady c.branch) :
    ¬ SRWCandidate c := by
  intro h
  exact hNotReady h.2.2.1

/-- Open search adequacy cannot be promoted into SRW. -/
theorem search_open_blocks_srw
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hSearchOpen : SearchOpen c.branch) :
    ¬ SRWCandidate c := by
  intro h
  have hAdequate : SearchAdequate c.branch := h.2.2.2.1
  unfold SearchOpen at hSearchOpen
  unfold SearchAdequate at hAdequate
  rw [hSearchOpen] at hAdequate
  cases hAdequate

/-- Open or violated Layer-A entry cannot be promoted into SRW. -/
theorem entry_not_ready_blocks_srw
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hNotReady : ¬ EntryReady c.branch.routeContract) :
    ¬ SRWCandidate c := by
  intro h
  have hReady : EntryReady c.branch.routeContract := h.2.2.2.2.1.1
  exact hNotReady hReady

/-- One unreplicated SRW cannot suspend closure. -/
theorem unreplicated_srw_does_not_suspend_closure
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hNoReplication : ¬ c.srwReplicationSucceeded) :
    ¬ ClosureSuspended c := by
  intro h
  rcases h with ⟨hReplicated, _, _, _⟩
  exact hNoReplication hReplicated.2

/-- Replication without exhausting the pre-frozen state-completeness ladder is insufficient. -/
theorem replicated_srw_without_state_completeness_does_not_suspend
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hNotExhausted : ¬ c.stateCompletenessExhausted) :
    ¬ ClosureSuspended c := by
  intro h
  rcases h with ⟨_, hExhausted, _, _⟩
  exact hNotExhausted hExhausted

/-- Resolution by a richer admitted ordinary state blocks closure suspension. -/
theorem richer_state_resolution_blocks_closure_suspension
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hResolved : c.richerOrdinaryStateResolves) :
    ¬ ClosureSuspended c := by
  intro h
  rcases h with ⟨_, _, hNotResolved, _⟩
  exact hNotResolved hResolved

/-- Closure suspension is available exactly through the maximal-state residual gate. -/
theorem maximal_state_residual_permits_closure_suspension
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (h : MaximalStateStructuralResidual c) :
    ClosureSuspended c := by
  exact h

/-- FR6 candidate cannot be licensed without closure already suspended. -/
theorem fr6_candidate_requires_closure_suspended
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (h : FR6Candidate c) :
    ClosureSuspended c := by
  exact h.1

/-- FR6 earned requires the candidate-newness summary itself to be discharged. -/
theorem fr6_earned_requires_discharged_candidate_newness
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (h : FR6Earned c) :
    c.candidateNewnessState = .discharged := by
  exact h.2.1

/-- FR6 earned inherits the full candidate gate. -/
theorem fr6_earned_requires_candidate
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (h : FR6Earned c) :
    FR6Candidate c := by
  exact h.1

/-- Known-capacity reduction restores closure only through an explicit witness-resolution adjudication. -/
theorem known_capacity_reduction_resolution_requires_actual_resolution
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (h : KnownCapacityReductionResolved c) :
    c.knownCapacityReductionResolvesWitness := by
  exact h.2.2.2

/-- A reduction label by itself does not prove restored closure. -/
theorem reduction_without_resolution_does_not_restore_closure
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hNoResolution : ¬ c.knownCapacityReductionResolvesWitness) :
    ¬ KnownCapacityReductionResolved c := by
  intro h
  exact hNoResolution h.2.2.2

/-- A final closure-suspended report cannot be down-reported as mere observable novelty. -/
theorem closure_suspended_blocks_final_novelty_only_report
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hSuspended : ClosureSuspended c) :
    ¬ PrimaryResidualResultEvidence c .novelObservablePressure := by
  intro hFinal
  exact hFinal.2 hSuspended.1.1

/-- A final closure-suspended report cannot be down-reported as an unreplicated SRW. -/
theorem closure_suspended_blocks_final_srw_only_report
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hSuspended : ClosureSuspended c) :
    ¬ PrimaryResidualResultEvidence c .srwCandidate := by
  intro hFinal
  exact hFinal.2 hSuspended.1

/-- FR6 EARNED cannot be final-reported as only an open FR6 candidate. -/
theorem fr6_earned_blocks_final_candidate_only_report
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hEarned : FR6Earned c) :
    ¬ PrimaryResidualResultEvidence c .fr6Candidate := by
  intro hFinal
  have hOpen : c.candidateNewnessState = .open := hFinal.2
  have hDischarged : c.candidateNewnessState = .discharged := hEarned.2.1
  rw [hOpen] at hDischarged
  cases hDischarged

/-- A rejected candidate whose witness remains unresolved returns to final CLOSURE SUSPENDED. -/
theorem violated_candidate_with_unresolved_witness_supports_final_suspension
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hSuspended : ClosureSuspended c)
    (hProposed : c.candidateProposed)
    (hViolated : c.candidateNewnessState = .violated)
    (hNotResolved : ¬ KnownCapacityReductionResolved c) :
    PrimaryResidualResultEvidence c .closureSuspended := by
  exact ⟨hSuspended, Or.inr ⟨hProposed, hViolated, hNotResolved⟩⟩

/-- Reduction to one of the known five blocks FR6 earned. -/
theorem reduction_to_existing_capacity_blocks_fr6_earned
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hReduction : c.reducesToKnownFive) :
    ¬ FR6Earned c := by
  intro h
  exact h.2.2.nonReduction hReduction

/-- Functional equivalence / ordinary redescription blocks FR6 earned. -/
theorem functional_equivalence_blocks_fr6_earned
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hEquivalent : c.functionallyEquivalentToKnown) :
    ¬ FR6Earned c := by
  intro h
  exact h.2.2.nonEquivalence hEquivalent

/-- Necessity is load-bearing rather than documentary. -/
theorem failed_necessity_blocks_fr6_earned
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hNoNecessity : ¬ c.necessityEstablished) :
    ¬ FR6Earned c := by
  intro h
  exact hNoNecessity h.2.2.necessity

/-- Failed irreducibility / unique-removal pressure blocks FR6 earned. -/
theorem failed_irreducibility_blocks_fr6_earned
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hNoIrreducibility : ¬ c.uniqueRemovalOrIrreducible) :
    ¬ FR6Earned c := by
  intro h
  exact hNoIrreducibility h.2.2.irreducibility

/-- Failed complete-result replication blocks FR6 earned. -/
theorem failed_complete_replication_blocks_fr6_earned
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hNoReplication : ¬ c.completeResultReplicated) :
    ¬ FR6Earned c := by
  intro h
  exact hNoReplication h.2.2.completeReplication

/-- Failed independent procedural reproduction blocks FR6 earned. -/
theorem failed_independent_reproduction_blocks_fr6_earned
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hNoReproduction : ¬ c.independentlyReproduced) :
    ¬ FR6Earned c := by
  intro h
  exact hNoReproduction h.2.2.independentReproduction

/-- If intervention is physically available, failed removal blocks FR6 earned. -/
theorem available_failed_removal_blocks_fr6_earned
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hAvailable : c.interventionAvailable)
    (hRemovalFailed : ¬ c.removalTestPassed) :
    ¬ FR6Earned c := by
  intro h
  have hTests := h.2.2.intervention.2 hAvailable
  exact hRemovalFailed hTests.1

/-- If intervention is physically available, failed restoration blocks FR6 earned. -/
theorem available_failed_restoration_blocks_fr6_earned
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hAvailable : c.interventionAvailable)
    (hRestorationFailed : ¬ c.restorationTestPassed) :
    ¬ FR6Earned c := by
  intro h
  have hTests := h.2.2.intervention.2 hAvailable
  exact hRestorationFailed hTests.2

/-- Even when intervention is unavailable, availability itself must have been adjudicated. -/
theorem unadjudicated_intervention_availability_blocks_fr6_earned
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (hUnadjudicated : ¬ c.interventionAvailabilityAdjudicated) :
    ¬ FR6Earned c := by
  intro h
  exact hUnadjudicated h.2.2.intervention.1

/-- FR6 earned explicitly carries every positive foundational-newness burden. -/
theorem fr6_earned_requires_full_registered_newness_contract
    {ObjectId RouteId ScaleId BranchId : Type}
    (c : ResidualContract ObjectId RouteId ScaleId BranchId)
    (h : FR6Earned c) :
    NewnessAuditComplete c := by
  exact h.2.2

/-- Reporting firewall: CLOSURE SUSPENDED cannot be reported as closure survived. -/
theorem closure_suspended_blocks_reporting_closure_survived :
    ¬ ClosureSurvivalReportAllowed FoundationalClosureStatus.suspended := by
  simp [ClosureSurvivalReportAllowed]

/-- FR6 earned produces the scoped experimental reopening disposition. -/
theorem fr6_earned_reopens_at_tested_scope :
    residualResultClosureStatus ResidualResult.fr6Earned = .reopenedAtTestedScope := by
  rfl

/--
The current Universal Kernel still says exactly what it said before this experiment:
inside the current architecture, every irreducible first-break candidate collapses
to one of the five known regimes.  Layer C does not mutate that theorem; an earned
FR6 is instead the experiment-owned signal that the architecture must be reopened.
-/
theorem current_kernel_five_regime_closure_is_unchanged
    (R : FailureClosure.RouteSnapshot -> Prop)
    (c : FailureClosure.FirstBreakCandidate R) :
    (forall s, R s -> FailureClosure.Dissolution s)
    ∨ (forall s, R s -> FailureClosure.Shear s)
    ∨ (forall s, R s -> FailureClosure.Drift s)
    ∨ (forall s, R s -> FailureClosure.Echo s)
    ∨ (forall s, R s -> FailureClosure.Lock s) := by
  exact FailureClosure.no_sixth_irreducible_first_break_regime_inside_current_architecture R c

/-! --------------------------------------------------------------------------
Layer-C checkpoint
---------------------------------------------------------------------------- -/

theorem layer_c_checkpoint :
    residualResultClosureStatus .novelObservablePressure = .unchanged
    ∧ residualResultClosureStatus .srwCandidate = .unchanged
    ∧ residualResultClosureStatus .replicatedSRW = .unchanged
    ∧ residualResultClosureStatus .stateIncompletenessResolved = .unchanged
    ∧ residualResultClosureStatus .closureSuspended = .suspended
    ∧ residualResultClosureStatus .fr6Candidate = .suspended
    ∧ residualResultClosureStatus .knownCapacityReductionResolved = .restoredAtTestedScope
    ∧ residualResultClosureStatus .fr6Earned = .reopenedAtTestedScope := by
  decide

end DarkMatterFailureRegimeLayerC
end StructuralFlow


/-!
===============================================================================
DARK-MATTER FAILURE-REGIME ADAPTER / CONTRACT — INTERNAL LAYER D
PROGRAM-LEVEL AGGREGATION AND CLAIM LICENSE
===============================================================================

SCIENTIFIC AUTHORITY
--------------------
Five Failure Regimes in Dark-Matter Light Probes:
An Open-Source Pre-Result Demonstration Protocol.
Use the governing accepted edition supplied with the release package.

ROLE
----
Layer D does not re-adjudicate branch science. Layers A-C own the branch-level
classification, downstream result, and residual/reopening routes.

Layer D owns only the program-reporting firewall:

1. every registered branch remains accounted for in the program record;
2. any intended cross-branch / cross-regime claim scope is frozen pre-target;
3. claim-support branches are a subset of the registered branch universe;
4. claim-support branches must actually have been tested;
5. a cross-regime U1 claim requires U1 on every branch in the frozen claim set;
6. the claim set must share the declared program object and claim content;
7. pairwise compatibility and any cross-scale relation must be admitted under the
   pre-frozen compatibility rule;
8. a cross-regime claim requires at least two structurally distinct first-break
   classes;
9. program-level closure-survival language requires an actual foundational closure
   test under registered pressure, a finalized closure result, and a surviving or
   restored status at every claimed scope;
10. unresolved / untested branches may carry `none` class or closure values rather
   than invented defaults.

PROGRAM-REPORTING AUTHORITY BOUNDARY
-----------------------------------
The governing anchor owns the pre-target program-claim scope, complete branch
accounting, compatibility rule, and any admitted cross-scale relation. Lean does
not decide which branches are physically compatible or whether a given cross-scale
relation is scientifically warranted. Those are executor/domain inputs. Lean checks
only whether a claimed aggregation carries the predeclared burdens supplied to it.
===============================================================================
-/

namespace StructuralFlow
namespace DarkMatterFailureRegimeLayerD

open DarkMatterFailureRegimeLayerA
open DarkMatterFailureRegimeLayerB
open DarkMatterFailureRegimeLayerC

/-! --------------------------------------------------------------------------
Layer-D program record surface
---------------------------------------------------------------------------- -/

/--
One program-level reporting contract.

`claimBranch` is the exact branch set declared before target access as the support
set for the particular cross-branch claim under consideration.  It is not a
post-result filter.
-/
structure ProgramContract
    (BranchId ProgramObjectId ClaimContentId : Type) where
  programObject : ProgramObjectId
  claimContent : ClaimContentId

  /- Registered program universe and frozen claim-support set. -/
  registeredBranch : BranchId -> Prop
  claimBranch : BranchId -> Prop

  /- Final accounting / execution state. -/
  recordPresent : BranchId -> Prop
  tested : BranchId -> Prop
  u1Earned : BranchId -> Prop

  /- Structural and closure identity carried by each branch record. None is lawful for unresolved / untested records. -/
  firstBreakClass : BranchId -> Option FirstBreakClass
  closureStatusAt : BranchId -> Option FoundationalClosureStatus

  /- Foundational-closure reporting burdens. -/
  closureTestPlacedUnderPressure : BranchId -> Prop
  closureStatusFinalized : BranchId -> Prop

  /- Domain-owned aggregation warrants. -/
  matchesDeclaredProgramObject : BranchId -> Prop
  matchesDeclaredClaimContent : BranchId -> Prop
  mutuallyCompatible : BranchId -> BranchId -> Prop
  scaleRelationAdmitted : BranchId -> BranchId -> Prop

  /- Pre-target program-claim freeze burdens. -/
  programObjectDeclaredPreTarget : Prop
  claimContentDeclaredPreTarget : Prop
  claimBranchSetFrozenPreTarget : Prop
  compatibilityRuleFrozenPreTarget : Prop
  scaleRelationRuleFrozenPreTarget : Prop

/-- All program-claim scoping choices existed before target access. -/
structure ProgramClaimFreezeReady
    {BranchId ProgramObjectId ClaimContentId : Type}
    (p : ProgramContract BranchId ProgramObjectId ClaimContentId) : Prop where
  programObject : p.programObjectDeclaredPreTarget
  claimContent : p.claimContentDeclaredPreTarget
  claimBranchSet : p.claimBranchSetFrozenPreTarget
  compatibilityRule : p.compatibilityRuleFrozenPreTarget
  scaleRule : p.scaleRelationRuleFrozenPreTarget

/-- Every branch registered in the execution remains represented in the program record. -/
def CompleteRegisteredAccounting
    {BranchId ProgramObjectId ClaimContentId : Type}
    (p : ProgramContract BranchId ProgramObjectId ClaimContentId) : Prop :=
  forall b, p.registeredBranch b -> p.recordPresent b

/-- A program claim cannot silently import an unregistered branch. -/
def ClaimSetWithinRegisteredUniverse
    {BranchId ProgramObjectId ClaimContentId : Type}
    (p : ProgramContract BranchId ProgramObjectId ClaimContentId) : Prop :=
  forall b, p.claimBranch b -> p.registeredBranch b

/-- Every branch used to support the declared program claim was actually tested. -/
def ClaimSetTested
    {BranchId ProgramObjectId ClaimContentId : Type}
    (p : ProgramContract BranchId ProgramObjectId ClaimContentId) : Prop :=
  forall b, p.claimBranch b -> p.tested b

/-- Every branch in the frozen support set earned branch-scoped U1. -/
def ClaimSetEarnedU1
    {BranchId ProgramObjectId ClaimContentId : Type}
    (p : ProgramContract BranchId ProgramObjectId ClaimContentId) : Prop :=
  forall b, p.claimBranch b -> p.u1Earned b

/-- Every claim-support branch instantiates the same declared program object. -/
def ClaimSetMatchesProgramObject
    {BranchId ProgramObjectId ClaimContentId : Type}
    (p : ProgramContract BranchId ProgramObjectId ClaimContentId) : Prop :=
  forall b, p.claimBranch b -> p.matchesDeclaredProgramObject b

/-- Every claim-support branch supports the same exact declared claim content. -/
def ClaimSetMatchesClaimContent
    {BranchId ProgramObjectId ClaimContentId : Type}
    (p : ProgramContract BranchId ProgramObjectId ClaimContentId) : Prop :=
  forall b, p.claimBranch b -> p.matchesDeclaredClaimContent b

/-- All claim-support branches are mutually compatible under the frozen rule. -/
def ClaimSetMutuallyCompatible
    {BranchId ProgramObjectId ClaimContentId : Type}
    (p : ProgramContract BranchId ProgramObjectId ClaimContentId) : Prop :=
  forall b1 b2,
    p.claimBranch b1 ->
    p.claimBranch b2 ->
    p.mutuallyCompatible b1 b2

/-- Any relation among different registered primary scales is admitted under the frozen rule. -/
def ClaimSetScaleCompatible
    {BranchId ProgramObjectId ClaimContentId : Type}
    (p : ProgramContract BranchId ProgramObjectId ClaimContentId) : Prop :=
  forall b1 b2,
    p.claimBranch b1 ->
    p.claimBranch b2 ->
    p.scaleRelationAdmitted b1 b2

/-- A cross-regime claim requires at least two support branches in different first-break classes. -/
def StructurallyCrossRegime
    {BranchId ProgramObjectId ClaimContentId : Type}
    (p : ProgramContract BranchId ProgramObjectId ClaimContentId) : Prop :=
  exists b1 b2 k1 k2,
    p.claimBranch b1
    ∧ p.claimBranch b2
    ∧ p.firstBreakClass b1 = some k1
    ∧ p.firstBreakClass b2 = some k2
    ∧ k1 ≠ k2

/--
Positive certificate for a bounded cross-regime U1 claim.

This is intentionally a one-constructor proposition so downstream theorems can
project named burdens without dependent-match fragility.
-/
structure CrossRegimeUtilityClaimLicensed
    {BranchId ProgramObjectId ClaimContentId : Type}
    (p : ProgramContract BranchId ProgramObjectId ClaimContentId) : Prop where
  freezeReady : ProgramClaimFreezeReady p
  completeAccounting : CompleteRegisteredAccounting p
  withinRegisteredUniverse : ClaimSetWithinRegisteredUniverse p
  tested : ClaimSetTested p
  earnedU1 : ClaimSetEarnedU1 p
  sameProgramObject : ClaimSetMatchesProgramObject p
  sameClaimContent : ClaimSetMatchesClaimContent p
  compatible : ClaimSetMutuallyCompatible p
  scaleCompatible : ClaimSetScaleCompatible p
  crossRegime : StructurallyCrossRegime p

/-- Closure-survival reporting is a separate claim license from U1 aggregation. -/
structure ProgramClosureSurvivalLicensed
    {BranchId ProgramObjectId ClaimContentId : Type}
    (p : ProgramContract BranchId ProgramObjectId ClaimContentId) : Prop where
  freezeReady : ProgramClaimFreezeReady p
  completeAccounting : CompleteRegisteredAccounting p
  withinRegisteredUniverse : ClaimSetWithinRegisteredUniverse p
  tested : ClaimSetTested p
  closurePressure :
    forall b,
      p.claimBranch b ->
      p.closureTestPlacedUnderPressure b
  closureFinalized :
    forall b,
      p.claimBranch b ->
      p.closureStatusFinalized b
  closureSurvives :
    forall b,
      p.claimBranch b ->
      (p.closureStatusAt b = some FoundationalClosureStatus.unchanged
       ∨ p.closureStatusAt b = some FoundationalClosureStatus.restoredAtTestedScope)

/-! --------------------------------------------------------------------------
Layer-D positive consequences and blockers
---------------------------------------------------------------------------- -/

/-- Program-level aggregation cannot silently drop a registered branch record. -/
theorem cross_regime_claim_requires_complete_registered_accounting
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (h : CrossRegimeUtilityClaimLicensed p) :
    CompleteRegisteredAccounting p := by
  exact h.completeAccounting

/-- The support set itself is frozen before target access. -/
theorem cross_regime_claim_requires_pre_target_support_set
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (h : CrossRegimeUtilityClaimLicensed p) :
    p.claimBranchSetFrozenPreTarget := by
  exact h.freezeReady.claimBranchSet

/-- Missing accounting for any registered branch blocks the aggregate U1 claim. -/
theorem missing_registered_record_blocks_cross_regime_u1
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (b : BranchId)
    (hRegistered : p.registeredBranch b)
    (hMissing : ¬ p.recordPresent b) :
    ¬ CrossRegimeUtilityClaimLicensed p := by
  intro h
  exact hMissing (h.completeAccounting b hRegistered)

/-- A branch cannot be selected into the claim set after the fact without being registered. -/
theorem unregistered_claim_branch_blocks_cross_regime_u1
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (b : BranchId)
    (hClaim : p.claimBranch b)
    (hUnregistered : ¬ p.registeredBranch b) :
    ¬ CrossRegimeUtilityClaimLicensed p := by
  intro h
  exact hUnregistered (h.withinRegisteredUniverse b hClaim)

/-- One successful tested branch cannot promote an untested branch inside the frozen support set. -/
theorem untested_claim_branch_blocks_cross_regime_u1
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (b : BranchId)
    (hClaim : p.claimBranch b)
    (hUntested : ¬ p.tested b) :
    ¬ CrossRegimeUtilityClaimLicensed p := by
  intro h
  exact hUntested (h.tested b hClaim)

/-- A branch in the frozen support set that did not earn U1 blocks that exact aggregate claim. -/
theorem non_u1_claim_branch_blocks_cross_regime_u1
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (b : BranchId)
    (hClaim : p.claimBranch b)
    (hNoU1 : ¬ p.u1Earned b) :
    ¬ CrossRegimeUtilityClaimLicensed p := by
  intro h
  exact hNoU1 (h.earnedU1 b hClaim)

/-- Program-object mismatch blocks aggregation even when branch-local U1 was earned. -/
theorem program_object_mismatch_blocks_cross_regime_u1
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (b : BranchId)
    (hClaim : p.claimBranch b)
    (hMismatch : ¬ p.matchesDeclaredProgramObject b) :
    ¬ CrossRegimeUtilityClaimLicensed p := by
  intro h
  exact hMismatch (h.sameProgramObject b hClaim)

/-- Claim-content mismatch blocks aggregation. -/
theorem claim_content_mismatch_blocks_cross_regime_u1
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (b : BranchId)
    (hClaim : p.claimBranch b)
    (hMismatch : ¬ p.matchesDeclaredClaimContent b) :
    ¬ CrossRegimeUtilityClaimLicensed p := by
  intro h
  exact hMismatch (h.sameClaimContent b hClaim)

/-- One incompatible pair blocks the single aggregate claim. -/
theorem incompatible_claim_pair_blocks_cross_regime_u1
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (b1 b2 : BranchId)
    (h1 : p.claimBranch b1)
    (h2 : p.claimBranch b2)
    (hIncompatible : ¬ p.mutuallyCompatible b1 b2) :
    ¬ CrossRegimeUtilityClaimLicensed p := by
  intro h
  exact hIncompatible (h.compatible b1 b2 h1 h2)

/-- Cross-scale aggregation without the frozen admitted relation is blocked. -/
theorem unadmitted_scale_relation_blocks_cross_regime_u1
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (b1 b2 : BranchId)
    (h1 : p.claimBranch b1)
    (h2 : p.claimBranch b2)
    (hNoScaleRelation : ¬ p.scaleRelationAdmitted b1 b2) :
    ¬ CrossRegimeUtilityClaimLicensed p := by
  intro h
  exact hNoScaleRelation (h.scaleCompatible b1 b2 h1 h2)

/-- A nominal multi-branch success confined to one first-break class is not cross-regime. -/
theorem no_structural_cross_regime_pair_blocks_cross_regime_u1
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (hNoPair : ¬ StructurallyCrossRegime p) :
    ¬ CrossRegimeUtilityClaimLicensed p := by
  intro h
  exact hNoPair h.crossRegime

/-- Missing foundational pressure blocks a closure-survival report even if the branch was otherwise tested. -/
theorem unpressured_claim_branch_blocks_program_closure_survival
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (b : BranchId)
    (hClaim : p.claimBranch b)
    (hNoPressure : ¬ p.closureTestPlacedUnderPressure b) :
    ¬ ProgramClosureSurvivalLicensed p := by
  intro h
  exact hNoPressure (h.closurePressure b hClaim)

/-- A branch with no finalized closure result cannot support a closure-survival report. -/
theorem unfinalized_closure_status_blocks_program_closure_survival
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (b : BranchId)
    (hClaim : p.claimBranch b)
    (hNotFinal : ¬ p.closureStatusFinalized b) :
    ¬ ProgramClosureSurvivalLicensed p := by
  intro h
  exact hNotFinal (h.closureFinalized b hClaim)

/-- No closure result may be invented for an unresolved / untested record. -/
theorem missing_closure_result_blocks_program_closure_survival
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (b : BranchId)
    (hClaim : p.claimBranch b)
    (hNone : p.closureStatusAt b = none) :
    ¬ ProgramClosureSurvivalLicensed p := by
  intro h
  rcases h.closureSurvives b hClaim with hUnchanged | hRestored
  · rw [hNone] at hUnchanged
    cases hUnchanged
  · rw [hNone] at hRestored
    cases hRestored

/-- CLOSURE SUSPENDED at any claim-support branch blocks a closure-survival report for that scope. -/
theorem suspended_claim_branch_blocks_program_closure_survival
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (b : BranchId)
    (hClaim : p.claimBranch b)
    (hSuspended : p.closureStatusAt b = some FoundationalClosureStatus.suspended) :
    ¬ ProgramClosureSurvivalLicensed p := by
  intro h
  rcases h.closureSurvives b hClaim with hUnchanged | hRestored
  · rw [hSuspended] at hUnchanged
    cases hUnchanged
  · rw [hSuspended] at hRestored
    cases hRestored

/-- Reopened closure likewise cannot be reported as five-regime closure survival. -/
theorem reopened_claim_branch_blocks_program_closure_survival
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (b : BranchId)
    (hClaim : p.claimBranch b)
    (hReopened : p.closureStatusAt b = some FoundationalClosureStatus.reopenedAtTestedScope) :
    ¬ ProgramClosureSurvivalLicensed p := by
  intro h
  rcases h.closureSurvives b hClaim with hUnchanged | hRestored
  · rw [hReopened] at hUnchanged
    cases hUnchanged
  · rw [hReopened] at hRestored
    cases hRestored

/-- U1 aggregation and foundational closure are intentionally separate licenses. -/
theorem cross_regime_u1_does_not_override_suspended_closure
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (_hU1 : CrossRegimeUtilityClaimLicensed p)
    (b : BranchId)
    (hClaim : p.claimBranch b)
    (hSuspended : p.closureStatusAt b = some FoundationalClosureStatus.suspended) :
    ¬ ProgramClosureSurvivalLicensed p := by
  exact suspended_claim_branch_blocks_program_closure_survival b hClaim hSuspended

/-! --------------------------------------------------------------------------
Layer-D checkpoint
---------------------------------------------------------------------------- -/

/--
Layer D closes when program-level reporting preserves registered-branch accounting,
pre-target claim scope, branch-local test identity, compatibility, scale relation,
and foundational-closure status rather than collapsing them into one global verdict.
-/
theorem layer_d_scope_firewall
    {BranchId ProgramObjectId ClaimContentId : Type}
    {p : ProgramContract BranchId ProgramObjectId ClaimContentId}
    (h : CrossRegimeUtilityClaimLicensed p) :
    p.claimBranchSetFrozenPreTarget
    ∧ CompleteRegisteredAccounting p
    ∧ ClaimSetWithinRegisteredUniverse p
    ∧ ClaimSetTested p
    ∧ ClaimSetEarnedU1 p
    ∧ ClaimSetMatchesProgramObject p
    ∧ ClaimSetMatchesClaimContent p
    ∧ ClaimSetMutuallyCompatible p
    ∧ ClaimSetScaleCompatible p
    ∧ StructurallyCrossRegime p := by
  exact ⟨h.freezeReady.claimBranchSet,
    h.completeAccounting,
    h.withinRegisteredUniverse,
    h.tested,
    h.earnedU1,
    h.sameProgramObject,
    h.sameClaimContent,
    h.compatible,
    h.scaleCompatible,
    h.crossRegime⟩

end DarkMatterFailureRegimeLayerD
end StructuralFlow
