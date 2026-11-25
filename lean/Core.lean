import Std

namespace CriminalSystem

/-
Uncompiled candidate. Assessed inputs require independent source and legal review.
No theorem here establishes real case facts or applicability to a real case.
-/

structure SourceRef where
  documentId : String
  versionId : String
  articleId : String
  officialUrl : String
  snapshotHash : Option String

/-- Day ordinals are supplied by an independently verified calendar conversion. -/
structure EffectWindow where
  starts : Nat
  endsExclusive : Option Nat

/-- Formal entry into force only; criminal retroactivity is a separate question. -/
def formallyInForce (w : EffectWindow) (day : Nat) : Prop :=
  w.starts ≤ day ∧
    match w.endsExclusive with
    | none => True
    | some stop => day < stop

theorem startIncluded :
    formallyInForce ⟨10, some 20⟩ 10 := by decide

theorem endExcluded :
    ¬ formallyInForce ⟨10, some 20⟩ 20 := by decide

inductive Assessment where
  | established | refuted | unknown | conflicting
  deriving DecidableEq, Repr

inductive Trigger where
  | triggered | notTriggered | unresolved
  deriving DecidableEq, Repr

def negateAssessment : Assessment → Assessment
  | .established => .refuted
  | .refuted => .established
  | .unknown => .unknown
  | .conflicting => .conflicting

/-- Conservative audit aggregation, NOT classical or Belnap conjunction. -/
def auditConjunction : Assessment → Assessment → Assessment
  | .conflicting, _ => .conflicting
  | _, .conflicting => .conflicting
  | .refuted, _ => .refuted
  | _, .refuted => .refuted
  | .established, .established => .established
  | _, _ => .unknown

def allAssessments (xs : List Assessment) : Assessment :=
  xs.foldr auditConjunction .established

def toTrigger : Assessment → Trigger
  | .established => .triggered
  | .refuted => .notTriggered
  | .unknown => .unresolved
  | .conflicting => .unresolved

theorem unknownNotRefuted :
    Assessment.unknown ≠ Assessment.refuted := by decide

theorem assessmentNegationInvolutive (a : Assessment) :
    negateAssessment (negateAssessment a) = a := by
  cases a <;> rfl

/-
CPP55 local gates only. "factsSupported" covers guilt and sentencing facts;
"evidenceVerified" requires verification through statutory procedure.
A passing evidence gate is not sufficient to order a conviction.
-/
structure CPP55Input where
  caseId : String
  onlyConfession : Assessment
  factsSupported : Assessment
  evidenceVerified : Assessment
  reasonableDoubtExcluded : Assessment

def cpp55ConvictionBar (f : CPP55Input) : Trigger :=
  toTrigger f.onlyConfession

def cpp55EvidenceGate (f : CPP55Input) : Trigger :=
  toTrigger (allAssessments [
    negateAssessment f.onlyConfession,
    f.factsSupported,
    f.evidenceVerified,
    f.reasonableDoubtExcluded])

def confessionOnlySample : CPP55Input :=
  ⟨"synthetic-case", .established, .unknown, .unknown, .unknown⟩

def evidenceGateSample : CPP55Input :=
  ⟨"synthetic-case", .refuted, .established, .established, .established⟩

theorem confessionOnlyBarsConviction :
    cpp55ConvictionBar confessionOnlySample = .triggered := by decide

theorem assessedEvidenceGatePasses :
    cpp55EvidenceGate evidenceGateSample = .triggered := by decide

theorem unresolvedDoubtDoesNotPass :
    cpp55EvidenceGate
      { evidenceGateSample with reasonableDoubtExcluded := .unknown }
      = .unresolved := by decide

/-
CPP56 confession branch. The method must already have been assessed as falling
within this article's coercive illegal-method category, not any procedural defect.
-/
structure Confession56Input where
  evidenceId : String
  isSuspectOrDefendantConfession : Assessment
  qualifyingIllegalMethod : Assessment

def cpp56Confession (f : Confession56Input) : Trigger :=
  toTrigger (allAssessments [
    f.isSuspectOrDefendantConfession, f.qualifyingIllegalMethod])

theorem illegalConfessionTriggers :
    cpp56Confession ⟨"synthetic-e1", .established, .established⟩
      = .triggered := by decide

theorem uncertainMethodUnresolved :
    cpp56Confession ⟨"synthetic-e1", .established, .unknown⟩
      = .unresolved := by decide

inductive Remediation where
  | pending | cured | reasonablyExplained | neitherAvailable
  deriving DecidableEq, Repr

def neitherRemedyAvailable : Remediation → Assessment
  | .pending => .unknown
  | .cured => .refuted
  | .reasonablyExplained => .refuted
  | .neitherAvailable => .established

/-
All fields must refer to the same evidence. The record groups them by evidenceId;
it does not itself prove that externally supplied assessments are correctly bound.
-/
structure Material56Input where
  evidenceId : String
  isPhysicalOrDocumentary : Assessment
  unlawfulCollection : Assessment
  seriousJusticeRisk : Assessment
  remediation : Remediation

def cpp56Material (f : Material56Input) : Trigger :=
  toTrigger (allAssessments [
    f.isPhysicalOrDocumentary,
    f.unlawfulCollection,
    f.seriousJusticeRisk,
    neitherRemedyAvailable f.remediation])

def materialSample (r : Remediation) : Material56Input :=
  ⟨"synthetic-e2", .established, .established, .established, r⟩

theorem unremediableMaterialTriggers :
    cpp56Material (materialSample .neitherAvailable) = .triggered := by decide

theorem pendingRemediationUnresolved :
    cpp56Material (materialSample .pending) = .unresolved := by decide

theorem curedDoesNotTriggerThisBranch :
    cpp56Material (materialSample .cured) = .notTriggered := by decide

/-- Traceable outputs; missing snapshot hashes remain explicit. -/
structure Finding where
  source : SourceRef
  subjectId : String
  branchId : String
  result : Trigger

def cpp56Source : SourceRef :=
  { documentId := "PRC-CPP"
    versionId := "2018-amended"
    articleId := "56"
    officialUrl :=
      "https://www.samr.gov.cn/zw/zfxxgk/fdzdgknr/bgt/art/2025/art_48b3b0c3f954448e996602a71fc6f878.html"
    snapshotHash := none }

def cpp56MaterialFinding (f : Material56Input) : Finding :=
  { source := cpp56Source
    subjectId := f.evidenceId
    branchId := "physical-documentary-exclusion"
    result := cpp56Material f }

theorem findingPreservesSubject (f : Material56Input) :
    (cpp56MaterialFinding f).subjectId = f.evidenceId := by rfl

/-- Normative requirements and actual performance are separate. -/
structure EnforcementState where
  finding : Trigger
  exclusionPerformed : Bool

def exclusionRequired (w : EnforcementState) : Prop :=
  w.finding = .triggered

def exclusionOccurred (w : EnforcementState) : Prop :=
  w.exclusionPerformed = true

theorem noncompliancePossible :
    ∃ w : EnforcementState,
      exclusionRequired w ∧ ¬ exclusionOccurred w := by
  refine ⟨⟨.triggered, false⟩, ?_⟩
  decide

theorem obligationDoesNotGuaranteePerformance :
    ¬ (∀ w : EnforcementState, exclusionRequired w → exclusionOccurred w) := by
  intro h
  rcases noncompliancePossible with ⟨w, required, notOccurred⟩
  exact notOccurred (h w required)

#print axioms startIncluded
#print axioms endExcluded
#print axioms unknownNotRefuted
#print axioms assessmentNegationInvolutive
#print axioms confessionOnlyBarsConviction
#print axioms assessedEvidenceGatePasses
#print axioms unresolvedDoubtDoesNotPass
#print axioms illegalConfessionTriggers
#print axioms uncertainMethodUnresolved
#print axioms unremediableMaterialTriggers
#print axioms pendingRemediationUnresolved
#print axioms curedDoesNotTriggerThisBranch
#print axioms findingPreservesSubject
#print axioms noncompliancePossible
#print axioms obligationDoesNotGuaranteePerformance

end CriminalSystem


