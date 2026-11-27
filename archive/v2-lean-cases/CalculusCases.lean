import Hakem
import Solution.Calculus
import Solution.Finite

/-! Güvenilmeyen ispatlar: veri olarak verilen sertifikaların denetimi (yalnızca çekirdek hesabı). -/

namespace Proofs

theorem banking_net_proof_checks :
    check Banking.axioms (glossaryNet.trF conservationLaw) netProof = true := by decide +kernel

theorem bank_counterexample_checks :
    check Physics.axioms conservationLaw conservationProof = true ∧
    bankFin.checkTheory Banking = true ∧
    bankFin.refutes (glossaryDeposits.trF conservationLaw) = true := by decide +kernel

theorem policy_data_checks :
    check WithNorm.axioms preventAct preventProof = true ∧
    polWorld.checkTheory WithNorm = true ∧ polAlt.refutes preventAct = true := by decide +kernel

theorem banking_net_by_calculus : Banking.Entails (glossaryNet.trF conservationLaw) :=
  calculus_sound _ _ _ banking_net_proof_checks

theorem metaphor_by_data :
    Nonempty (Refutation Physics Banking (fun _ => true) (fun _ => true) glossaryDeposits) :=
  refutation_of_data Physics Banking _ _ glossaryDeposits conservationLaw conservationProof bankFin
    trivial bank_counterexample_checks.1 (by decide) bank_counterexample_checks.2.1
    bank_counterexample_checks.2.2

theorem verdict_by_data : Nonempty (PolicyVerdict WithNorm preventAct) :=
  verdict_of_data WithNorm preventAct preventProof polWorld polWorld.fn (fun _ _ => false)
    (fun _ => trivial) policy_data_checks.1 policy_data_checks.2.1 policy_data_checks.2.2

-- Challenge'daki iddialar, veri yoluyla:
theorem metaphor_physics_banking_deposits :
    Nonempty (Refutation Physics Banking (fun _ => true) (fun _ => true) glossaryDeposits) :=
  metaphor_by_data

theorem policy_verdict_prevent : Nonempty (PolicyVerdict WithNorm preventAct) := verdict_by_data

end Proofs
