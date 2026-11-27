import Hakem

/-! Güvenilmeyen ispatlar: korunum. -/

namespace Proofs

theorem physics_conserves :
    Physics.Thm (fun p => Unchanged (beforeAfter totalEnergy p)) := by
  rintro ⟨p, q⟩ ⟨a, h1, h2⟩
  dsimp only at h1 h2
  show p.e1 + p.e2 = q.e1 + q.e2
  omega

def physicsAccounting :
    Analogy Physics Accounting (beforeAfter totalEnergy) (beforeAfter balance) where
  red := fun (p : Ledger × Ledger) => (Bodies.mk p.1.kasa p.1.banka, Bodies.mk p.2.kasa p.2.banka)
  ax := by
    rintro ⟨p, q⟩ ⟨a, h1, h2⟩
    exact ⟨a, h1, h2⟩
  anchors := fun _ _ => rfl
  model := (⟨0, 0⟩, ⟨0, 0⟩)
  model_ax := ⟨0, by decide, by decide⟩

theorem analogy_physics_accounting :
    Nonempty (Analogy Physics Accounting (beforeAfter totalEnergy) (beforeAfter balance)) :=
  ⟨physicsAccounting⟩

theorem accounting_conserves_balance :
    Accounting.Thm (fun p => Unchanged (beforeAfter balance p)) :=
  physicsAccounting.toInterp.transfer_anchored physicsAccounting.anchors physics_conserves

def physicsBankTransfers :
    Analogy Physics (Banking.extend isTransfer) (beforeAfter totalEnergy) (beforeAfter deposits) where
  red := fun (p : Bank × Bank) =>
    (Bodies.mk p.1.mevduat1 p.1.mevduat2, Bodies.mk p.2.mevduat1 p.2.mevduat2)
  ax := by
    rintro ⟨p, q⟩ ⟨-, a, h1, h2, -⟩
    exact ⟨a, h1, h2⟩
  anchors := fun _ _ => rfl
  model := (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)
  model_ax := ⟨Or.inl ⟨0, by decide, by decide, rfl⟩, ⟨0, by decide, by decide, rfl⟩⟩

theorem analogy_physics_bankTransfers :
    Nonempty (Analogy Physics (Banking.extend isTransfer)
      (beforeAfter totalEnergy) (beforeAfter deposits)) :=
  ⟨physicsBankTransfers⟩

theorem bankTransfers_conserve_deposits :
    (Banking.extend isTransfer).Thm (fun p => Unchanged (beforeAfter deposits p)) :=
  physicsBankTransfers.toInterp.transfer_anchored physicsBankTransfers.anchors physics_conserves

def physicsBankingDeposits :
    Refutation Physics Banking (beforeAfter totalEnergy) (beforeAfter deposits) where
  claim  := Unchanged
  thm    := physics_conserves
  cex    := (⟨0, 0, 0⟩, ⟨1, 0, 1⟩)
  cex_ax := Or.inr ⟨1, by decide, by decide, by decide, by decide⟩
  fails  := by
    show ¬ ((0 : Int) + 0 = 1 + 0)
    decide

theorem metaphor_physics_banking_deposits :
    Nonempty (Refutation Physics Banking (beforeAfter totalEnergy) (beforeAfter deposits)) :=
  ⟨physicsBankingDeposits⟩

def physicsBankingNet :
    Analogy Physics Banking (beforeAfter totalEnergy) (beforeAfter netPosition) where
  red := fun (p : Bank × Bank) =>
    (Bodies.mk (p.1.mevduat1 - p.1.kredi) p.1.mevduat2,
     Bodies.mk (p.2.mevduat1 - p.2.kredi) p.2.mevduat2)
  ax := by
    rintro ⟨p, q⟩ (⟨a, h1, h2, h3⟩ | ⟨a, -, h1, h2, h3⟩) <;> dsimp only at h1 h2 h3
    · exact ⟨a, by dsimp only; omega, by dsimp only; omega⟩
    · exact ⟨0, by dsimp only; omega, by dsimp only; omega⟩
  anchors := by
    rintro ⟨p, q⟩ -
    show (_, _) = (_, _)
    simp only [totalEnergy, netPosition]
    congr 1 <;> omega
  model := (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)
  model_ax := Or.inl ⟨0, by decide, by decide, rfl⟩

theorem analogy_physics_banking_net :
    Nonempty (Analogy Physics Banking (beforeAfter totalEnergy) (beforeAfter netPosition)) :=
  ⟨physicsBankingNet⟩

end Proofs
