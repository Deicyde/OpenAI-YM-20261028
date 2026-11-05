import YM.Pert.Parity.Twinning
import YM.Pert.Parity.EvenLow
import YM.Pert.Position.Four
/-! Parity of the finite-regulator position readings on a determining family constructed at horizon four. -/
noncomputable section
namespace YM.Pert.Parity
open Position Filter Labels Lattice Topology Classical Maxwell Climb Spec Rigid
open scoped Topology
variable {G : Gauge} (C : Family G) {I : Extraction.Order} {S : Table C.book}
lemma parity_four (hg : G.Simple) : ∃ (n : ℕ) (Q : Conditions C.labels 4 n) (J : Module.End ℝ (Fin n→ℝ)), square Q ∧ Fair Q J ∧ CleanProfiles Q := by
  obtain ⟨k,s,m,g,h,_⟩ := square_of_frozen C.labels 4 (frozen_four C.labels hg)
  obtain ⟨J,hj,he⟩ := make_pairing _ _ s g h
  exact ⟨m,_,J, hj, he,fun i=>⟨(duo C.labels 4 s i).f,rfl⟩⟩
variable {C} {n d : ℕ} {Q : Conditions C.labels d n} {φ : Ledger Q→Buffer C.labels d}
structure ParityFields (φ : Ledger Q→ Buffer C.labels d) : Prop where
  oddity {m} (R : Conditions C.labels d m) (L : Side) (hl : 1<L.val) (p j : ℕ) :
     ∀ᶠ i in atTop, readJet φ p j (chart (reverseRows R)) (finite Q L i) (finite (reverseRows R) L i)= (-1:ℝ)^j • readJet φ p j (chart R) (finite Q L i) (finite R L i)
lemma fields_generator {J} (h : Fair Q J) (hc : CleanProfiles Q) (h₁ : Reports (chart Q) (white Q) 0 φ) : ParityFields φ := ⟨fun R L hl p j=> position_sign h h₁ L hc hl R p j⟩
variable (b : Final C I S) (X : Scaling S)

theorem parityEndpoint (hg : G.Simple) {c : ℝ} (hc : 0<c) : ∃ C : Family G,
  C.path.levels.clock.kernel.penalty=c ∧ Extraction.Wcmain C ∧
  MergeProof.Ribbons.Materials C ∧ MergeProof.Ribbons.Plenty C ∧ ∀ f : Extraction.Order,
    ∃ (g : Extraction.Order) (S : Table C.book) (b : Final C (f.refine g) S), ∃ X : Scaling S, FirstExtension b X ∧ Crest X ∧ ∃ (n : ℕ) (Q : Conditions C.labels 4 n) (φ : Ledger Q→Buffer C.labels 4) (J : Module.End ℝ (Fin n→ℝ)), CleanProfiles Q ∧ BoardAttains Q X φ ∧ Resident b X φ ∧ Fair Q J ∧ ParityFields φ := by
  obtain ⟨C,hc0,hW,hM,hP,H⟩ := crestTarget hg hc
  refine ⟨C,hc0,hW,hM,hP,fun f => ?_⟩
  obtain ⟨g,S,k,X,hX,hC⟩ := H f
  obtain ⟨n,Q,J,hq,hJ,hR⟩ := parity_four C hg
  obtain ⟨φ,hφ⟩ := hC.position _ _ Q hR hq
  exact ⟨g,S,k,X,hX,hC,n,Q,φ,J,hR,hφ,residency k X hX hg hR hφ,hJ,fields_generator hJ hR hφ.patch⟩
end YM.Pert.Parity
