import YM.Next.FREE_KERNELS.Eject
import YM.Next.FREE_KERNELS.Ground

/-!
# Commit both neighboring linear prices before any length

`pledges` appropriate as standalone pricing lemma: includes support for
steps within stages and at transitions, independent of Levels. Routed l₀
pre-L. External choice of clips remains possible after this. No calibration
price/services assumed. Use BEFORE path dependent scheduling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid
open Work.F06 (sqLength pairingRe countCeil)
open Work.F07 (Band)
open scoped Topology BigOperators ComplexConjugate

def Mag (j t : ℕ) : Prop := 4≤j ∧ 4≤t ∧ (t=j ∨ t+1=j)

def BottomQuote (K : KernelChoices) (j : ℕ) (m γ σ η C : ℝ) := ∀ (p : Clip), p.direct≤γ → ∀ R : Train j,
    ∃ M : Bed, Defined K.penalty m R M ∧ M.covered σ C ∧ (∀ n, Floor M p n η C) ∧ (∀ n G, Bid.Sworn M n G) ∧
      (R=Train.top j → ∀ n,M.diagonal.acts n=1)
def HopQuote (K : KernelChoices) (j t : ℕ) (m l σ η C : ℝ) (b : ℕ) := ∀ P : Flight j t,
    let k := K.penalty
    let W := P.rollFunds k m l
    Donate (P.duo k) σ C (j-2) ∧ W.strip σ C ∧ (b ≤ P.L.val → Funds W η C)
structure Catalog (K : KernelChoices) (q : MapPrices) (l γ : ℕ → ℝ) (b : ℕ → ℕ) : Prop where
  net i : 0 ≤ l i
  fit i : 0 < γ i
  bottom (j) : 4 ≤ j → BottomQuote K j (l j) (γ j) (q.α j) (q.η j) (q.Ω j)
  hop (j t) : Mag j t → HopQuote K j t (l j) (l t) (q.α j) (q.η j) (q.Ω j) (b j)

lemma BottomQuote.revise {K : KernelChoices} {j : ℕ} {γ m σ η C σ' η' C' : ℝ} (h : BottomQuote K j m γ σ η C) (ht : σ'≤σ) (hk : η'≤η) (hC : C≤C') : BottomQuote K j m γ σ' η' C' := by
  intro p hp R; obtain ⟨M,h₁,h₂,h₃,h₄,h₅⟩ := h p hp R
  exact ⟨M,h₁,cover_revise h₂ ht hC, fun n => floor_revise (h₃ _) hk hC,h₄,h₅⟩
lemma HopQuote.revise {K : KernelChoices} {j t b b' : ℕ} {l m σ η C σ' η' C' : ℝ} (h : HopQuote K j t m l σ η C b) (ht : σ'≤σ) (hk : η'≤η) (hC : C≤C') (hb : b≤b') : HopQuote K j t m l σ' η' C' b' := by
  intro P
  obtain ⟨hh,h₁,h₂⟩ := h P
  refine ⟨fun i hi => ⟨strip_mono (hh i hi).1 ht (div_le_div_of_nonneg_right hC (by positivity)),
    strip_mono (hh i hi).2 ht (div_le_div_of_nonneg_right hC (by positivity))⟩,strip_mono h₁ ht hC,fun hi p hp => ?_⟩
  obtain ⟨hG,h⟩ := h₂ (hb.trans hi) p hp
  exact ⟨hG,fun x => ⟨(mul_le_mul_of_nonneg_right hk (Work.F06.sqLength_nonneg x)).trans (h x).1,(h x).2.trans (mul_le_mul_of_nonneg_right hC (Work.F06.sqLength_nonneg x))⟩⟩

lemma buys (K : KernelChoices) (j t : ℕ) : ∃ l₀ : ℝ, 0<l₀ ∧ ∀ (m l : ℝ), 0≤m → l₀ ≤ l → ∃ σ η C : ℝ, ∃ b : ℕ, 0<σ ∧ 0<η ∧ (Mag j t → HopQuote K j t m l σ η C b) := by
  by_cases h : Mag j t
  · obtain ⟨C,B,hC,hB,H⟩ := Flight.frontier K (show 4≤j from h.1) (show 4≤t from h.2.1)
    refine ⟨C,hC, fun m l hm hl => ?_⟩
    obtain ⟨v,σ,D,hv,hσ,hD,hP⟩ := H l m hm hl
    obtain ⟨σ₁,B₁,hp₁,hb₁,hh₁⟩ := ((secure_both K.penalty K.penalty_pos (show 4≤j from h.1) (show 4≤t from h.2.1)).1).honored h.1 1
    obtain ⟨σ₂,B₂,hp₂,hb₂,hh₂⟩ := ((secure_both K.penalty K.penalty_pos (show 4≤j from h.1) (show 4≤t from h.2.1)).2).honored h.1 2
    obtain ⟨b,hb⟩ := exists_nat_gt (m*B)
    let w := min σ (min σ₁ σ₂)
    let W := D+B₁+B₂
    refine ⟨w,v,W,b,lt_min hσ (lt_min hp₁ hp₂),hv,fun _ P => ?_⟩
    have he (p : C3) (hr : Funds p v D) : Funds p v W := by
      intro q hp; have hh := hr q hp; exact ⟨hh.1,fun x => ⟨(hh.2 x).1,(hh.2 x).2.trans (mul_le_mul_of_nonneg_right (by unfold W; linarith) (Work.F06.sqLength_nonneg _))⟩⟩
    refine ⟨fun i hi => ?_,strip_mono (hP P).1 (min_le_left ..) (by unfold W; linarith),fun hz => ?_⟩
    · exact ⟨strip_mono (hh₁ P i hi) ((min_le_right ..).trans (min_le_left ..)) (div_le_div_of_nonneg_right (by unfold W; linarith) (by positivity)),
        strip_mono (hh₂ P i hi) ((min_le_right ..).trans (min_le_right ..)) (div_le_div_of_nonneg_right (by unfold W; linarith) (by positivity))⟩
    apply he _ ((hP P).2 ?_); have hy : (b:ℝ) ≤ P.L.val := by exact_mod_cast hz
    have ht : 1 ≤ (P.L.val:ℝ) := by exact_mod_cast P.L.property
    nlinarith
  exact ⟨1,one_pos,fun _ _ _ _ => ⟨1,1,1,1,one_pos,one_pos,fun hz => False.elim (h hz)⟩⟩

lemma pledges (K : KernelChoices) : ∃ q l γ b,Catalog K q l γ b := by
  classical
  choose δ hδ h using buys K
  let l := fun i : ℕ => max (δ i i) (δ (i+1) i)
  have hl (i) : 0 ≤ l i := (hδ i i).le.trans (le_max_left ..)
  have hH (j t : ℕ) : ∃ σ η C : ℝ, ∃ b : ℕ, 0 < σ ∧ 0 < η ∧ (Mag j t → HopQuote K j t (l j) (l t) σ η C b) := by
    by_cases hp : Mag j t
    · apply h j t _ _ (hl _)
      rcases hp.2.2 with ht|ht
      · rw [ht]; exact le_max_left ..
      rw [← ht]; exact le_max_right ..
    exact ⟨1,1,1,1,one_pos,one_pos,fun hh => False.elim (hp hh)⟩
  choose S E T n hS hE hT using hH
  have hb (j : ℕ) : ∃ γ σ η C : ℝ, 0<γ ∧ 0<σ ∧ 0<η ∧ (4≤j → BottomQuote K j (l j) γ σ η C) := by
    by_cases he : 4 ≤ j
    · obtain ⟨γ,σ,η,C,hγ,hσ,hη,hC,h⟩ := bid_bed K.penalty (l j) K.penalty_pos (hl j) he
      exact ⟨γ,σ,η,C,hγ,hσ,hη,fun _ => h⟩
    exact ⟨1,1,1,1,one_pos,one_pos,one_pos,fun hz => False.elim (he hz)⟩
  choose γ t e u hγ ht he hu using hb
  let X : MapPrices := ⟨fun i => min (t i) (min (S i i) (S i (i-1))),
    fun i => max (u i) (max (T i i) (T i (i-1))),fun i => min (e i) (min (E i i) (E i (i-1))),
    fun i => lt_min (ht i) (lt_min (hS ..) (hS ..)),fun i => lt_min (he i) (lt_min (hE ..) (hE ..))⟩
  refine ⟨X,l,γ,fun i => max (n i i) (n i (i-1)),⟨hl,hγ,fun i hi => ?_,fun i j hij => ?_⟩⟩
  · exact (hu i hi).revise (min_le_left ..) (min_le_left ..) (le_max_left ..)
  apply (hT i j hij).revise
  all_goals
    rcases (show j=i ∨ j=i-1 by obtain hx := hij.2.2; omega) with hz|hz <;> rw [hz] <;> (try dsimp [X]) <;> grind
end YM.Next.Free
