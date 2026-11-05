import YM.Next.STATIONARY.Films.RankColor

/-!
# Joint gauge completion on the canonically repeated blocks

We only want the *flat* inverse. Obtain its pre-block strip from the joint completion in the
construction by using the film oracle on **zero input columns** -- no perturbative rank/det
estimates required. P,K fixed for the step, pricing hypotheses signaled before any length.
No asserted covariance bound on arbitrary-tag/masked actual outputs.
-/
noncomputable section
namespace YM.RG08.Line
open Stationary Function Set Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.Frobenius
set_option autoImplicit false
variable {G : Gauge} {P : Patch} {S K : KernelChoices} {σ : ℝ}

def dark (G : Gauge) (P : Patch) : Stationary.Bridge G P := 0
def blank (G : Gauge)(P : Patch) := arriving (dark G P)

theorem dark_price (hσ : σ ≤ 1) : Spotlight P (blank G P) σ (Real.exp 4) := by
  refine spotlight_cape (Φ:=dark G P) ?_ le_rfl (Poster.web _) hσ
  intro x hx v i
  unfold dark; dsimp only [Pi.zero_apply]; rw [Matrix.zero_mulVec]
  simp only [roster]
  change ‖(WithLp.toLp 2 (0 : Loc G 1 → ℂ) : EuclideanSpace ℂ (Loc G 1))‖ ≤ _
  rw [show (WithLp.toLp 2 (0 : Loc G 1 → ℂ) : EuclideanSpace ℂ (Loc G 1))=0 from rfl]
  rw [norm_zero]
  exact mul_nonneg (inch_pos _).le (Real.exp_pos _).le

theorem night {c f : Side} (S : StepData c f) : Premise S (0: Matrix (Body 1 f) (Body 1 c) ℝ) (dark G S.patch) := by
  unfold Premise
  have he : patron G (0:Matrix (Body 1 f) (Body 1 c) ℝ)=0 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    change _ *ᵥ x=(0:Matrix (Lines G f 1) (Lines G c 1) ℝ)*ᵥ x -- Funds square wrong
    rw [patron_fee,Matrix.zero_mulVec]
    ext1 v
    simp [uniformM]
  rw [he]
  have hv : approached (repackM (unitSplit G S 1) (Equiv.refl _) (0 : Matrix (Lines G f 1) (Lines G c 1) ℝ))=0 := by ext; simp [approached,repackM]
  rw [hv]; exact Jaunt.zero _

def fixSymbol (G : Gauge) (P : Patch) := (CanonR (blank G P) false).tab

theorem unmasked {c f : Side} (S : StepData c f) (hp : S.patch.Branches S.kernel G) (t : S.Choices) :
    Jaunt (approached (repackM (unitSplit G S 0) (clothe G S) (postroom S t (inch S.patch.L)))) (fixSymbol G S.patch) 0 := by
  classical
  let W : Matrix (Body 1 f) (Body 1 c) ℝ := 0
  let D := blank G S.patch
  let Z := cardHand (G:=G) W
  have hZ : Turns D (billZ S Z):= atlas_photo _ (night S)
  have hx := (regulator_tour S t false Z hZ hp (fun _=>rfl)).tab
  unfold cardM at hx
  dsimp only at hx
  rw [zero_hat S hp ..] at hx
  exact hx

-- choose a cofinal side sequence divisible for given P
abbrev sizes (i : ℕ) : Side := ⟨i+1,by omega⟩
abbrev depthSizes (P:Patch) (i:ℕ) : Side:= sizes i * P.L
abbrev atSide (P:Patch)(K:KernelChoices) : Armada sizes (depthSizes P) P K := ⟨fun _=>rfl⟩

theorem increasing : Tendsto (fun i => (sizes i).val) atTop atTop := tendsto_add_atTop_nat 1

theorem inventory (G : Gauge)(K : KernelChoices)(j : ℕ)(ε Ω σ : ℝ)(hε:0<ε)(hs:0<σ)(hσ:σ≤1)(hΩ:0≤Ω):
    ∃ η C : ℝ,0<η ∧ η≤σ ∧ 0≤C ∧ ∀ (P:Patch), P.J=j → P.Branches K G → ∀ (b:Bed) (p:Clip) (D : ℝ),
      b.metric.strip (inch P.L*σ) Ω → (∀ n,Floor b p n ε D) →
      let F := forceK G P (fixSymbol G P) K.penalty b
      Poster η F ∧ Freezer (slabW G P.L|>.dual) (slabW G P.L) F η C ∧ Poster η (fixSymbol G P) := by
  classical
  obtain ⟨z,B,hz,hz',hB,Hb⟩:=amasses G
  let u:=min σ z
  have hu:0<u:=lt_min hs hz
  have hh:u≤σ:=min_le_left ..
  let A:=|tribute2 G j (Real.exp 4) B|
  obtain ⟨η,C,hη,hη',hC,H⟩:=post_cert G j K ε u Ω A hε hu (hh.trans hσ) hΩ (abs_nonneg _)
  refine ⟨η,C,hη,hη'.trans hh,hC,fun P hP ht b p D hK hv=>?_⟩
  intro F
  have hQ := conquer (E:=blank G P) ht hu (dark_price (hh.trans hσ)) (Hb P.L u (min_le_right ..))
  have hp : Poster u (fixSymbol G P):= hQ.covered.tab
  have hx : b.metric.strip (inch P.L*u) Ω:= fun i j=> (hK i j).mono (mul_le_mul_of_nonneg_left hh (inch_pos _).le) le_rfl
  have hZ i : Nonempty ((atSide P K).boot i).Choices:= inferInstance
  let t i := Classical.choice (hZ i)
  exact ⟨(Poster.amounts (gift_lane b _ hx hu) (hp.reverse.forge hp)).skinny hη',
    H _ hP ht b p _ (fixSymbol G P) _ _ (atSide P K) increasing hx hv hp (fun _ hw=> (hQ.base hw).mono (hP ▸ le_abs_self _)) t (fun i=>unmasked _ ht (t i)),hp.skinny hη'⟩
end YM.RG08.Line
