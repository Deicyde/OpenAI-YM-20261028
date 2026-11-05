import YM.Work.F08.Mixed

/-!
Stack construction at uniform widths (F08). These are real kernels; only
entrywise strips are used, no square root/positivity properties of the given
rows.  Clip constants used in the rows of Bed.full are already available
before L. Keep every donated row of A0 and T (hence also their advances).
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.F08
open Lattice Laurent Precision RG Exterior Craft Bloch
open scoped BigOperators

/-- A period-independent (crude) work price for the finite stencil. -/
def stencilCost (r : ℕ) (η : ℝ) :=
  ∑ i : TypeFace (r+1), ∑ j : TypeFace r,
    ∑ z ∈ Exterior.support, Real.exp (η * size z) * ‖cobound r i j z‖

lemma strip_stencil (r : ℕ) (η : ℝ) : (cobound r).strip η (stencilCost r η) := by
  let F (i j) (z : Cover) := Real.exp (η * size z) * ‖cobound r i j z‖
  let D (i j) := ∑ z ∈ Exterior.support, F i j z
  have hn (i j) : 0 ≤ D i j :=
    Finset.sum_nonneg (fun z _ ↦ mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  intro i j
  change SumBudget (F i j) (∑ i, ∑ j, D i j)
  have hz (z : Cover) (h : z ∉ Exterior.support) : F i j z = 0 := by
    unfold F; rw [Exterior.certified _ _ _ _ h]; simp
  refine ⟨fun z ↦ mul_nonneg (Real.exp_pos _).le (norm_nonneg _),
    summable_of_ne_finset_zero hz, ?_⟩
  rw [tsum_eq_sum hz]
  calc
    D i j ≤ ∑ j, D i j := Finset.single_le_sum (fun k _ ↦ hn i k) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, D i j := Finset.single_le_sum (fun k _ ↦
      Finset.sum_nonneg (fun l _ ↦ hn k l)) (Finset.mem_univ i)

def fullRow (H : Bed) (p : Clip) : Row Layers2 (TypeFace 2) :=
  stackRows (scaleRows (Real.sqrt p.direct) (unitRow _)) H.roots

lemma strip_full (H : Bed) (p : Clip) {η A : ℝ} (h : H.roots.strip η A) :
    (fullRow H p).strip η (max ‖Real.sqrt p.direct‖ A) := by
  have hh := strip_stack (strip_scale (α := TypeFace 2) strip_unit (Real.sqrt p.direct)) h
  rwa [mul_one] at hh

lemma acts_full (H : Bed) (p : Clip) (n : Side) : (fullRow H p).acts n = H.full p n := by
  unfold fullRow
  rw [acts_stack, acts_scale, acts_unit]
  ext ⟨x,i⟩ ⟨y,j⟩; cases i <;> rfl

/-- Actual rows for every compatible pair of tori, with pre-L prices. -/
theorem answer : YM.Bid.F08 := by
  intro p q k Ω σ σ' Ω' ν V X _hk hσ hσ' hν
  let γ := min σ (min σ' ν)
  have he : 0 < γ := lt_min hσ (lt_min hσ' hν)
  have heσ : γ ≤ σ := min_le_left ..
  have heσ' : γ ≤ σ' := (min_le_right ..).trans (min_le_left ..)
  have heν : γ ≤ ν := (min_le_right ..).trans (min_le_right ..)
  let A := max ‖Real.sqrt p.direct‖ Ω
  let B := max ‖Real.sqrt q.direct‖ Ω'
  let n : ℝ := Fintype.card (TypeFace 2)
  let m : ℝ := Fintype.card (TypeFace 3)
  let l := (Real.sqrt k)⁻¹
  let CA := n * (A * Ω) -- H.full times inverse on fine side
  let CB := n * (B * Ω')
  let CL := n * (CA * Ω) -- after mixing, retain L^-2 separately
  let CF := n * (CL * B)
  let D₁ := stencilCost 1 γ
  let D₂ := stencilCost 2 γ
  let CN := ‖l‖ * (n * (D₁ * B))
  let Cproj := n * (CB * B)
  let Cup := m * (V * D₂)
  let CX := n * (Cup * Ω')
  let CO := max (1 + Cproj) (n * (CX * B))
  let M := max Ω (max CF (max CN CO))
  refine ⟨γ, M, he, ?_⟩
  intro H H' hH hH' P hP L _hodd S hS
  have hI : H.inverse.strip γ Ω := strip_mono hH.2.2.1 heσ le_rfl
  have hI' : H'.inverse.strip γ Ω' := strip_mono hH'.2.2.1 heσ' le_rfl
  let J := fullRow H p
  let J' := fullRow H' q
  let Jt := transRows J'
  have hJ : J.strip γ A := strip_full _ _ (strip_mono hH.2.2.2.1 heσ le_rfl)
  have hJ' : J'.strip γ B := strip_full _ _ (strip_mono hH'.2.2.2.1 heσ' le_rfl)
  have ht : Jt.strip γ B := strip_trans hJ'
  have hT : S.T.strip γ (Ω / (L.val:ℝ)^2) :=
    strip_mono ((hS [] (Nat.zero_le X)).2) heσ le_rfl
  let Y := composeRows J H.inverse
  let Z := composeRows J' H'.inverse
  have hY : Y.strip γ CA := strip_compose he.le hJ hI
  have hZ : Z.strip γ CB := strip_compose he.le hJ' hI'
  let Left := fineCompose Y S.T
  let mf := composeRows Left Jt
  have hLeft : Left.strip γ (CL / (L.val:ℝ)^2) := by
    rw [show CL / (L.val:ℝ)^2 = n * (CA * (Ω / (L.val:ℝ)^2)) from by unfold CL; ring]
    exact strip_fine he.le hY hT
  have hmf : mf.strip γ (CF / (L.val:ℝ)^2) := by
    rw [show CF / (L.val:ℝ)^2 = n * ((CL / (L.val:ℝ)^2) * B) from by unfold CF; ring]
    exact strip_compose he.le hLeft ht
  have hD₁ : (transRows (cobound 1)).strip γ D₁ := strip_trans (strip_stencil _ _)
  let mn := scaleRows l (composeRows (transRows (cobound 1)) Jt)
  have hmn : mn.strip γ CN := strip_scale (strip_compose he.le hD₁ ht) _
  let proj := composeRows Z Jt
  let D := composeRows P (cobound 2)
  let E := composeRows D H'.inverse
  let o := stackRows (minusRows (unitRow _) proj) (composeRows E Jt)
  have hPg : P.strip γ V := strip_mono hP heν le_rfl
  have hproj : proj.strip γ Cproj := strip_compose he.le hZ ht
  have hD : D.strip γ Cup := strip_compose he.le hPg (strip_stencil _ _)
  have hE : E.strip γ CX := strip_compose he.le hD hI'
  have ho : o.strip γ CO := strip_stack (strip_minus strip_unit hproj)
    (strip_compose he.le hE ht)
  let T : Towers L := ⟨S.A0, S.T, mf, mn, o⟩
  refine ⟨T, ?_, ?_⟩
  · have hΩ : Ω ≤ M := le_max_left ..
    have hF : CF ≤ M := le_max_of_le_right (le_max_left ..)
    have hN : CN ≤ M := le_max_of_le_right (le_max_of_le_right (le_max_left ..))
    have hO : CO ≤ M := le_max_of_le_right (le_max_of_le_right (le_max_right ..))
    refine ⟨strip_mono hmn le_rfl hN, strip_mono ho le_rfl hO,
      strip_mono hmf le_rfl (div_le_div_of_nonneg_right hF (by positivity)), ?_⟩
    intro w hw
    obtain ⟨h₀,h₁⟩ := hS w hw
    exact ⟨strip_mono h₀ heσ (div_le_div_of_nonneg_right hΩ (by positivity)),
      strip_mono h₁ heσ (div_le_div_of_nonneg_right hΩ (by positivity))⟩
  intro c f h
  let g : Ratio c f := ⟨L, h⟩
  have hpJ : J.acts f = H.full p f := acts_full _ _ _
  have hpJ' : J'.acts c = H'.full q c := acts_full _ _ _
  have hpt : Jt.acts c = (H'.full q c).transpose := by unfold Jt; rw [acts_trans, hpJ']
  change Replaces g H H' p q k P S T
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · change installed g (composeRows Left Jt) = _
    have hx : installed g Left = Y.acts f * installed g S.T := installed_fine g he.le hY hT
    have hy : Y.acts f = J.acts f * H.inverse.acts f := acts_compose he.le hJ hI f
    rw [installed_compose g he.le hLeft ht, hx, hy, hpJ, hpt]
  · change (scaleRows l (composeRows (transRows (cobound 1)) Jt)).acts c = _
    rw [acts_scale, acts_compose he.le hD₁ ht, acts_trans, hpt]
  change (stackRows (minusRows (unitRow _) proj) (composeRows E Jt)).acts c = _
  have hx : proj.acts c = Z.acts c * Jt.acts c := acts_compose he.le hZ ht c
  have hz : Z.acts c = J'.acts c * H'.inverse.acts c := acts_compose he.le hJ' hI' c
  have hd : D.acts c = P.acts c * (cobound 2).acts c :=
    acts_compose he.le hPg (strip_stencil _ _) c
  have hy : E.acts c = D.acts c * H'.inverse.acts c := acts_compose he.le hD hI' c
  rw [acts_stack, acts_minus he.le strip_unit hproj, acts_unit,
    acts_compose he.le hE ht, hx, hy, hd, hz, hpJ', hpt]

end YM.Work.F08
