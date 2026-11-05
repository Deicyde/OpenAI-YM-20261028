import YM.SectorNext.VACUUM_NORMALIZATION.Etch
import YM.SectorNext.VACUUM_NORMALIZATION.ForestLine
import YM.SectorNext.VACUUM_NORMALIZATION.Round


/-!
# Inactive completion and the scalar extraction ledger

Presumes neither stationary approximation nor Taylor jets of partition
sums. Input Gaussian-change interface uses the TRUE regular dimension
(m_H−|frozen|, times real Color finrank) and true covariance prefactor;
`unloads` converts to common extraction with explicit compensators. Use
`identity_price` if matrices supplied on regular-only coordinates; same
price and no extra exponent there. Keep scale of LocalRatio (j(0)), linkZ
and old v distinct. S is the matrix correction not a seed count. Work
in orthonormal *real* colors. No assertion that an arbitrary collection
of named matrices/local rules is the Gram of the Wilson integration;
need verify when applying (esp. relative to the very same change of vars).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open RG Precision Tree Wilson Matrix Lattice Filter Function
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {g : Ratio c f} (F : Forest g)

/-- Link count prior to freezing, exactly those used by `Forest.drape`. -/
def nt := Fintype.card F.Free
local notation "D[" A "]" => Module.finrank ℝ (Gauge.Color A)
local notation "Meter" => Round.Wall (Key F G)

lemma card_meter : Fintype.card (Key F G)=nt F * D[G] := by simp [Key, nt,Gauge.Color]
lemma bonds_nt : nt F= 3*Fintype.card (Site f)+Fintype.card (Site c) := by
  have he := FlatTree.count_clear F
  rw [Fintype.card_prod,show Fintype.card Axis=4 by decide] at he
  unfold nt; omega

-- Proof convention: tree excluded, inactive non-tree integrated in their own group variables or completed at Id
theorem identity_price {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J] [DecidableEq I] (e : I⊕J ≃ Key F G)
    (A : Meter) (T : Round.Wall I) (h : A.submatrix e e = Matrix.fromBlocks T 0 0 1) : A.det = T.det := by
  rw [← det_submatrix_equiv_self e, h, det_fromBlocks_zero₂₁, det_one,mul_one]

def gaussLink (A : ChartRatio G) (β : ℝ) := ((2*Real.pi/β)^((D[G]:ℝ)/2)) * A.scale
lemma link_factor_pos (A : ChartRatio G) (h : LocalRatio A) (β : ℝ) (he : 0<β) : 0<gaussLink A β := by
  unfold gaussLink; have := h.scale; have := Real.pi_pos; positivity

-- after individual chart integrations, before extracting common ledg3
def surface (A : ChartRatio G) (β : ℝ) (H : Finset F.Free) (C : Meter) :=
    ((2*Real.pi/β)^((((nt F-H.card)*D[G]:ℕ):ℝ)/2)) * A.scale^(nt F-H.card) * Real.sqrt C.det

def flatLine (A : ChartRatio G) (β : ℝ) (B : Meter) := gaussLink A β ^ nt F * (Real.sqrt B.det)⁻¹

def residualLog (A : ChartRatio G) (β : ℝ) (H : Finset F.Free) (B A₁ C : Meter) :=
    - (H.card:ℝ)*Real.log (gaussLink A β) - (Real.log A₁.det-Real.log B.det)/2 + Round.traceLog (A₁*C-1)/2

lemma unloads (A : ChartRatio G) (hA : LocalRatio A) (β : ℝ) (he : 0<β)
    (H : Finset F.Free) (B A₁ C : Meter) (hb : 0<B.det) (h : A₁.PosDef)
    (hC : C.IsHermitian) {q : ℝ} (hz : 0 ≤ q) (hq : q < 1) (hp : Round.rowRate q (A₁*C-1)) :
    0<C.det ∧ flatLine F A β B * Real.exp (residualLog F A β H B A₁ C)=surface F A β H C := by
  obtain ⟨hy,hI,_,ht⟩ := Round.exact_trace h hC _ rfl hp hz hq
  refine ⟨hy,?_⟩
  have hh := h.det_pos
  have hm : (1:Meter)+(A₁*C-1)=A₁*C := by abel
  rw [hm,Matrix.det_mul,Real.log_mul hh.ne' hy.ne'] at ht
  let s := gaussLink A β
  have hS : 0<s := link_factor_pos A hA β he
  let v := nt F-H.card
  have hU : ((2*Real.pi/β)^(((v*D[G]:ℕ):ℝ)/2)) * A.scale^v = s^v := by
    unfold s gaussLink; rw [mul_pow, ← Real.rpow_natCast ((2*Real.pi/β)^((D[G]:ℝ)/2)), ← Real.rpow_mul (by have h:=Real.pi_pos; positivity)]
    congr 2; push_cast; ring
  unfold surface flatLine residualLog
  change s^nt F * _ * Real.exp ( -(H.card:ℝ)*Real.log s-(_-_)/2+_/2) = _ * Real.sqrt C.det
  rw [hU,ht]
  have hR (b : ℝ) (hh : 0<b) : Real.log b = 2*Real.log (Real.sqrt b) := by rw [Real.log_sqrt hh.le]; ring
  rw [show -(H.card:ℝ)*Real.log s- (Real.log A₁.det-Real.log B.det)/2+(Real.log A₁.det+Real.log C.det)/2=
      Real.log (Real.sqrt B.det)+Real.log (Real.sqrt C.det)+ - ((H.card:ℝ)*Real.log s) by rw [hR B.det hb,hR C.det hy]; ring,
      Real.exp_add,Real.exp_add,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (Real.sqrt_pos.mpr hb),Real.exp_log (Real.sqrt_pos.mpr hy),Real.exp_log hS]
  rw [show nt F=v+H.card from (Nat.sub_add_cancel (Finset.card_le_univ H)).symm,pow_add]
  have := (Real.sqrt_pos.mpr hb).ne'
  field_simp




lemma log_form_anchor (A : ChartRatio G) (β : ℝ)
    (H : Finset F.Free) (B A₁ C : Meter) (hB : B.IsHermitian) (h : A₁.IsHermitian)
    {η L q : ℝ} (hN : Numeric B η L) (hI : Numeric A₁ η L) (hη : 0<η) (hL : η≤L) (hz : 0 ≤ q)
    (hq : q<1) (hp : Round.rowRate q (A₁*C-1)) :
    residualLog F A β H B A₁ C = -∑ _∈H,Real.log (gaussLink A β) +
      ∑ i : Key F G,(-(Panel.priceLine A₁ L i-Panel.priceLine B L i)/2+Round.onLine (A₁*C-1) i/2) := by
  unfold residualLog; rw [Panel.log_form A₁ h hI hη hL,Panel.log_form B hB hN hη hL,Round.lines _ hp hz hq]
  simp only [Finset.sum_add_distrib,neg_sub,← Finset.sum_div,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]; ring

end YM.SectorNext.Vacuum
