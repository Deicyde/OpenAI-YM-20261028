import YM.Further.CURVED_GAUSSIAN_JETS.Motion

/-!
# Uniform column, defect and covariance jet estimates at the principal windows

Before domain tests or change to new coordinates. This is the envelope
argument only at each supplied U (and any direction predicate, priced
by Street). In TraceJets also license passing to the series there on
open unmasked extensions. No locality assumption on jets in the kernel
bounds. Need check decision supports later, and NEVER let derivatives
act on named hard indicators or change the windows without paying.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Jets
open Function Filter MeasureTheory Set Matrix Lattice SectorNext.Vacuum Wilson RG Precision Progress.StationaryScenes
open Green (wt wt_symm)
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff Classical
variable {n c : Side} {G : Gauge} {I : Type*} [Fintype I] [DecidableEq I] (W : Windows I) {a : I → Site n}
    {U : Config G c} {A : Field G c I} {s : Weights a} {M u : ℝ} {l : Word G c} {k N : ℕ}
    {Q : Directions G c → Prop} {p : Prices}

def slab (W : Windows I) (A : Field G c I) (i : I) : Field G c (W.box i) := fun V => W.localGram (A V) i
def probe (W : Windows I) (A : Field G c I) (u : ℝ) : Field G c I := fun V => W.column (A V) u
def err (W : Windows I) (A : Field G c I) (u : ℝ) : Field G c I := fun V => W.defect (A V) u
def covariance (W : Windows I) (A : Field G c I) : Field G c I := fun V => W.blend (A V)
def coeff (W : Windows I) (A : Field G c I) : Field G c I := fun V => A V * covariance W A V - 1
variable (h : Street p s k Q A U M)
include h
lemma Street.slab (i : I) : Street p (s.restrict (W.inside i)) k Q (slab W A i) U M := h.restrict _
lemma Street.probe (hu : 0≤u) : Good (probe W A u) k U := by
  intro i j; unfold Jets.probe Windows.column; simp only [Matrix.of_apply]; split <;> rename_i hi
  · exact ((Street.slab W h j).eye hu) ⟨i,hi⟩ (W.center j)
  exact contDiffAt_const
lemma Street.err (hu : 0≤u) : Good (err W A u) k U := ((h.good.raise _).prod (Street.probe W h hu)).minus (Good.const 1)
lemma Street.covariance : Good (covariance W A) k U := (Good.plus (Street.probe W h (u:=0) le_rfl)
    ((Street.probe W h (u:=0) le_rfl).transpose)).scale (1/2:ℝ)
lemma Street.coeff : Good (coeff W A) k U := (h.good.prod (Street.covariance W h)).minus (Good.const _)
omit h in
lemma jet_probe (i j : I) (hi : i∈W.box j) : jet l (probe W A u) U i j = jet l (eye (slab W A j) u) U ⟨i,hi⟩ (W.center j) := by
  simp only [jet,of_apply,probe,Windows.column,hi,dif_pos,eye,slab,Windows.resolvent]

/-- Fixed numerical order losses. Keep the decay factors separately. -/
def column_cost (p : Prices) (s : Weights a) (k : ℕ) (M : ℝ) := discount p s k M k * p.tags * Push.Uniform.countCost (spare p)
def defect_cost (p : Prices) (s : Weights a) (k : ℕ) (M : ℝ) := s.pay k*M*column_cost p s k M
def sharp_cost (p : Prices) (s : Weights a) (k : ℕ) (M : ℝ) := s.pay k * discount p s k M k * defect_cost p s k M
def line_cost (p : Prices) (s : Weights a) (k : ℕ) (M : ℝ) := s.pay k*M*sharp_cost p s k M
omit h in
lemma cost_pos (p : Prices) (s : Weights a) (k : ℕ) {M : ℝ} (hm : 0≤M) : 0 ≤ column_cost p s k M ∧ 0 ≤ defect_cost p s k M ∧ 0 ≤ sharp_cost p s k M ∧ 0 ≤ line_cost p s k M := by
  have hp := (discount_pos p s k hm k); have hh := s.pay_pos k; have ht := Push.Uniform.count_pos (spare_pos p)
  unfold line_cost sharp_cost defect_cost column_cost; constructor <;> try positivity
  refine ⟨by positivity,by positivity,by positivity⟩
omit h in
lemma smaller (p : Prices) : 0<3*spare p ∧ 3*spare p≤p.speed := by have := four_spare p; have := spare_pos p; constructor <;> linarith

lemma columns_pay (hu : 0≤u) : Cash s (3*spare p) k Q U (probe W A u) (column_cost p s k M / (1+u)) := by
  intro l hl hd
  let C := discount p s k M k / (1+u)
  have hC := show 0≤C by unfold C; have := discount_pos p s k h.has k; positivity
  have he i j (hi : i∉W.box j) : jet l (probe W A u) U i j=0 := by
    rw [jet_entry_eq (b:=0) i j (Eventually.of_forall fun V=>dif_neg hi),ite_self]
  have H (j : I) := eye_budget (Street.slab W h j) hu le_rfl l hl hd
  have hc (j : I) (k' : ℕ) : discount p (s.restrict (W.inside j)) k M k'=discount p s k M k' := by
    induction k' with | zero => rfl | succ k' ih => simp only [discount,ih]; rfl
  let E (i j : I) := wt (s.width p.speed l.length) (a i) (a j)
  let f := jet l (probe W A u) U
  have hu i j : E i j * |f i j| ≤ C * s.τ i^l.length ∧ E j i*|f i j| ≤ C*s.τ j^l.length := by
    unfold f; by_cases hx : i∈W.box j
    · rw [jet_probe W i j hx]; unfold C; rw [← hc j]; exact ⟨(H j).1.here ⟨i,hx⟩ (W.center j), (H j).2.here (W.center j) ⟨i,hx⟩⟩
    rw [he i j hx,abs_zero,mul_zero,mul_zero]; exact ⟨mul_nonneg hC (pow_nonneg (s.nonneg _) _),mul_nonneg hC (pow_nonneg (s.nonneg _) _)⟩
  have hr : 3*spare p < p.speed := by have := four_spare p; linarith [spare_pos p]
  have he := Weights.from_points (k:=l.length) hr h.base.mult (fun i j => (hu i j).1) hC
  have he' := Weights.from_points (A:=f.transpose) (k:=l.length) hr h.base.mult (fun i j => (hu j i).2) hC
  rw [column_cost,mul_div_right_comm,mul_div_right_comm]; rw [show p.speed-3*spare p=spare p by linarith only [four_spare p]] at he he'; exact ⟨he,he'⟩

variable (hb : W.Includes a N)
include hb
lemma defect_pay (hu : 0≤u) : Cash s (2*spare p) k Q U (err W A u) ( (defect_cost p s k M)*Real.exp (-spare p*N)/(1+u)) := by
  have hx := spare_pos p; have hy := h.has
  have hC := cost_pos p s k hy
  have hp := columns_pay W h hu
  have he := (h.cash.mono (smaller p).2 le_rfl).product hp h.good (Street.probe W h hu) (h.space (show spare p≤3*spare p by linarith)) h.has (div_nonneg hC.1 (by positivity))
  intro l hl hd
  have h₁ i j (hij : i∈W.box j) : jet l (err W A u) U i j=0 := by
    have hg := ((h.slab W j).good.raise u).near_regular ((Street.slab W h j).base.shift_pos hu).isUnit
    rw [jet_entry_eq i j (b:=0) (hg.mono (fun V hv=> ?_)),ite_self]
    -- does not require uniform Fits at every V in neighborhood!
    have he := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hv)
    have hm := congr_arg (fun T : Table (W.box j)=> T ⟨i,hij⟩ (W.center j)) he
    rw [Matrix.mul_apply] at hm
    change (∑ z : W.box j, shifted (W.localGram (A V) j) u ⟨i,hij⟩ z * W.resolvent _ _ _ z (W.center j)) = _ at hm
    conv at hm => lhs; arg 2; intro z; rw [show z=⟨z.val,z.property⟩ from rfl,W.local_entry (A V) hij z.property]
    unfold err Windows.defect; rw [Matrix.sub_apply, Windows.restricted_mul,hm]; simp [Matrix.one_apply,Windows.center]
  let f := jet l (fun V => A V * probe W A u V) U
  let e := jet l (err W A u) U
  have h₂ i j (hh : i∉W.box j) : e i j=f i j := by
    unfold e f jet; simp_rw [Matrix.of_apply,err, Windows.outside_defect _ _ _ _ hh]; rfl
  have hh := he l hl hd
  let v (n : ℝ) (i j : I) := wt (s.width (n*spare p) l.length) (a i) (a j)
  have hm i j : v 2 i j*|e i j| ≤ Real.exp (-spare p*N) * (v 3 i j*|f i j|) := by
    by_cases hij : i∈W.box j
    · rw [show e i j=0 from h₁ i j hij,abs_zero,mul_zero]; have := Green.wt_pos (s.width (3*spare p) l.length) (a i) (a j); unfold v; positivity
    rw [h₂ i j hij,←mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    unfold v wt Weights.width; rw [←Real.exp_add]; apply Real.exp_monotone
    have ht : (N:ℝ) < (separation (a i) (a j):ℝ) := by exact_mod_cast (lt_of_not_ge (mt (hb i j) hij))
    nlinarith only [hx,ht]
  have ht (e f : Table I) (h : s.Costs (3*spare p) l.length f (s.pay k*M*(column_cost p s k M/(1+u))))
      (hm : ∀ i j,v 2 i j*|e i j| ≤ Real.exp (-spare p*N)*(v 3 i j*|f i j|)) : s.Costs (2*spare p) l.length e
          ((defect_cost p s k M)*Real.exp (-spare p*N)/(1+u)) := fun i=> by
        apply (Finset.sum_le_sum fun j _ => hm i j).trans; rw [← Finset.mul_sum]
        apply (mul_le_mul_of_nonneg_left (h i) (Real.exp_pos _).le).trans_eq; unfold defect_cost; ring
  exact ⟨ht _ f hh.1 hm, ht e.transpose f.transpose hh.2 (fun i j=>by unfold v; rw [wt_symm _ (a i),wt_symm _ (a i)]; exact hm j i)⟩

omit hb h in
lemma error_eq (V : Config G c) (u : ℝ) (he : IsUnit (raise A u V)) : probe W A u V-eye A u V = eye A u V * err W A u V := by
  unfold raise at he
  unfold eye probe err Windows.defect; rw [Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp he),one_mul,mul_one]
lemma error_pay (hu : 0≤u) : Cash s (2*spare p) k Q U (fun V=> probe W A u V-eye A u V)
    (sharp_cost p s k M * Real.exp (-spare p*N) * Line.bell u) := by
  have hv : 2*spare p ≤ p.speed := (by linarith only [(smaller p).2,spare_pos p])
  have he := (eye_budget h hu le_rfl).mono hv le_rfl
  have hp := discount_pos p s k h.has k
  have hm := (cost_pos p s k h.has).2.1
  have ht := he.product (defect_pay W h hb hu) (h.eye hu) (h.err W hu) (h.space (by linarith only [spare_pos p])) (by positivity) (by positivity)
  intro l hl hd
  rw [jet_eq (((h.good.raise u).near_regular (h.base.shift_pos hu).isUnit).mono fun V hv=>error_eq W V u hv :
       (fun V=> probe W A u V-eye A u V) =ᶠ[𝓝 U] fun V=> eye A u V * err W A u V)]
  convert ht l hl hd using 1
  rw [Line.bell, sharp_cost, pow_two,one_div,mul_inv]; ring

lemma coeff_pay (herm : ∀ᶠ V in 𝓝 U, (A V).IsHermitian) : Cash s (2*spare p) k Q U (coeff W A) (line_cost p s k M * Real.exp (-spare p*N)) := by
  have hp := error_pay W h hb (u:=0) le_rfl; simp only [Line.bell,add_zero,one_pow,div_one,mul_one] at hp
  let f := fun V => probe W A 0 V-eye A 0 V
  have hs := hp.symmetrize ((Street.probe W h (u:=0) le_rfl).minus (h.eye (u:=0) le_rfl))
  have heq : coeff W A =ᶠ[𝓝 U] fun V=> A V*((1/2:ℝ) • (f V + (f V).transpose)) := by
    filter_upwards [herm, h.good.near_regular h.base.pos.isUnit] with V hv hV
    have he : (A V)⁻¹.transpose=(A V)⁻¹ := hv.inv
    unfold coeff covariance Windows.blend f probe eye; rw [shifted,zero_smul,add_zero,transpose_sub,he,
      sub_add_sub_comm, smul_sub, Matrix.mul_sub, ←two_smul ℝ,smul_smul,show (1/2:ℝ)*2=1 by norm_num,one_smul,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hV)]
  have hf := (Street.probe W h (u:=0) le_rfl).minus (h.eye (u:=0) le_rfl)
  have hg := (h.cash.mono (show 2*spare p≤p.speed by linarith only [(smaller p).2, spare_pos p]) le_rfl).product hs h.good ((hf.plus hf.transpose).scale _)
    (h.space (by linarith only [spare_pos p])) h.has (mul_nonneg (cost_pos p s k h.has).2.2.1 (Real.exp_pos _).le)
  intro l hl hd; rw [jet_eq heq,line_cost,mul_assoc (s.pay k*M)]; exact hg l hl hd

end YM.Further.CurvedGaussianJets.Jets
