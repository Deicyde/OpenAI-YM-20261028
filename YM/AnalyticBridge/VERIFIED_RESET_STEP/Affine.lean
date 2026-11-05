import YM.AnalyticBridge.VERIFIED_RESET_STEP.Jets

/-! E:eq:FQaff. Work in native site units at the actual anchor. Gradients need only
agree on edges of the tested support; never identify a nonperiodic affine field
on the whole torus. Prices normalized by `(a.budget m).threshold` on each slot. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

variable {G : Gauge} {n : Side} {p : BudgetPoint} {X : Support n}

abbrev Flux (G : Gauge) := PlaqAxes → G.Color

structure LinearJet (G : Gauge) where
  at0 : Axis → G.Color
  slope : Axis → Axis → G.Color

def coord (o x : Site n) (j : Axis) : ℝ := lift (x-o) j

lemma small_coord (o x : Site n) (j : Axis) : |coord o x j| ≤ separation x o := by
  unfold coord separation
  exact_mod_cast ((Int.natCast_natAbs _).symm.trans_le (Int.ofNat_le.mpr (component_le (x-o) j)))

lemma lift_step {o x : Site n} (hx : 10*separation x o < n.val) (hn : 4 ≤ n.val) (d : Step) :
    lift (x + d.vec - o) = lift (x-o) + d.vec := by
  refine lift_eq_iff.mpr ⟨?_,fun i => ?_⟩
  · rw [map_add,wrap_lift,wrap_vec]; abel
  have hi : (lift (x-o) i).natAbs ≤ separation x o := component_le _ _
  rcases d with ⟨b,_|_⟩ <;> by_cases e : i=b <;> simp_all [Step.vec] <;> omega

lemma coord_step {o x : Site n} (hx : 10*separation x o < n.val) (hn : 4 ≤ n.val) (i j : Axis) :
    coord o (x+step i) j = coord o x j + if j=i then 1 else 0 := by
  unfold coord; rw [← Step.vec_pos, lift_step hx hn]; simp

namespace LinearJet
variable (a : LinearJet G)

def field (o : Site n) : Dir G n := fun e => a.at0 e.2 + ∑ j, coord o e.1 j • a.slope e.2 j
lemma isAffine (o : Site n) {v : Dir G n} : IsAffineDirection o v ↔ ∃ a : LinearJet G, v = a.field o := by
  constructor
  · rintro ⟨a,d,h⟩; refine ⟨⟨a,d⟩,funext fun e => ?_⟩
    simpa [field,coord,Int.cast_smul_eq_zsmul] using h e
  rintro ⟨a,rfl⟩; exact ⟨a.at0,a.slope,fun _ => by simp [field,coord,Int.cast_smul_eq_zsmul]⟩

def curl (i j : Axis) := a.slope j i - a.slope i j
def positive : Flux G := fun b => a.curl b.val.1 b.val.2

lemma field_step {o x : Site n} (hx : 10*separation x o < n.val) (hn : 4 ≤ n.val) (i j : Axis) :
    a.field o (x+step i,j) = a.field o (x,j) + a.slope j i := by
  rw [field,field]; simp only [coord_step hx hn,add_smul,Finset.sum_add_distrib,add_assoc]; congr 2
  simp [ite_smul]

lemma zero_symm (h : a.positive = 0) (i j) : a.slope j i = a.slope i j := by
  have he (i j : Axis) (hi : i < j) := sub_eq_zero.mp (show a.slope j i - a.slope i j = 0 from congr_fun h ⟨(i,j),hi⟩)
  rcases lt_trichotomy i j with hi|hi|hi
  · exact he i j hi
  · rw [hi]
  exact (he j i hi).symm

private def phi (o x : Site n) : G.Color :=
  (∑ i, coord o x i • (a.at0 i - (2:ℝ)⁻¹ • a.slope i i)) +
    (2 : ℝ)⁻¹ • ∑ i, ∑ j, (coord o x i * coord o x j) • a.slope i j

private lemma linear_step (o x : Site n) (d : Axis) (k : Axis → G.Color) (hx : 10 * separation x o < n.val) (hn : 4 ≤ n.val) :
    ∑ i, coord o (x+step d) i • k i = (∑ i, coord o x i • k i) + k d := by
  simp [coord_step hx hn,ite_smul,add_smul,Finset.sum_add_distrib]

private lemma phi_step (h : a.positive = 0) {o x : Site n} (hx : 10*separation x o < n.val) (hn : 4 ≤ n.val) (d : Axis) :
    a.phi o (x+step d) - a.phi o x = a.field o (x,d) := by
  simp_rw [phi,linear_step o x d _ hx hn,mul_smul,← Finset.smul_sum,linear_step o x d _ hx hn,
    smul_add,Finset.sum_add_distrib]
  simp_rw [a.zero_symm h d _]
  unfold field; module

lemma gradient_agrees {o : Site n} (h : Nonwrapping X o) (hn : 4 ≤ n.val) (ha : a.positive = 0) :
    ∃ s, Agrees X (gradient s) (a.field o) := ⟨a.phi o,fun e he _ => a.phi_step ha (h _ he) hn e.2⟩

instance : Sub (LinearJet G) := ⟨fun a b => ⟨fun i => a.at0 i-b.at0 i, fun i j => a.slope i j - b.slope i j⟩⟩

lemma field_sub (b : LinearJet G) (o : Site n) : (a-b).field o = a.field o - b.field o := by
  funext e
  change a.at0 _ - b.at0 _ + ∑ j,coord _ _ _ • (a.slope e.2 j - b.slope e.2 j) = _
  simp only [smul_sub,Finset.sum_sub_distrib,Pi.sub_apply,field]; abel
lemma positive_sub (b : LinearJet G) : (a-b).positive = a.positive - b.positive := by
  ext1 ⟨⟨i,j⟩,h⟩; change a.slope j i - b.slope j i - (a.slope i j - b.slope i j) = _ - _; dsimp [positive,curl]; abel

lemma hessian_curl₁ {f : Pot G n} (hG : G.Simple) (hf : p.Regular X f) {o : Site n} (h : Nonwrapping X o)
    (hn : 4 ≤ n.val) (b : LinearJet G) (hab : a.positive = b.positive) (u : Dir G n) :
    logHessian f (a.field o) u = logHessian f (b.field o) u := by
  obtain ⟨s,hs⟩ := (a-b).gradient_agrees h hn (by rw [positive_sub,hab,sub_self])
  have he := hessian_agrees hG hf hs (show Agrees X u u from fun _ _ _ => rfl)
  rw [hessian_gradient hG hf,field_sub,hessian_eq,map_sub,sub_apply,← hessian_eq, ← hessian_eq] at he
  linarith only [he]

lemma hessian_curl {f : Pot G n} (hG : G.Simple) (hf : p.Regular X f) {o : Site n} (h : Nonwrapping X o)
    (hn : 4 ≤ n.val) {a b c d : LinearJet G} (hab : a.positive = b.positive) (hcd : c.positive = d.positive) :
    logHessian f (a.field o) (c.field o) = logHessian f (b.field o) (d.field o) := by
  rw [a.hessian_curl₁ hG hf h hn b hab, hessian_symm hf, c.hessian_curl₁ hG hf h hn d hcd, hessian_symm hf]
end LinearJet

def wedge (b : PlaqAxes) (w : G.Color) : LinearJet G := ⟨0, fun i j => if b.val=(j,i) then w else 0⟩
lemma wedge_field (o : Site n) (b : PlaqAxes) (w : G.Color) (e : Edge (Site n)) :
    (wedge b w).field o e = if b.val.2=e.2 then coord o e.1 b.val.1 • w else 0 := by
  by_cases hh : b.val.2 = e.2 <;> simp [LinearJet.field,wedge,Prod.ext_iff,hh,smul_ite]
lemma curl_wedge (b : PlaqAxes) (w : G.Color) (i : PlaqAxes) : (wedge b w).positive i = if b=i then w else 0 := by
  obtain ⟨⟨k,l⟩,h⟩ := i; change k < l at h
  have hi := b.property; have h' : b.val ≠ (l,k) := fun he => by rw [he] at hi; exact lt_asymm h hi
  by_cases he : b.val = (k,l) <;> simp [LinearJet.positive,LinearJet.curl,wedge,h',he,Subtype.ext_iff,h.ne]

def primitive (w : Flux G) : LinearJet G := ⟨0,fun i j => ∑ b, (wedge b (w b)).slope i j⟩
lemma primitive_field (w : Flux G) (o : Site n) : (primitive w).field o = ∑ b, (wedge b (w b)).field o := by
  funext i; simpa [LinearJet.field, primitive, Finset.sum_apply, Finset.smul_sum,show ∀ b,(wedge b (w b)).at0 = 0 from fun _ => rfl] using Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun j b => coord o i.1 j • (wedge b (w b)).slope i.2 j)
@[simp] lemma positive_primitive (w : Flux G) : (primitive w).positive = w := by
  ext1 i
  change (∑ b, (wedge b (w b)).slope _ _) - ∑ b,(wedge b (w b)).slope _ _ = _
  rw [← Finset.sum_sub_distrib]; change ∑ b, (wedge b _).positive i = _; simp [curl_wedge]

lemma wedge_dir (o : Site n) (p : BudgetPoint) (b : PlaqAxes) (w : G.Color) (h : ‖w‖ ≤ 1) :
    p.dirBound o (p.threshold • (wedge b w).field o) := by
  intro e; rw [Pi.smul_apply,wedge_field,norm_smul,Real.norm_of_nonneg p.threshold_pos.le]
  apply mul_le_mul_of_nonneg_left _ p.threshold_pos.le
  split
  · rw [norm_smul,Real.norm_eq_abs]
    apply (mul_le_of_le_one_right (abs_nonneg _) h).trans
    have hp := p.power_ge
    exact (small_coord ..).trans <| (le_add_of_nonneg_left zero_le_one).trans <| by
      simpa using
        pow_le_pow_right₀ (show (1:ℝ) ≤ 1+↑(separation e.1 o) by simp) (by omega : 1 ≤ p.power)
  rw [norm_zero]; positivity
lemma wedge_avg (o : Site n) (p : BudgetPoint) (b c : PlaqAxes) (w : G.Color) (h : ‖w‖ ≤ 1) :
    p.dirBound o ((p.threshold/2) • ((wedge b w).field o + (wedge c w).field o)) := by
  intro e
  have hh (x : PlaqAxes) := wedge_dir o p x w h e
  simp only [Pi.smul_apply,norm_smul,Real.norm_of_nonneg p.threshold_pos.le] at hh
  rw [Pi.smul_apply,Pi.add_apply,norm_smul,Real.norm_of_nonneg (by have := p.threshold_pos; positivity : 0 ≤ p.threshold/2)]
  have hp := p.threshold_pos
  nlinarith [norm_add_le ((wedge b w).field o e) ((wedge c w).field o e),hh b,hh c]
end YM.AnalyticBridge.VerifiedReset
