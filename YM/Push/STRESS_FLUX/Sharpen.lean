import YM.Push.STRESS_FLUX.Low
import YM.Push.STRESS_FLUX.Matching
import YM.Push.STRESS_FLUX.Restore

/-!
Alternative introduction for `Quotes` from 's ancestor-scale
(a_k^h rather than e^h) budgets with possible signed equation terms in the
replicated-root tests. Uses finite Wilson IBP, doesn't ask for Ward/Killing
symmetry of a regulator. Costs are required on the ACTUAL joint alternative
(product minus matched field), not merely after removing the other cells or
identifying histories. Comparison field still represents the full weight D,
 including possible units, at the same literal reference of C.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Matching
open Wilson Lattice Cells Function Filter Set Asymptotics Extraction
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {C : Family G} {n : Side} {N p d D h k J m l : ℕ} {β ε : ℝ} {T : Tiling n} {f : Extraction.Order}

def Before (T : Tiling n) (β ε : ℝ) (F : Config G n → ℂ) : Prop := Interior (T.chamber 0) F ∧
  ∃ B, Interior (T.chamber 0) B ∧ T.rootTest β B ≤ ε ∧ ∃ j : ℕ, ∃ (x : Fin j → Site n) (d : Fin j → Step)
    (X : Fin j → Config G n → G.Color) (α : Fin j → Config G n → ℂ) (K : Fin j → Set (Site n)),
      (∀ i, RegularD (X i) ∧ Tame (α i) ∧ LocalOn (K i) (α i) ∧ x i ∈ T.chamber 0 ∧ x i ∉ K i) ∧
      ∀ U : Config G n, F U - B U = ∑ i, (↑(equation β (x i) (d i) (X i) U) : ℂ) * α i U

lemma before_test {F : Config G n → ℂ} (hb : Before T β ε F) : T.rootTest β F ≤ ε := by
  obtain ⟨h,B,hB,h1,j,x,d,X,α,K,hx,hE⟩ := hb
  exact (restore_equations T β h hB _ x d X α (fun i _ => (hx i).1) (fun i _ => (hx i).2.1) K (fun i _ => (hx i).2.2.1) (fun i _ => (hx i).2.2.2) hE) ▸ h1

lemma test_scale (F : Config G n → ℂ) (c : ℝ) (hc : 0 ≤ c) : T.rootTest β (fun U => (c:ℂ)*F U) ≤ c * T.rootTest β F := by
  apply le_of_pow_le_pow_left₀ T.cells_positive.ne' (mul_nonneg hc (T.root_nonneg β F))
  rw [mul_pow,T.powering,T.powering,T.rootPower_scale (t:=fun _ => c) (h:=fun _ => hc)]
  simp only [Finset.prod_const, Finset.card_univ, le_refl]

def prepared (C : Family G) (N p J m l : ℕ) (ε : ℝ) (F : Config G (C.side N p) → ℂ) := ∃ (_hm : m ≤ N) (hl : l ≤ N),
  ∀ T : Tiling (C.side N p), T.kind = .site → T.side.val=Cells.span C.S _hm p → SiteArray.aligned (Cells.span C.S hl p) T.base →
    (0 : Site (C.side N p)) ∈ T.margin 0 (T.side.val/(8*(J+1))) → Before T (C.beta N p) ε F

lemma rescale (v : C.label 4) (B : C.label d) {r : ℝ} {y : Site (C.side N p)} {u : C.label D} (c : ℝ) (hc : 0 ≤ c) (hp : prepared C N p J m l ε (cluster v B (r^h) y u)) :
    arrayTest C N p J m l (c^h * ε) (cluster v B ((c*r)^h) y ((c^h:ℂ) • u)) := by
  have he : cluster v B ((c*r)^h) y ((c^h:ℂ) • u) = fun U => (c^h:ℝ) * cluster v B (r^h) y u U := by
    funext U
    unfold cluster
    rw [mul_pow,Complex.ofReal_mul]
    have hu : C.seen (N:=N) (p:=p) ⟨D, (c^h:ℂ) • u⟩ 0 U = (c^h : ℂ) * C.seen ⟨D,u⟩ 0 U := congr_fun ((C.linearO N p D 0).map_smul (c^h) u) U
    rw [hu]; push_cast; ring
  obtain ⟨hm,hl,ht⟩ := hp
  rw [he]; refine ⟨hm,hl,fun T h1 h2 h3 h4 => ?_⟩
  have hh := ht T h1 h2 h3 h4
  exact ⟨(Interior.constant _ _).times hh.1, (test_scale _ _ (pow_nonneg hc _)).trans (mul_le_mul_of_nonneg_left (before_test hh) (pow_nonneg hc _))⟩

lemma squeeze_exp {g t w : ℕ → ℝ} {γ : ℝ} (hγ : 0<γ) (hg : ∀ k, 0<g k) (hr : Tendsto t atTop atTop)
    (hu : (Real.log ∘ g) =o[atTop] t) (hw : w =o[atTop] t) :
    Tendsto (fun k => g k ^ h * Real.exp (-γ * t k + w k)) atTop (𝓝 0) := by
  have hb : ∀ᶠ k : ℕ in atTop, g k^h * Real.exp (-γ*t k+w k) ≤ Real.exp (-(γ/2)* t k) := by
    filter_upwards [hu.bound (show 0<γ/(4*(h+1 : ℝ)) by positivity),hw.bound (show 0<γ/4 by positivity),hr.eventually (eventually_ge_atTop 0)] with k hk he hk'
    rw [← Real.exp_log (pow_pos (hg k) h), ← Real.exp_add, Real.log_pow]
    simp only [comp_apply,Real.norm_eq_abs,abs_of_nonneg hk'] at hk he
    apply Real.exp_le_exp.mpr
    have ht := (le_div_iff₀ (show (0:ℝ)<4*(h+1) by positivity)).mp (show |Real.log (g k)| ≤ γ * t k / (4*(h+1 : ℝ)) from by convert hk using 1; ring)
    nlinarith [(le_abs_self (Real.log (g k))), abs_nonneg (Real.log (g k)), le_abs_self (w k)]
  exact squeeze_zero' (Eventually.of_forall (fun k => by have := hg k; positivity)) hb (Real.tendsto_exp_atBot.comp (hr.const_mul_atTop_of_neg (by linarith)))

lemma separation_size {g : ℕ → ℝ} (hg : ∀ k, 0<g k) {b : ℕ → ℕ} (hb : Tendsto b atTop atTop)
    (hu : (Real.log ∘ g) =o[atTop] (C.S.scale ∘ b)) : Tendsto (fun k => g k * C.S.a (b k)) atTop (𝓝 0) := by
  have he k : -1*(C.S.scale ∘ b) k + (0 : ℝ) = Real.log (C.S.a (b k)) := by simp [Schedule.scale]
  have ht := squeeze_exp (h:=1) zero_lt_one hg (C.S.divergent.comp hb) hu (isLittleO_zero _ _)
  simpa only [he,Real.exp_log (C.S.a_pos _),pow_one] using ht

/-- A sufficient budget for `Quotes`. Scales may be chosen *after* the
coarse side and seam hierarchy requests, and every weight/component data
pair. Nodes themselves still at the tested spacings projected directly to
N (NOT just depth b k). Thresholds/coordinate norm bound can depend on the
fixed node z, not on p and N once on the tails. Subexponential growth or decay
here measured against the ACTUAL log(1/a_(b k)). No Gentle required for this
conversion. No paid root for the comparison difference with equations
restored is assumed. j=0/color-equation sum empty allowed. -/
def Ancestor (f : Extraction.Order) (v : Rows C) (B : C.label d) (D h : ℕ) :=
  ∀ J : ℕ, ∀ minM, ∃ m≥minM, ∀ minL : ℕ, ∃ l≥max m minL, ∃ b : ℕ → ℕ, ∃ g w : ℕ → ℝ, ∃ γ : ℝ,
    0<γ ∧ Tendsto b atTop atTop ∧ (∀ k, 0<g k) ∧ ((Real.log ∘ g) =o[atTop] (C.S.scale ∘ b)) ∧ (w =o[atTop] (C.S.scale ∘ b)) ∧
    ∀ᶠ k : ℕ in atTop, ∀ z : E4, 1/4 ≤ ‖z‖ → ‖z‖ ≤ 1 → ∀ a j : Axis, ∃ A : ℝ,
      ∀ᶠ i : ℕ×ℕ in f.fuse, ∃ u : C.label D, ‖u‖ ≤ A ∧
        prepared C i.1 i.2 J m l (Real.exp (-γ * C.S.scale (b k) + w k)) (cluster (v a j) B (C.S.a (b k) ^ h) (ceilSite C i.1 i.2 ((g k*C.S.a (b k)) • z)) u)

theorem quotes_of_ancestor {v : Rows C} {B : C.label d} (hp : Ancestor f v B D h) : Quotes f v B D h := by
  intro J m
  obtain ⟨m,hm,H⟩ := hp J m; refine ⟨m,hm,fun l => ?_⟩
  obtain ⟨l,hl,b,g,w,γ,hγ,hb,hg,hs,hw,he⟩ := H l
  refine ⟨l,hl,fun k => g k * C.S.a (b k),fun k => g k^h * Real.exp (-γ * C.S.scale (b k)+w k), fun k => ⟨mul_pos (hg _) (C.S.a_pos _),by have := hg k; positivity⟩, separation_size hg hb hs,
    squeeze_exp hγ hg (C.S.divergent.comp hb) hs hw,?_⟩
  filter_upwards [he] with k hk z hz hZ a j
  obtain ⟨A,hA⟩ := hk z hz hZ a j
  refine ⟨‖((↑(g k):ℂ)^h)‖ * A, hA.mono ?_⟩
  intro i hi; obtain ⟨u,hu,hU⟩ := hi
  refine ⟨_, ?_, rescale (v a j) B (g k) (hg k).le hU⟩
  exact norm_smul_le .. |>.trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
end YM.StressFlux.Matching
