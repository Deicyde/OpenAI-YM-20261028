import YM.Push.LOCAL_SPLITTING.Recovery

/-!
# Exact conversion of a raw single-source expansion on the SAME vacuum

The hypotheses
concern the pre-projection, pre-merger bulk/forced expansion and its actual
activity alphabet. In particular, Raw.Format does NOT require projection or
identity null. Raw.Income operates on the raw terms; the support reserves and
the constants at which to require that income are quantified further below. Linearity uses fixed addresses on a whole operand family, not a choice of
support or representation after each direction or coefficient is evaluated.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source Labels Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}

structure Raw (F : Labels.Frame G d) (n : Side) where
  seed : F.Coeff
  bulk : ℕ → Config G n → ℂ
  forced : ℕ → Config G n → ℂ

namespace Raw
variable {A : Hol G} {T : SectionData F} {o : Site n} {X : ℕ → Support n} {B : BudgetPoint}
  {w v κ paid : ℝ} {M : Raw F n} {R : Rep G n}

structure Format (M : Raw F n) (o : Site n) (X : ℕ → Support n) (R : Rep G n) : Prop where
  origin i : o ∈ X i
  regular i : R.p.Regular (X i) (M.bulk i)
  force : ForceFormat R.p R.activities o M.forced

def cost (M : Raw F n) (o : Site n) (X : ℕ → Support n) (B : BudgetPoint) (e : ℕ → ℝ) :=
  ∀ i, B.supBounds o (X i) (M.bulk i) (e i)

def rawMass (A : Hol G) (T : SectionData F) (o : Site n) (X : Support n) (B : BudgetPoint) (w c : ℝ) :=
  B.mass (joint T o X) (atomPrice A F w * c)

def rawMerge (A : Hol G) (T : SectionData F) (o : Site n) (X : Support n) (B : BudgetPoint) (w v c : ℝ) :=
  mergePrice B v (joint T o X) (atomPrice A F w * c)

def Income (M : Raw F n) (o : Site n) (X : ℕ → Support n) (A : Hol G) (T : SectionData F) (R : Rep G n) (w v κ paid : ℝ) :=
  ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a+(b+c) ≤ paid ∧
    (∃ e, M.cost o X R.p e ∧ SumBudget (fun i => rawMass A T o (X i) R.p w (e i)) a ∧
      SumBudget (fun i => rawMerge A T o (X i) R.p w v (e i)) (κ*c)) ∧ ForceCost R.p R.activities M.forced (κ*b)

def eval (M : Raw F n) (o : Site n) (X : ℕ → Support n) (T : SectionData F) (R : Rep G n) (U : Config G n) : ℂ :=
  (R.eval U : ℂ) * (primary T o R.p.threshold M.seed U + ∑' i, masked R.p.threshold (X i) (M.bulk i) U) +
    (Real.exp (R.exponent U) : ℂ) * ∑' b, gasMark R.p R.activities U b M.forced

def row (M : Raw F n) (o : Site n) (X : ℕ → Support n) (A : Hol G) (t : ℝ) (i : ℕ) := weighted A F o (X i) t (M.bulk i)

def build (M : Raw F n) (o : Site n) (X : ℕ → Support n) (A : Hol G) (T : SectionData F) (R : Rep G n)
    (S : Slots R.activities (fun i => joint T o (X i))) : Coefficient F n := {
  x := M.seed + ∑' i, M.row o X A R.p.threshold i
  support := fun i => joint T o (X i)
  regular := fun i => residual A T o (X i) R.p.threshold (M.bulk i)
  forced := M.forced + S.pack R.p.threshold (fun i => rebate A T o (X i) R.p.threshold (M.bulk i))
}

theorem summable_income (h : Income M o X A T R w v κ paid) (hw : 0 ≤ w) : ∃ e, M.cost o X R.p e ∧ Summable e := by
  obtain ⟨a,b,c,-,-,-,-,⟨e,h1,h2,-⟩,-⟩ := h
  exact ⟨e,h1,h2.2.1.of_nonneg_of_le (fun i => (h1 i).1) fun i => ((le_mul_of_one_le_left (h1 i).1 (atomPrice_ge_one A F hw)).trans (R.p.loMass _ _ (mul_nonneg (zero_le_one.trans (atomPrice_ge_one _ _ hw)) (h1 i).1)))⟩

theorem dominated_pieces (o : Site n) (h : Readable A T R.p n w) (hf : M.Format o X R) (hu : Income M o X A T R w v κ paid) :
    Summable (fun i => ‖M.row o X A R.p.threshold i‖) ∧ Dominated (fun i => rebate A T o (X i) R.p.threshold (M.bulk i)) := by
  obtain ⟨e,hE,he⟩ := summable_income hu h.nonneg
  exact ⟨(he.mul_left (readPrice A F)).of_nonneg_of_le (fun i => norm_nonneg _) (fun i => (norm_le_size F _).trans (weighted_bound A F o (hf.regular i) h.order h.power (hE i))),
    ⟨_,he.mul_left (atomPrice A F w), fun i => (charge_atom o h (hf.regular i) (hE i)).2⟩⟩

theorem build_format (S : Slots R.activities (fun i => joint T o (X i))) (ha : R.activities.ForcedFamily R.p) (h : Readable A T R.p n w)
    (hf : M.Format o X R) : (M.build o X A T R S).Format o A R := by
  have he (i) := convert_atom o h (hf.regular i)
  have hj (i) := (reads_null_iff ..).mp (he i).2.2.1
  have hF := hf.force.add (S.forceFormat ha (fun i => (he i).2.1) (fun i => (he i).2.2.2))
  exact ⟨fun i => (he i).1, fun i => (he i).2.1, fun i => (hj i).1,fun i => (hj i).2,hF.forcing, hF.carried,hF.invariant,hF.supported,hF.borel⟩

theorem build_remBound (S : Slots R.activities (fun i => joint T o (X i))) (ha : R.activities.KBound R.p v) (h : Readable A T R.p n w)
    (hf : M.Format o X R) (hu : Income M o X A T R w v κ paid) (hκ : 0 < κ) : (M.build o X A T R S).remBound o R κ paid := by
  obtain ⟨a,b,c,h1,h2,h3,h4,⟨e,h5,h6,h7⟩,h8⟩ := hu
  have hi i := charge_atom o h (hf.regular i) (h5 i)
  have hF := h8.add (S.forceCost ha h7 (fun i => mul_nonneg (zero_le_one.trans (atomPrice_ge_one A F h.nonneg)) (h5 i).1) (fun i => (hi i).2))
  exact ⟨a,b+c,h1,add_nonneg h2 h3,h4,hκ,⟨_,h6,fun i => (hi i).1⟩, (by rw [mul_add]; exact hF)⟩

theorem build_density (S : Slots R.activities (fun i => joint T o (X i))) {σ C Λ δ : ℝ} (ha : R.Lawful σ C Λ δ v) (h : Readable A T R.p n w)
    (hf : M.Format o X R) (hu : Income M o X A T R w v κ paid) (hκ : 0 < κ) : (M.build o X A T R S).density o T R = M.eval o X T R := by
  let t := R.p.threshold
  let p (i : ℕ) := rebate A T o (X i) t (M.bulk i)
  let L := M.build o X A T R S
  obtain ⟨a,b,c,h1,h2,h3,h4,h5,h6⟩ := hu
  obtain ⟨hr,hp⟩ := dominated_pieces o h hf (v:=v) ⟨a,b,c,h1,h2,h3,h4,h5,h6⟩
  have hR := build_remBound S ha.labels.boundK h hf (paid:=paid) ⟨a,b,c,h1,h2,h3,h4,h5,h6⟩ hκ
  funext U
  let q := ∑' i, p i U
  let P : F.Coeff →L[ℂ] ℂ := ((LinearMap.proj (R:=ℂ) (φ:=fun _ : Config G n => ℂ) U) ∘ₗ primary T o t).toContinuousLinearMap
  have he : primary T o t M.seed U + ∑' i, masked t (X i) (M.bulk i) U = L.exponentialEntry o T R U + q := by
    have hi (i) : masked t (X i) (M.bulk i) U = P (M.row o X A t i) + L.maskedTerm R i U + p i U := by
      change _ = primary T o t (weighted A F o (X i) t (M.bulk i)) U + masked t (joint T o (X i)) (residual A T o (X i) t (M.bulk i)) U + (_ - primary T o t (weighted A F o (X i) t (M.bulk i)) U - masked t _ _ U); abel
    change P M.seed + _ = (P L.x + ∑' i, L.maskedTerm R i U) + _
    have hx := Coefficient.regular_series hR |>.summable U
    simp_rw [hi]; rw [show L.x=M.seed + ∑' i, M.row o X A t i from rfl,map_add, P.map_tsum hr.of_norm, ((P.summable hr.of_norm).add hx).tsum_add (hp.summable U), (P.summable hr.of_norm).tsum_add hx]; abel
  have hg := S.recover R.p U p (fun i => (convert_atom o h (hf.regular i)).2.2.2) ha.labels (hp.absolute U)
  have hMark : (∑' b', L.marked R b' U) = (∑' b', gasMark R.p R.activities U b' M.forced) + q*(R.activities.gas R.p U:ℂ) := by
    have hx (s : Finset ℕ) : L.marked R s U = gasMark R.p R.activities U s L.forced := (gasMark_eq ..).symm
    have hs := dominated_gasMark h6 ha.labels.boundK |>.summable U
    simp_rw [hx,show L.forced = M.forced + S.pack t p from rfl,map_add]; exact (hs.hasSum.add hg).tsum_eq
  change L.density o T R U = _
  rw [Coefficient.density, hMark, eval, he, Rep.eval,Complex.ofReal_mul]; ring

theorem build_samples (S : Slots R.activities (fun i => joint T o (X i))) (h : Readable A T R.p n w) (hf : M.Format o X R)
    (hs : Summable (M.row o X A R.p.threshold)) (i : Probe G d) :
    runProbe F i (M.build o X A T R S).x = runProbe F i M.seed + ∑' j, sample A o (X j) R.p.threshold (M.bulk j) i := by
  rw [build,map_add,(runProbe F i).map_tsum hs]; congr 1; exact tsum_congr fun j => (sample_eq F A o _ (hf.regular j) h.order i).symm

theorem build_star (S : Slots R.activities (fun i => joint T o (X i))) {M' : Raw F n}
    (h : Readable A T R.p n w) (hf : M.Format o X R) (hx : M'.seed=star M.seed) (e : Equiv.Perm ℕ) (he : ∀ i,X (e i) = X i)
    (hg : ∀ i, M'.bulk (e i) = star (M.bulk i)) : (M'.build o X A T R S).x = star (M.build o X A T R S).x := by
  simp only [build,hx,star_add,tsum_star]; rw [← e.tsum_eq]; exact congr_arg _ (tsum_congr fun i => by rw [row, he, hg,weighted_star A F o _ (hf.regular i) h.order,row])

theorem build_pull (S : Slots R.activities (fun i => joint T o (X i))) {R' : Rep G n} {X' : ℕ → Support n} {M' : Raw F n} (s : Signed) (b : Site n)
    (S' : Slots R'.activities (fun i => joint T (turnSites s b o) (X' i))) (h : Readable A T R.p n w) (hf : M.Format o X R) (hm : R'.p.threshold = R.p.threshold) (hn : 2 ≤ n.val) (hs : Summable (M.row o X A R.p.threshold))
    (hx : M'.seed=F.act s.ortho M.seed) (e : Equiv.Perm ℕ) (he : ∀ i,X' (e i) = (X i).image (turnSites s b)) (hg : ∀ i, M'.bulk (e i) = M.bulk i ∘ pull s b) :
    (M'.build (turnSites s b o) X' A T R' S').x = F.act s.ortho (M.build o X A T R S).x := by
  simp only [build,hx,map_add,hm]; rw [← e.tsum_eq]
  rw [show F.act s.ortho (∑' _, _) = _ from (F.act s.ortho).toContinuousLinearMap.map_tsum hs]; congr 1
  exact tsum_congr fun i => by
    simp only [row,he,hg]; exact weighted_pull A F o b s R.p.threshold (hf.regular i) h.order hn

section Linear
variable {K : F.Coeff → Raw F n}

structure Linear (K : F.Coeff → Raw F n) : Prop where
  seed : IsLinearMap ℂ (fun v => (K v).seed)
  bulk i : IsLinearMap ℂ (fun v => (K v).bulk i)
  forced : IsLinearMap ℂ (fun v => (K v).forced)

private theorem linear_tsum (u : F.Coeff → F.Coeff) (hu : IsLinearMap ℂ u) (r : F.Coeff → ℕ → F.Coeff)
    (hr : ∀ i, IsLinearMap ℂ (fun v => r v i)) (hs : ∀ v, Summable (r v)) : IsLinearMap ℂ (fun v => u v + ∑' i, r v i) := by
  constructor
  · intro x y; simp_rw [(hr _).map_add x y,hu.map_add x y,(hs x).tsum_add (hs y),add_add_add_comm]
  intro z x; simp_rw [(hr _).map_smul z x,hu.map_smul z x,(hs x).tsum_const_smul,smul_add]

private theorem linear_forced (f : F.Coeff → ℕ → Config G n → ℂ) (q : F.Coeff → ℕ → Config G n → ℂ)
    (p : (ℕ → Config G n → ℂ) →ₗ[ℂ] ℕ → Config G n → ℂ) (hf : IsLinearMap ℂ f) (hq : IsLinearMap ℂ q) : IsLinearMap ℂ (fun v => f v + p (q v)) :=
  ((IsLinearMap.mk' _ hf) + p.comp (IsLinearMap.mk' _ hq)).isLinear

private theorem rows_linear (h : Readable A T R.p n w) (hl : Linear K) (hf : ∀ v, (K v).Format o X R) (i : ℕ) : IsLinearMap ℂ (fun v => (K v).row o X A R.p.threshold i) := by
  let t := R.p.threshold
  let r v := (K v).row o X A t
  have hr (i) : IsLinearMap ℂ (fun v => r v i) := by
    constructor
    · intro x y; dsimp only [r,row,weighted]; rw [(hl.bulk i).map_add x y,project_add A o ((hf x).regular _) ((hf y).regular _) h.order,map_add,map_add]
    intro z x; dsimp only [r,row,weighted]; rw [(hl.bulk i).map_smul z x,project_smul A o _ ((hf x).regular _) h.order,map_smul,map_smul]
  exact hr i

private theorem residual_linear (h : Readable A T R.p n w) (hl : Linear K) (hf : ∀ v, (K v).Format o X R) : IsLinearMap ℂ (fun v i => residual A T o (X i) R.p.threshold ((K v).bulk i)) := by
  let t := R.p.threshold
  let r v := (K v).row o X A t
  have hr (i) : IsLinearMap ℂ (fun v => r v i) := rows_linear h hl hf (o:=o) i
  let g (x : F.Coeff) (i : ℕ) := residual A T o (X i) t ((K x).bulk i)
  let q (x : F.Coeff) (i : ℕ) := rebate A T o (X i) t ((K x).bulk i)
  have hg : IsLinearMap ℂ g := by
    constructor
    · intro x y; funext i; change (K (x+y)).bulk i - presented T o t (r (x+y) i) = g x i + g y i
      rw [(hl.bulk i).map_add x y,(hr i).map_add x y,map_add]; exact add_sub_add_comm ..
    intro z x; funext i; change (K (z • x)).bulk i - presented T o t (r (z • x) i) = z • g x i
    rw [(hl.bulk i).map_smul z x,(hr i).map_smul z x,map_smul, ← smul_sub]; rfl
  exact hg

private theorem rebate_linear (h : Readable A T R.p n w) (hl : Linear K) (hf : ∀ v, (K v).Format o X R) : IsLinearMap ℂ (fun v i => rebate A T o (X i) R.p.threshold ((K v).bulk i)) := by
  let t := R.p.threshold
  let r v := (K v).row o X A t
  have hr (i) : IsLinearMap ℂ (fun v => r v i) := rows_linear h hl hf (o:=o) i
  let g (x : F.Coeff) (i : ℕ) := residual A T o (X i) t ((K x).bulk i)
  let q (x : F.Coeff) (i : ℕ) := rebate A T o (X i) t ((K x).bulk i)
  have hg := residual_linear h hl hf (o:=o)
  have hq : IsLinearMap ℂ q := by
    have he (v i) : q v i = maskLinear t (X i) ((K v).bulk i) - primary T o t (r v i) - maskLinear t (joint T o (X i)) (g v i) := rfl
    constructor
    · intro x y; funext i; change IsLinearMap ℂ g at hg; simp only [Pi.add_apply,he,(hl.bulk i).map_add x y,(hr i).map_add x y,hg.map_add x y,map_add]; abel
    intro z x; funext i; change IsLinearMap ℂ g at hg; simp only [Pi.smul_apply,he,(hl.bulk i).map_smul z x,(hr i).map_smul z x,hg.map_smul z x,map_smul,smul_sub]
  exact hq

/-- The common-support convention is enforced in the TYPES. -/
theorem build_linear (S : Slots R.activities (fun i => joint T o (X i))) (h : Readable A T R.p n w) (hl : Linear K) (hf : ∀ v, (K v).Format o X R)
    (hs : ∀ v, Summable ((K v).row o X A R.p.threshold)) :
    let P := fun v => (K v).build o X A T R S
    IsLinearMap ℂ (fun v => (P v).x) ∧ IsLinearMap ℂ (fun v => (P v).regular) ∧ IsLinearMap ℂ (fun v => (P v).forced) ∧ ∀ v, (P v).support=(P 0).support := by
  let t := R.p.threshold
  let r v := (K v).row o X A t
  have hr (i) : IsLinearMap ℂ (fun v => r v i) := rows_linear h hl hf (o:=o) i
  let g (x : F.Coeff) (i : ℕ) := residual A T o (X i) t ((K x).bulk i)
  let q (x : F.Coeff) (i : ℕ) := rebate A T o (X i) t ((K x).bulk i)
  have hg := residual_linear h hl hf (o:=o)
  have hq := rebate_linear h hl hf (o:=o)
  have same (v) : ((K v).build o X A T R S).support = fun i => joint T o (X i) := rfl
  exact ⟨linear_tsum _ hl.seed r hr hs, hg, linear_forced _ q (S.packLinear t) hl.forced hq, fun v => (same v).trans (same 0).symm⟩
end Linear
end Raw
end YM.Push.Local
