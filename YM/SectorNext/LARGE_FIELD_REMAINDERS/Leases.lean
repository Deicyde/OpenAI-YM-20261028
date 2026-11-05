import YM.Next.BOUNDARY.Stage
import YM.Next.PHASE.Assembly
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Bills
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Columns


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Volume-explicit bills after the grant

These are the analytic estimates under the cost invoices for the actual T and
true representation. No comparison of input vacuum energy at different β. Never
divide by an unknown partition function. Normalize the table used for bounds,
NOT the cut sector charges, making possession add up to ≤1 for summability. Its
κ currency can still pay much more under named gates. All-units bounds in next
module. Fixed-width invoices, don't assume all scheduling (use pre/post calls).
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector Scales Metric Oriented Presented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ENNReal

variable {G : Gauge} {c f : Side} {S : StepData c f} {x W γ : ℝ} (d : Allocation G S x W)
  (F : Forest S.ratio) (V : Config G c)

def rent (A : Stores S) (m : Mode) (C γ D : ℝ) : ℝ :=
  let s := m.size G S.patch.L x
  seats d m F V A C (γ/2) s / (D*s^dim G)^nt F

lemma rents (G : Gauge) (C γ : ℝ) (m : Mode) (hC : 0<C) (hγ : 0<γ) : ∃ D : ℝ, 1 ≤ D ∧
    ∀ {c f : Side} (S : StepData c f) (x W : ℝ) (d : Allocation G S x W)
    (F : Forest S.ratio) (V : Config G c), S.patch.Branches S.kernel G → 1<y G S.patch.L x →
    (∀ A,0≤rent d F V A m C γ D) ∧ (∑ A, rent d F V A m C γ D) ≤ 1 := by
  obtain ⟨D,hD,H⟩ := seats_price m G C (γ/2) hC (half_pos hγ)
  have hd : 0<D := by linarith
  refine ⟨D,hD,fun {c f} S x W d F V hB hx => ?_⟩
  let s := m.size G S.patch.L x
  have hs : 0<s := (g01 G S.patch.L hx).1.trans_le (s_le G S.patch.L hx m)
  have he : 0 < (D*s^dim G)^nt F := by positivity
  refine ⟨fun i => div_nonneg (seats_nonneg _ _ _ _ _ _ _ _ hs.le) he.le,?_⟩
  change (∑ A, _ / (D*s^dim G)^nt F) ≤ 1; rw [← Finset.sum_div, div_le_iff₀ he,one_mul]; exact H _ _ _ _ _ _ _ _ hB _ hs

def nf (n : Side) : ℕ := Fintype.card (Site n)

lemma nf_le (S : StepData c f) : nf c ≤ nf f := by
  unfold nf; simp only [site_card,S.sizes]
  have h := S.patch.L.property; change 0 < S.patch.L.val at h
  gcongr; simpa using Nat.mul_le_mul_left c.val h

/-- The bulk-volume bill; for `shielded` this can still cost (fixed-L
constant)^volume after extracting β^-1/2 link scales. Separate symbols
so iteration caller sees and can challenge those affordability needs. -/
def shore (S : StepData c f) (G : Gauge) (F : Forest S.ratio) (m : Mode) (β x D : ℝ) :=
  prefactor S G β * Real.exp (2*(nf f:ℝ)) * (D*m.size G S.patch.L x^dim G)^nt F

def direct (T : Tube G S) (x β : ℝ) (V : Config G c) (m : Mode) := match m with
  | .clipped => (1:ℝ)
  | .shielded => shield T β x V

def allCut (T : Tube G S) (x β : ℝ) (V : Config G c) (m : Mode) := match m with
  | .clipped => (1:ℝ)
  | .shielded => sieve T β x V

/-- Kept-rows estimates for the actual factors. First part doesn't demand representation,
just multiplier measured on same configuration. Second part for **full** input, all
masks and countable labels, whenever Lawful/compatible (v need not be part of horizon fit).
Mode `shielded` estimates leftOver; be careful NOT to multiply a second sieve!
Estimated with incoming costs σ>0 B>0 and post caps. -/
structure PaidHere (T : Tube G S) (x W κ σ B C γ H : ℝ) (n : ℕ) (D : Mode → ℝ) : Prop where
  single
    (A : Stores S) (F : Forest S.ratio) (V : Config G c) (d : Allocation G S x W) (m : Mode)
    (β K : ℝ) (g : S.Choices → F.Slice G → ℝ) (hy : β ∈ Set.Icc (y G S.patch.L x/2) (2*y G S.patch.L x)) (hk : 0≤K)
    (hgi : ∀ k, Integrable (g k) (F.order G))
    (h : ∀ k, ∀ᵐ a ∂(F.order G), d.bill A k (F.drape a) V ≠0 → Alive S (F.drape a) k →
      ‖g k a‖ ≤ K * Real.exp (coin G S.patch.L H n x * (A.shares:ℝ))) :
    earn S G x κ β A.shares * (direct T x β V m *
      d.column A F V (remainder F A T β x V (fun k a => ‖g k a‖))) ≤
        K * shore S G F m β x (D m) * Real.exp (-(seed G S.patch.L x κ β A.shares)/2) *
          outputReserve m false T x β V * rent d F V A m C γ (D m)
  full (R : Rep G f) (Λ δ w : ℝ) (hR : R.Lawful σ B Λ δ w) (hΛ : Λ ≤ 2*p G S.patch.L x)
    (hw : w∈Set.Icc (0:ℝ) 1) (hd : δ ≤ 1)
    (hu : R.p.threshold = fiery G x S.patch.L)
    (hy : R.beta ∈ Set.Icc (y G S.patch.L x/2) (2*y G S.patch.L x))
    (F : Forest S.ratio) (d : Allocation G S x W) (A : Stores S) (V : Config G c) (m : Mode) :
    Real.exp (coin G S.patch.L H n x * (A.shares:ℝ)) * earn S G x κ R.beta A.shares *
      (allCut T x R.beta V m * restBill d F V A R T) ≤
        Real.exp R.scalar * shore S G F m R.beta x (D m) * Real.exp (-(seed G S.patch.L x κ R.beta A.shares)/2) *
          outputReserve m true T x R.beta V * rent d F V A m C γ (D m)

-- assist arithmetic elaboration
private lemma collect {p s ex sustain f out kh extra vacuum earn base : ℝ} (hp : 0 ≤ p) (hs : 0 ≤ s)
    (he : 0 ≤ ex) (hsu : 0≤sustain) (hf : 0 < f) (hh : 0 ≤ out)
    (hA : ex*sustain ≤ vacuum*Real.exp base)
    (hB : Real.exp extra * kh ≤ Real.exp (earn/2)) :
    Real.exp extra * (p * Real.exp (-earn)) * (ex*sustain * out * kh * s) ≤
      vacuum*(p * Real.exp base * f) * Real.exp (-earn/2) * out * (s/f) := by
  have hw : Real.exp (-earn) * Real.exp (earn/2) = Real.exp (-earn/2) := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ = (p*s*out*Real.exp (-earn))*((Real.exp extra*kh)*(ex*sustain)) := by ring
    _ ≤ (p*s*out*Real.exp (-earn))*(Real.exp (earn/2)*(vacuum*Real.exp base)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_trans (mul_le_mul_of_nonneg_right hB (by positivity))
        (mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le)
    _ = _ := by rw [show -earn/2=-(earn)/2 by ring, ← hw]; field_simp
-- collect needs sustain≥0

set_option maxHeartbeats 1200000 in
/-- POST-L authority (incorporate κ and then delay; don't spend on other schedules
retrospectively). Constants C,γ,D also for subvolume-rent normalization. -/
lemma lease (P : Teller G) (L : Side) (W : ℝ) (hW : 0 < W) :
    ∃ (C γ : ℝ) (D : Mode → ℝ), 0 < C ∧ 0 < γ ∧ (∀ m, 1≤D m) ∧
      (∀ (m : Mode) {c f : Side} (S : StepData c f) (x W : ℝ) (d : Allocation G S x W)
      (F : Forest S.ratio) (V : Config G c), S.patch.Branches S.kernel G → 1<y G S.patch.L x →
      (∀ A,0≤rent d F V A m C γ (D m)) ∧ (∑ A, rent d F V A m C γ (D m)) ≤ 1) ∧
      ∀ (κ σ B H : ℝ) (n : ℕ), 0 < κ → 0 < σ → 0 < B → 0 ≤ H → ∀ᶠ x : ℝ in atTop,
      1<y G L x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L = L →
      100*(1+radiusB x) ≤ c.val → P.Funds S T → PaidHere T x W κ σ B C γ H n D := by
  obtain ⟨C,γ,l,hC,hγ,hl,hJ⟩ := joint_post P L W hW
  choose D hD h using fun m => rents G C γ m hC hγ
  refine ⟨C,γ,D,hC,hγ,hD,h,fun κ σ B k n hk hs hB h0 => ?_⟩
  have hv : Tendsto (fun x => 2*y G L x*l x) atTop (𝓝 0) := by
    have hh := (hl 0).const_mul 2; rw [mul_zero] at hh
    exact hh.congr fun x => by simp; ring
  filter_upwards [hJ, hv.eventually (ge_mem_nhds zero_lt_one),
    bulk_price G L σ B (error:=l) (by simpa using hl 0) hs hB,
    hole_price G L κ (k+4) n hk (by linarith), (year G L).eventually_gt_atTop 1] with x hT he hh hX hY
  obtain ⟨hy,ht⟩ := hT
  refine ⟨hY,fun c f S T hL hR hg => ?_⟩
  obtain hj := ht c f S T hL hR hg
  rw [← hL] at he hh hY hX -- hy no L
  let L := S.patch.L
  let z := y G L x
  let a := coin G L k n x
  have hz : 1 < z := hY
  have hf (m : Mode) : 0<m.size G L x := (g01 G L hY).1.trans_le (s_le G L hY m)
  have hp (d : Allocation G S x W) (F : Forest S.ratio) (A : Stores S) V : ∀ (a : F.Slice G) k, d.bill A k (F.drape a) V ≠0 →
      Alive S (F.drape a) k → Joint T A (F.drape a) k V x C γ (l x) :=
    fun a k ha hb => hj _ _ _ _ _ (fun i hi => F.on_tree a ⟨i,hi⟩) (d.actual _ _ _ _ ha) hb
  have hw (F : Forest S.ratio) (A : Stores S) (m : Mode) (β w : ℝ) (hb : z/2 ≤ β) (hv : w ≤ 1) :
      Real.exp (a*A.shares+w*4*A.shares) * hole F A G x (m.size G L x) ≤ Real.exp (seed G L x κ β A.shares/2) := by
    apply le_trans ?_ (hX S rfl A F m β hb)
    apply mul_le_mul_of_nonneg_right _ (hole_nonneg _ _ _ _ (hf _).le)
    have hi : 1 ≤ b x^n := one_le_pow₀ (size x)
    have Hj : 1 ≤ 1+Real.log (y G L x) := le_add_of_nonneg_right (Real.log_nonneg hz.le)
    have ht : k*b x^n*(1+Real.log (y G L x)) + w*4 ≤ (k+4)*b x^n*(1+Real.log (y G L x)) := by
      nlinarith only [one_le_mul_of_one_le_of_one_le hi Hj,hv]
    exact Real.exp_monotone (by
      unfold a coin
      linarith only [mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg (α:=ℝ) A.shares)])
  have hbulk (β : ℝ) (hβ : β∈Set.Icc (z/2) (2*z)) : 0 ≤ β ∧ Real.exp (β*l x*(nf c:ℝ)) ≤ Real.exp (2*(nf f:ℝ)) := by
    have hhh := hβ.1
    refine ⟨by linarith,?_⟩
    have hr : β*l x ≤ 1 := (mul_le_mul_of_nonneg_right hβ.2 hy).trans he
    have hr' : (nf c:ℝ) ≤ (nf f:ℝ) := by exact_mod_cast nf_le S
    apply Real.exp_monotone
    have hg := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg (α:=ℝ) (nf c)); linarith
  have hD0 (m : Mode) : 0 < D m := zero_lt_one.trans_le (hD m)
  constructor
  · intro A F V d m β K g hz1 hK hgi hq
    let t := m.size G L x
    let P := K * Real.exp (a*A.shares)
    have hQ := outgoing_column d F V A m hg hz1.1 (zero_lt_one.trans hY) hγ g hgi hq
      (show 0 ≤ P by unfold P; positivity) (hp d F A V)
    let u := prefactor S G β; let e := seed G L x κ β A.shares
    let s := seats d m F V A C (γ/2) t
    let out := outputReserve m false T x β V
    let sustain := Real.exp (β*l x*Fintype.card (Site c))
    let M := (D m*t^dim G)^nt F
    let L0 := hole F A G x t
    have hf0 : 0<t := hf m
    have hM : 0<M := by unfold M; have := hD0 m; positivity
    have hu : 0<u := prefactor_pos _
    have hB : 0≤earn S G x κ β A.shares := (earn_pos ..).le
    apply (mul_le_mul_of_nonneg_left hQ hB).trans
    have hh := hw F A m β 0 hz1.1 (by norm_num)
    rw [zero_mul,zero_mul,add_zero] at hh
    have hm := collect (f:=M) (s:=s) (out:=out) hu.le (seats_nonneg d m F V A _ _ _ hf0.le)
      hK (Real.exp_pos _).le hM (Real.exp_pos _).le
      (mul_le_mul_of_nonneg_left (hbulk β hz1).2 hK) hh
    change u*Real.exp _ * (P*sustain*out*L0*s) ≤ K*(u*Real.exp _*M)*Real.exp (-e/2)*out*(s/M)
    rw [show Real.exp (-β*(κ*(fiery G x S.patch.L)^2*A.shares))=Real.exp (-e) by unfold e seed L; ring_nf]
    apply le_trans ?_ hm
    unfold P sustain L0 t e nf; ring_nf; rfl
  intro R Λ δ w h0 hΛ hW hd hu hz1 F d A V m
  let β := R.beta
  let t := m.size G L x
  let u := prefactor S G β
  let e := seed G L x κ β A.shares
  let s := seats d m F V A C (γ/2) t
  let out := outputReserve m true T x β V
  let sustain := Real.exp (β*l x*Fintype.card (Site c))
  let M := (D m*t^dim G)^nt F
  let L0 := hole F A G x t
  let E := Real.exp (R.scalar + air R x σ B Λ δ * (nf f:ℝ))
  let v := w*4*A.shares
  have hb := (hbulk β hz1).1
  have hN (i : S.Choices) (x' : F.Slice G) (hx' : d.bill A i (F.drape x') V ≠0) :
      ‖exposed R (till x) (F.drape x')‖ ≤ E * Real.exp v := by
    obtain ⟨b,hb',hB'⟩ := occurrence_budget A R.activities R.p d hW.1 h0.labels hu
    exact (exposed_absolute A d R hW.1 hb' hB' h0 hb _ V _ hx').2
  have hE : 0≤E * Real.exp v := by unfold E; positivity
  have ht := rest_estimate d F V A m h0 hg hz1.1 (zero_lt_one.trans hY) hγ (fun i =>
    Eventually.of_forall fun h hh _ => hN _ _ hh) hE (hp d F A V)
  apply (mul_le_mul_of_nonneg_left ht (mul_nonneg (Real.exp_pos _).le (earn_pos ..).le)).trans
  have hS : E*sustain ≤ Real.exp R.scalar * Real.exp (2*(nf f:ℝ)) := by
    unfold E sustain; rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_monotone
    have hi := mul_le_mul_of_nonneg_right (hh f R δ Λ hd hΛ hu hz1 hy) (Nat.cast_nonneg (α:=ℝ) (nf f))
    have he : (nf c:ℝ) ≤ (nf f:ℝ) := by exact_mod_cast nf_le S
    have hv := mul_le_mul_of_nonneg_left he (mul_nonneg hb hy)
    unfold nf at *; linarith only [hi,hv]
  have hl := prefactor_pos (S:=S) (G:=G) β
  have hf0 : 0<t := hf m
  have hM : 0<M := by unfold M; have := hD0 m; positivity
  have hm := collect (f:=M) (s:=s) (out:=out) hl.le (seats_nonneg d m F V A _ _ _ hf0.le) (Real.exp_pos _).le (Real.exp_pos _).le hM (Real.exp_pos _).le hS (hw F A m β w hz1.1 hW.2)
  change Real.exp (a*A.shares) * (u * Real.exp _) * (E*Real.exp v*sustain*out*L0*s) ≤ Real.exp R.scalar*(u*Real.exp _*M)*Real.exp (-e/2)*out*(s/M)
  rw [show Real.exp (-R.beta*(κ*(fiery G x S.patch.L)^2*A.shares))=Real.exp (-e) by unfold e seed L β; ring_nf]
  apply le_trans ?_ hm
  rw [Real.exp_add]; unfold v u e E sustain L0 t nf; ring_nf; rfl
end YM.SectorNext.Remainder
