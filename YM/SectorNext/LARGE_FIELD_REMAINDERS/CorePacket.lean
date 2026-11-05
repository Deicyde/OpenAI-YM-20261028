import YM.SectorNext.LARGE_FIELD_REMAINDERS.Annulus
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Bills


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Core multiplier exponent estimate (E H_{D_c} contribution to pmult)

Doesn't assume Cut/FG reconstruction inputs. Keep actual assessed works
and actual L,D all the way through. Include enough threshold quantifiers
to combine this service both at preL & at `Hardware` stations. Here include
post-$L$ allowance usable for all the ancillary losses $O_L((1+B)^4 |\\Omega|
(1+\\log 1/g))$ like counting frozen deficits, bounded local log entries if
established, etc. (does not assert their bounds, actual change, guards,
locality/affordability, Borel outputs).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Scales Metric Oriented Presented Exterior Bloch Work.F03
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Example incidence sufficing even before having forest-sector constructors:
assign O from all-record A with other seeds physically separated from owner
halo. Used only for Plot prerequisites, can strengthen at geometry prices later. -/
structure Owns (O A : Stores S) (x : ℝ) : Prop where
  fine : O.costs ⊆ A.costs
  noise : O.aisles ⊆ A.aisles
  flags : O.flags ⊆ A.flags
  detachF (b : Cell f) : b∈A.costs → b∉O.costs → Disjoint (startPos S b) (O.dome (5*radiusB x))
  detachB (i : Bond c) : i ∈ A.aisles → i∉ O.aisles → Disjoint (pinPos i) (O.dome (5*radiusB x))
  detach (i : Site c) : i∈ A.flags → i ∉ O.flags → i ∉ O.dome (5*radiusB x)



lemma localOwner {O A : Stores S} {D : ℕ} {x W : ℝ} {k : S.Choices} {U : Config G f} {V : Config G c}
    (h : Owns O A x) (hh : Wide O A D x W U k V) : O.Plot U k V x W := by
  have he : O.dome (5*radiusB x) ⊆ O.dome ((D+5)*radiusB x) := Corona.halo_mono (by gcongr; omega) (fun _ h => h)
  constructor
  · intro p hp
    obtain ⟨h1,h2⟩ := hh.consumes p (fun ht => hp (Disjoint.mono_left he ht))
    exact ⟨fun hv => h1 (h.fine hv),fun he' => h2 (fun ha => hp ((h.detachF p ha he').symm))⟩
  · intro p hp
    obtain ⟨h1,h2⟩ := hh.drive p (fun ht => hp (Disjoint.mono_left he ht))
    exact ⟨fun hv => h1 (h.noise hv),fun he' => h2 (fun ha => hp ((h.detachB p ha he').symm))⟩
  · intro i hi
    rw [← hh.precise i (he hi)]
    exact ⟨fun hx => h.flags hx,fun hv => Classical.not_not.mp fun hx => h.detach i hv hx hi⟩
  exact fun i hi => hh.list i (he hi)

def boost (O : Stores S) (Q J : Window S) (T : Tube G S)
    (x : ℝ) (k : S.Choices) (U : Config G f) (V : Config G c) (a : Directions G f) :=
    O.assessed T x U (S.prediction U k) V+(Q.work T x U k V-J.extract T x k V a)

def Ledger (P : Teller G) (L : Side) (W κ K H : ℝ) (n D : ℕ)
    (x : ℝ) :=
    1<y G L x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → 100*(1+radiusB x)≤c.val →
     P.Funds S T → PointCharge T x W κ →
     ∀ (O A : Stores S) (Q J : Window S) (β : ℝ),
       β∈Set.Icc (y G L x/2) (2*y G L x) → Owns O A x → J.selects Q → Q.annulus O A D (radiusB x) →
       ∀ (F : Forest S.ratio) (k : S.Choices) (U : Config G f) (V : Config G c) (a : Directions G f),
         Wide O A D x W U k V → SliceSet S F U → J.charts U V a K x →
         J.written T x k V a ∧
           κ/4*(p G L x)^2*O.shares + coin G L H n x * O.shares ≤ β*boost O Q J T x k U V a

lemma authorize (P : Teller G) (L : Side) (W κ K H : ℝ) (n D : ℕ) (hW : 0<W) (hk : 0<κ) :
    ∀ᶠ x : ℝ in atTop, Ledger P L W κ K H n D x := by
  obtain ⟨C,hC,e,he,h,hp⟩ := annulus_pay P L W K hW D
  have hf := h 0; simp only [pow_zero,one_mul] at hf
  have hs := (inactive_price G L n (a:=2) (by norm_num)).const_mul H
  simp only [Real.rpow_two,mul_zero] at hs
  filter_upwards [hp,he,(year G L).eventually_gt_atTop 1, hf.eventually (ge_mem_nhds (show 0<κ/16 by positivity)),
    hs.eventually (ge_mem_nhds (show 0<κ/8 by positivity)), (peak G L).eventually_ge_atTop 1] with x hA he hy ha hx ht
  let v := p G L x
  have hh : H*((b x)^n*(1+Real.log (y G L x))/v^2) ≤ κ/8 := hx
  have hu : 1 ≤ v^2 := one_le_pow₀ ht
  rw [← mul_div_assoc, div_le_iff₀ (zero_lt_one.trans_le hu),← mul_assoc] at hh
  refine ⟨hy,fun c f S T hl hh' hT hF O A Q J β hb ho hS hQ F k U V a hM hu' hJ => ?_⟩
  obtain ⟨g,-,h⟩ := hA S T hl hh' hT O A F U k V hu' hM
  obtain ⟨hw,hA⟩ := (h Q J hS hQ).2.2.2 a hJ
  refine ⟨hw,?_⟩
  have hg := hF F O U k V hu' (localOwner ho hM)
  let b : ℝ := O.shares
  have h0 : 0 ≤ b := Nat.cast_nonneg _
  have hB := zero_lt_one.trans hy
  have hβ : 0 ≤ β := le_trans (by positivity) hb.1
  obtain hz := earned G L hB hk.le hb.1 (m:=O.shares)
  unfold seed at hz
  rw [hl] at hg
  have he' := mul_le_mul_of_nonneg_right hb.2 he
  change y G L x*e x ≤ _ at ha
  change _*v^2*_ + _ * b ≤ β*boost O Q J T x k U V a
  unfold coin boost
  let Z := y G L x
  have hc : β*e x ≤ κ/8 := by linarith only [he',ha]
  change _*v^2*_ ≤ _ at hz
  have hh := mul_le_mul_of_nonneg_right hh h0
  have hv := mul_le_mul_of_nonneg_right (hc.trans (show κ/8 ≤ κ/8*v^2 from le_mul_of_one_le_right (by positivity) hu)) h0
  have H := mul_le_mul_of_nonneg_left hA hβ
  unfold b at *
  linarith only [H,hv,hh,hz,mul_le_mul_of_nonneg_left hg hβ]

variable (U : Config G f) (V : Config G c) (O : Stores S) (Q J : Signed → Window S)
variable (T : Tube G S) (x : ℝ) (k : S.Choices) (a : Signed → Directions G f)
def credits (s : Signed) := boost (turnStore s O) (Q s) (J s) T x (choice s k) (pull s 0 U) (pull s 0 V) (a s)

def vital (β x : ℝ) (U : Config G f) (V : Config G c) (O : Stores S) (Q J : Signed → Window S)
    (T : Tube G S) (k : S.Choices) (a : Signed → Directions G f) := Real.exp (-β * averaged (credits U V O Q J T x k a))

def Ensures (W K : ℝ) (D : ℕ) (F : Forest S.ratio) (A : Stores S) (s : Signed) :=
    let X := pull s 0 U
    let Y := pull s 0 V
    let O0 := turnStore s O
    let A0 := turnStore s A
    let t := choice s k
    Owns O0 A0 x ∧ Wide O0 A0 D x W X t Y ∧ (J s).selects (Q s) ∧ (Q s).annulus O0 A0 D (radiusB x) ∧
     (J s).charts X Y (a s) K x

variable {x T} {P : Teller G}

lemma used (F : Forest S.ratio) (A : Stores S)
    {L : Side} (hl : S.patch.L=L) (hs : 100*(1+radiusB x)≤c.val) (hT : P.Funds S T)
    (β K H W κ : ℝ) (D n : ℕ) (ha : PointCharge T x W κ)
    (h : Ledger P L W κ K H n D x) (he : β∈Set.Icc (y G L x/2) (2*y G L x))
    (hy : SliceSet S F U) (hh : ∀ s,Ensures U V O Q J x k a W K D F A s) :
    (∀ s, (J s).written T x (choice s k) (pull s 0 V) (a s)) ∧
    vital β x U V O Q J T k a ≤ Real.exp (-κ/4*(p G L x)^2*O.shares-coin G L H n x*O.shares) := by
  have hv s := hh s
  have hx s := h.2 c f S T hl hs hT ha (turnStore s O) (turnStore s A) _ _ _ he (hv s).1 (hv s).2.2.1
    (hv s).2.2.2.1 (turnForest s F) _ _ _ _ (hv s).2.1 (turn_sliced s F U hy) (hv s).2.2.2.2
  refine ⟨fun s => (hx s).1, Real.exp_monotone ?_⟩
  let b := κ/4*(p G L x)^2*O.shares+coin G L H n x*O.shares
  suffices he : b ≤ β * averaged (credits U V O Q J T x k a) by unfold b at he; linarith only [he]
  have hi : ∀ s, b ≤ β * credits U V O Q J T x k a s := fun s => by have he := (hx s).2; rw [same_price] at he; exact he
  calc
    _ = averaged (fun _ => b) := (av_const b).symm
    _ ≤ _ := av_mono hi
    _ = _ := by unfold averaged; rw [← Finset.mul_sum]; ring

/-- Before-L threshold with already-usable point charge and later packet comparisons.
Use local `Ensures` for applications after dropping distant defaults; otherwise can
make those buys from an Allocation (incl every tag with strictly positive mass) and
geometry, see `actual`. -/
theorem before_local (P : Teller G) : ∃ i : ℕ, ∀ L : Side, i ≤ L.val → ∀ᶠ W : ℝ in atTop,0<W ∧
    ∃ κ : ℝ, 0<κ ∧ ∀ K H D n, ∀ᶠ x : ℝ in atTop,
      Ledger P L W κ K H n D x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L →
      100*(1+radiusB x)≤c.val → P.Funds S T → PointCharge T x W κ := by
  obtain ⟨i,h⟩ := points_grant P
  refine ⟨i,fun L hi => ?_⟩; filter_upwards [h L hi] with W hw
  obtain ⟨hW,κ,hK,H⟩ := hw
  refine ⟨hW,_,hK,fun u v n k => ?_⟩
  filter_upwards [H,authorize P L W κ u v k n hW hK] with x hx hu
  exact ⟨hu,hx.2.2⟩
end YM.SectorNext.Remainder.Affine
