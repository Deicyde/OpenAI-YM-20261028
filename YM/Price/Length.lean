import YM.Price.Intent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform entrances for each individual stage

Use physical units shrink with total σ, not assuming σ₀ > 0. Since protection
exists independent of depth and floorL asks precede anything here, each volume
bill x ↦ `(log(x))^C` is fixed at stage. This allows a single period threshold
along arbitrary depth, not separate by µ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG.Supply
open Wilson Lattice Set Filter Function Asymptotics Finset Real
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff
variable {G : Gauge}

lemma Bar.exists_above {p : Sheet G} {w : Rolls p} {T : Protection w} (W : Delays T) (b : ℝ) :
    ∃ P : Bar W, b ≤ P.value := by
  have he : ∀ᶠ x : ℝ in atTop, (Real.sqrt x)⁻¹*Real.exp (Real.log (Real.log x)^2) ≤ 1 := by
    have hx := (Real.isLittleO_pow_log_id_atTop (n:=2)).def (c:=(1/2:ℝ)) (by norm_num)
    filter_upwards [Real.tendsto_log_atTop.eventually hx,eventually_gt_atTop 1] with x hh hp
    have hg := Real.log_pos hp
    simp only [id_eq,norm_of_nonneg hg.le, norm_of_nonneg (sq_nonneg _)] at hh
    have ht : Real.exp (Real.log (Real.log x)^2) ≤ Real.sqrt x := calc
      _ ≤ Real.exp ((1/2)*Real.log x) := Real.exp_monotone hh
      _ = _ := by rw [show (1/2:ℝ)*Real.log x=Real.log (Real.sqrt x) by rw [Real.log_sqrt (by linarith)]; ring, Real.exp_log (Real.sqrt_pos.2 (by linarith))]
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr (Real.sqrt_nonneg x))
      _ = _ := inv_mul_cancel₀ (Real.sqrt_pos.2 (by linarith)).ne'
  obtain ⟨P,hP⟩ := eventually_atTop.1 he
  let a := max (max 2 P) (max b (W.betaEntry p.first))
  have ha : P≤a := le_trans (le_max_right ..) (le_max_left ..)
  refine ⟨⟨a,lt_of_lt_of_le (?_ : (1:ℝ)<2) (le_trans (le_max_left ..) (le_max_left ..)),
    le_trans (le_max_right ..) (le_max_right ..), fun x H => hP x (ha.trans H)⟩, le_trans (le_max_left ..) (le_max_right ..)⟩
  norm_num

variable {p : Sheet G} {w : Rolls p} {T : Protection w} {W : Delays T} (Y : Bar W)

/-- Bill in **output** sites, issued against `m+1→m`. Covers builtin sizeT
and patch too, on top of volume requested. -/
def Bar.bill (j : ℕ) (s : ℝ) : ℕ :=
    let y m := Y.value+G.slopeConstant*m
    let c := Nat.ceil (Real.log (y s)^2)
    let c' := Nat.ceil (Real.log (y (s+Real.log (w.L j).val))^2)
    W.shells j * (1+c+c')^(W.growth j) + 100*(c+1) + 100*((j+3)*(w.L j).val+1)

private lemma isBigO_const_id_atTop (a : ℝ) : (fun _ : ℝ => a) =O[atTop] id := (isLittleO_const_id_atTop _).isBigO

private lemma ceil_lo (a b r : ℝ) (hb : 0 < b) :
    (fun s : ℝ => (Nat.ceil (Real.log (a+b*(s+r))^2) : ℝ)) =O[atTop] id := by
  have hh : Tendsto (fun s : ℝ => a+b*(s+r)) atTop atTop := by
    apply tendsto_atTop_add_const_left _ a; refine Tendsto.const_mul_atTop hb (tendsto_atTop_add_const_right _ r tendsto_id)
  have h1 : (fun s : ℝ => a+b*(s+r)) =O[atTop] id := by
    refine (isBigO_const_id_atTop _).add ?_; exact ((isBigO_refl id _).add (isBigO_const_id_atTop _)).const_mul_left _
  have he : (fun s : ℝ => Real.log (a+b*(s+r))^2) =O[atTop] id :=
    ((Real.isLittleO_pow_log_id_atTop (n:=2)).isBigO.comp_tendsto hh).trans h1
  refine IsBigO.trans ?_ (he.add (isBigO_const_id_atTop (1:ℝ)))
  apply isBigO_of_le; intro x
  change ‖(Nat.ceil _ : ℝ)‖ ≤ ‖_ + (1 : ℝ)‖; rw [norm_of_nonneg (by positivity), norm_of_nonneg (by positivity)]
  exact le_of_lt (Nat.ceil_lt_add_one (sq_nonneg _))

theorem Bar.allocated (h : G.Simple) (j : ℕ) :
    ∀ᶠ s : ℝ in atTop, (Y.bill j s : ℝ) ≤ Real.exp s := by
  have hg := Gauge.slopeConstant_pos h
  let c := fun s : ℝ => (Nat.ceil (Real.log (Y.value+G.slopeConstant*s)^2):ℝ)
  let c' := fun s : ℝ => (Nat.ceil (Real.log (Y.value+G.slopeConstant*(s+Real.log (w.L j).val))^2):ℝ)
  have H : c =O[atTop] id := by simpa only [add_zero,c] using ceil_lo Y.value _ 0 hg
  have H' : c' =O[atTop] id := ceil_lo _ _ _ hg
  have K := (((isBigO_const_id_atTop (1:ℝ)).add H).add H').pow (W.growth j)
  have he (u : ℕ) : (fun x : ℝ => x^u) =o[atTop] Real.exp := by simpa using isLittleO_pow_exp_pos_mul_atTop u (zero_lt_one' ℝ)
  have ha : id (α := ℝ) =o[atTop] Real.exp := by simpa only [pow_one] using! he 1
  let q : ℝ := W.shells j
  let e : ℝ := 100*(((j:ℝ)+3)*(w.L j).val+1)
  have hc := (((K.trans_isLittleO (he _)).const_mul_left q).add (((H.add (isBigO_const_id_atTop (1:ℝ))).trans_isLittleO ha).const_mul_left (100:ℝ))).add
    ((isBigO_const_id_atTop e).trans_isLittleO ha)
  have hh : (fun s : ℝ => (Y.bill j s:ℝ))=o[atTop] Real.exp := by
    refine hc.congr_left fun x => ?_
    unfold Bar.bill
    push_cast
    rfl
  filter_upwards [hh.def (c:=1) zero_lt_one] with s hs
  simpa only [norm_of_nonneg (Nat.cast_nonneg _), norm_of_nonneg (Real.exp_pos s).le, one_mul] using hs

/-- Advance stage after waiting *in the coarser* until the prior step's
scale is large. For periods this ensures volume bill ≤ one physical unit.
First plateau exception can be paid directly for all (finitely many) steps.
-/
theorem Bar.enters (h : G.Simple) {j : ℕ} (hj : p.first < j) : ∃ n : ℕ,
    ∀ m : ℕ, n ≤ m → ∀ s : ℝ, (m:ℝ)*Real.log 3 ≤ s →
      W.betaEntry j ≤ Y.value+G.slopeConstant*s ∧ W.scaleEntry j Y.value ≤ s ∧
      0 < s ∧ Real.log (w.L j).val ≤ (j:ℝ)⁻¹*s ∧ (Y.bill j s : ℝ) ≤ Real.exp s := by
  let F : Set ℝ := {s | W.betaEntry j ≤ Y.value+G.slopeConstant*s ∧ W.scaleEntry j Y.value ≤ s ∧
      0 < s ∧ Real.log (w.L j).val ≤ (j:ℝ)⁻¹*s ∧ (Y.bill j s : ℝ) ≤ Real.exp s}
  have he : F ∈ (atTop : Filter ℝ) := by
    have hb : Tendsto (fun s : ℝ => Y.value+G.slopeConstant*s) atTop atTop :=
      tendsto_atTop_add_const_left _ _ ((tendsto_id (x:=atTop)).const_mul_atTop (Gauge.slopeConstant_pos h))
    have hh := (tendsto_id (x:=atTop)).const_mul_atTop (inv_pos.mpr (show 0 < (j:ℝ) from by exact_mod_cast Nat.pos_of_ne_zero (by omega)))
    exact (hb.eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_gt_atTop _).and
      ((hh.eventually_ge_atTop _).and (Y.allocated h j))))
  obtain ⟨s,hs⟩ := eventually_atTop.1 (show ∀ᶠ x : ℝ in atTop, x∈F from he)
  have hb : Tendsto (fun m : ℕ => (m:ℝ)*Real.log 3) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos (by norm_num : (1:ℝ) < 3))
  obtain ⟨n,hn⟩ := eventually_atTop.1 (hb.eventually_ge_atTop s)
  exact ⟨n,fun i hi a ha => hs _ ((hn i hi).trans ha)⟩

/-- bench slot for comparisons. Allocate using worst upper scale of plateau. -/
theorem Wait.lead {Y : Bar W} (B : Wait Y) (j : ℕ) : ∃ m : ℕ,
    ∀ k : ℕ, m ≤ k → ∀ s : ℝ, k*Real.log 3 ≤ s → s ≤ k*Real.log (w.L j).val →
      B.readyHere j ≤ s ∧ B.window j s ≤ k/2 := by
  have ha := (w.large j).size
  have hn : 0<Real.log (w.L j).val := Real.log_pos (by exact_mod_cast (show 1 < (w.L j).val by omega))
  have he := (B.sublin j).eventually (ge_mem_nhds (show 0 < (2*Real.log (w.L j).val)⁻¹ by positivity))
  obtain ⟨s,hs⟩ := eventually_atTop.1 (he.and ((eventually_ge_atTop (B.readyHere j)).and (eventually_gt_atTop (0:ℝ))))
  have hb : Tendsto (fun m : ℕ => (m:ℝ)*Real.log 3) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos (by norm_num : (1:ℝ) < 3))
  obtain ⟨n,hu⟩ := eventually_atTop.1 (hb.eventually_ge_atTop s)
  refine ⟨n,fun i hi a hl hh => ?_⟩
  have hA := hs _ ((hu i hi).trans hl)
  obtain ⟨hf,hf',HG⟩ := hA
  refine ⟨hf',?_⟩
  have hg : (B.window j a:ℝ)/a ≤ (2*Real.log (w.L j).val)⁻¹ := hf
  have hu := ((div_le_iff₀ HG).mp hg).trans (mul_le_mul_of_nonneg_left hh (by positivity))
  rw [show _⁻¹ *( (i:ℝ)* Real.log (w.L j).val)=(i:ℝ)/2 by field_simp] at hu
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  exact_mod_cast (le_div_iff₀ (zero_lt_two' ℝ)).1 hu
end YM.RG.Supply
