import Mathlib.Analysis.ODE.ExistUnique
import YM.Next.RANK.StationMeter
import YM.Next.RANK.Tuning


/-!
# Concrete dependency order test: is there room for Allocation?

Does **not** produce prices on marker polynomials or guarantee applicability
in physics (Offers). Test that the A station and terminal determinant costs *in
isolation* can indeed use the `Paid` scheduling machinery. Includes coherence of
B-hat with any Bar; costs ahead of period choice. Finite number of demands per J.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Ship
open Function Set Filter RG RG.Supply Station Asymptotics Real
open scoped Topology BigOperators
variable {G : Gauge} {p : Sheet G} {w : Rolls p} {T : Protection w} {D : Delays T} (Z : Bar D)

private lemma subwant (f : ℝ → ℝ) (h : f =o[atTop] id) (hp : ∀ᶠ i in atTop,0≤f i) : (fun i => (Nat.ceil (f i) : ℝ)) =o[atTop] id := by
  have he := h.add (isLittleO_const_id_atTop (1:ℝ))
  refine IsBigO.trans_isLittleO (isBigO_iff.mpr ⟨1,?_⟩) he
  filter_upwards [hp] with i hi
  rw [one_mul]
  change ‖(Nat.ceil (f i):ℝ)‖ ≤ ‖f i + 1‖
  simpa [Real.norm_of_nonneg hi,Real.norm_of_nonneg (show 0 ≤ f i + 1 by linarith)] using! (Nat.ceil_lt_add_one hi).le

private lemma possible_bump {u b : ℝ} (hu : 1<u) (hb : 0 ≤ b) :
    (fun s : ℝ => (bump u b s:ℝ) + (more u s:ℝ)) =o[atTop] id := by
  let z := YM.Vac.Numbers.P
  let v (s : ℝ) := Nat.ceil (Real.log s ^2)
  have hs : (fun s : ℝ => log (z s))=o[atTop] id := by
    have H := ((Real.isLittleO_pow_log_id_atTop (n:=2)).comp_tendsto Real.tendsto_log_atTop).trans_isBigO Real.isLittleO_log_id_atTop.isBigO
    simpa only [z,YM.Vac.Numbers.P, Real.log_exp] using! H
  have ht : (fun s : ℝ => (v s:ℝ))=o[atTop] id := subwant _ Real.isLittleO_pow_log_id_atTop (Eventually.of_forall fun _ => sq_nonneg _)
  have hg : ∀ᶠ s in atTop, 1 ≤ (v s:ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with s hs
    have he : 0 < v s := Nat.ceil_pos.mpr (pow_pos (Real.log_pos hs) _)
    exact_mod_cast he
  have hk : (fun s : ℝ => Real.log (v s:ℝ)) =o[atTop] id := by
    refine IsBigO.trans_isLittleO (isBigO_iff.mpr ⟨1,?_⟩) ht
    filter_upwards [hg] with s hs
    rw [one_mul]
    simp only [Real.norm_of_nonneg (Real.log_nonneg hs), Real.norm_of_nonneg (show (0:ℝ) ≤ v s by positivity)]
    exact Real.log_le_self (by positivity)
  let e (s : ℝ) := Real.log ((z s)^b*(z s)^2) / Real.log u
  have hx : e =o[atTop] id := by
    refine (((hs.const_mul_left b).add (hs.const_mul_left 2)).const_mul_left (Real.log u)⁻¹).congr_left ?_
    intro s
    have hn : 0 < z s := Real.exp_pos _
    change _=Real.log ((z s)^b*(z s)^2) / Real.log u
    rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_rpow hn]
    push_cast; ring
  have he' : ∀ᶠ i in atTop,0 ≤ e i := Eventually.of_forall fun i =>
    have hz : 1 ≤ z i := Real.one_le_exp (sq_nonneg _)
    div_nonneg (Real.log_nonneg (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hz hb) (one_le_pow₀ hz))) (Real.log_pos hu).le
  let a (s : ℝ) := Real.log ((v s:ℝ)^ (10:ℕ)) / Real.log u
  have ha : a=o[atTop] id := by
    refine ((hk.const_mul_left 10).const_mul_left (Real.log u)⁻¹).congr_left ?_
    intro s
    change (Real.log u)⁻¹*(10*Real.log (v s:ℝ))= _; dsimp only [a]
    rw [Real.log_pow];push_cast;ring
  have ha' : ∀ᶠ s in atTop,0 ≤ a s := by
    filter_upwards [hg] with s hi
    exact div_nonneg (Real.log_nonneg (one_le_pow₀ hi)) (Real.log_pos hu).le
  exact (subwant e hx he').add (subwant a ha ha')

-- Wait scale uses **log measure in σ rather than level count**.
def preHat (s : ℝ) := Z.value + G.slopeConstant*s

def benchCost (b : ℝ) (j : ℕ) (s : ℝ) := bump ((w.L j).val:ℝ) b (preHat Z s) + more ((w.L j).val:ℝ) (preHat Z s)

lemma accommodate (b : ℝ) (j : ℕ) (h : G.Simple) (hb : 0≤b) :
    Tendsto (fun s : ℝ => (benchCost Z b j s:ℝ)/s) atTop (𝓝 0) := by
  have hv : Tendsto (preHat Z) atTop atTop := Filter.tendsto_atTop_add_const_left _ _
    (Tendsto.const_mul_atTop (Gauge.slopeConstant_pos h) tendsto_id)
  have hu : 1 < ((w.L j).val:ℝ) := by have ht := (w.large j).size; exact_mod_cast (by omega : 1 < (w.L j).val)
  have hp : preHat Z=O[atTop] id := ((isLittleO_const_id_atTop _).isBigO).add ((isBigO_refl id _).const_mul_left _)
  have he := (((possible_bump hu hb).comp_tendsto hv).trans_isBigO hp).tendsto_div_nhds_zero
  simpa only [benchCost,Nat.cast_add] using! he

def amount (k : ℕ) (s : ℝ) := Real.log (YM.Vac.Numbers.P (preHat Z s))/(16*k)
lemma able (h : G.Simple) (k : ℕ) (hk : 0 < k) : Tendsto (amount Z k) atTop atTop := by
  have hv : Tendsto (preHat Z) atTop atTop := Filter.tendsto_atTop_add_const_left _ _
    (Tendsto.const_mul_atTop (Gauge.slopeConstant_pos h) tendsto_id)
  have he := Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (n:=2) (by decide)).comp
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hv)))
  exact (Real.tendsto_log_atTop.comp he).atTop_div_const (by positivity : 0 < (16:ℝ)*k)

-- Paid global record. Re-check each consumer input through A; only feasibility of this *numeric* component.

def Account (P : Wait Z) (O : HaarBudget G) (b : ℝ) (j k : ℕ) := ∀ s : ℝ,P.readyHere j ≤ s →
    ticket O (p.profile j) k ≤ amount Z k s ∧ benchCost Z b j s ≤ P.window j s

lemma honoured {P : Wait Z} (h : G.Simple) (O : HaarBudget G) (k : ℕ → ℕ) (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i)
    (D : ℕ → Finset ℕ) (hm : ∀ i, 0<k i) :
    ∃ P' : Wait Z, P.minLength ≤ P'.minLength ∧ (∀ j,P.readyHere j ≤ P'.readyHere j ∧ (∀ s,P.window j s≤P'.window j s)) ∧
      ∀ j i,i∈D j → Account Z P' O (b i) j (k i) := by
  have he (j : ℕ) : ∀ᶠ s in atTop, ∀ i∈ D j,ticket O (p.profile j) (k i) ≤ amount Z (k i) s :=
    eventually_all_finset _|>.2 (fun i _ => (able Z h _ (hm i)).eventually_ge_atTop _)
  choose v hv using fun j => eventually_atTop.mp (he j)
  let z (j : ℕ) (s : ℝ) := ∑ i∈D j,benchCost Z (b i) j s
  let P' : Wait Z := {
    minLength := P.minLength
    readyHere := fun j => max (P.readyHere j) (v j)
    window := fun j s => P.window j s+z j s
    sublin j := by
      have ht : Tendsto (fun s => (z j s:ℝ)/s) atTop (𝓝 0) := by
        have he := tendsto_finsetSum (D j) (fun i _ => accommodate Z (b i) j h (hb i))
        simpa [z,Finset.sum_div] using! he
      simpa [add_div] using! (P.sublin j).add ht }
  refine ⟨P',le_rfl,fun j => ⟨le_max_left ..,fun s => Nat.le_add_right ..⟩,fun j i hi s hs => ?_⟩
  refine ⟨hv j s ((le_max_right ..).trans hs) i hi, ?_⟩
  exact (Finset.single_le_sum (f:=fun i => benchCost Z (b i) j s) (fun _ _ => Nat.zero_le _) hi).trans (Nat.le_add_left ..)

-- This only proves room, NEVER instantiate existence
-- of Quota using this inference alone.




end YM.Next.Rank.Ship
