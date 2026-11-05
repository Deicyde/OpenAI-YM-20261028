import YM.Analysis.Polydisc
import YM.Euclid.Comparator
import YM.Next.RANK.Value
import YM.Pressure.Seeds


/-!
# Plateaux and scale for the A comparison

An `Allowed` station knows its stretch fits inside a plateau. The two
heights are least possible (even when going beyond allowed would leave this
stage; the condition explicitly checks the whole stretch is possible). No
freedom to pay marker estimates with a different `L`, `M`, period or monitor.
Keep Phi/T relevances in the ORIGINAL units even when price windows pay for a
restarting comparison.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Station
open MeasureTheory Lattice Wilson RG Filter Set Asymptotics Real Extraction Cells
open scoped Topology BigOperators
variable {G : Gauge}

section



def want (u t : ℝ) : ℕ := Nat.ceil (Real.log t / Real.log u)

lemma wanted {u t : ℝ} (hu : 1<u) (ht : 0<t) (i : ℕ) : t ≤ u^i ↔ want u t ≤ i := by
  unfold want
  rw [Nat.ceil_le,div_le_iff₀ (Real.log_pos hu),← Real.log_pow]
  exact (Real.log_le_log_iff ht (pow_pos (zero_lt_one.trans hu) _)).symm

-- functions of numerical scale at fixed stage, may use for Wait below

def bump (u b s : ℝ) := want u ((YM.Vac.Numbers.P s)^b * (YM.Vac.Numbers.P s)^2)
def more (u s : ℝ) := want u (((Nat.ceil (Real.log s^2) : ℕ):ℝ)^ (10 : ℕ))

def wheel (A : Levels G) (k : ℕ) : ℝ := (A.clock.factor (A.clock.J k)).val

def height (A : Levels G) (b : ℝ) (k : ℕ) := bump (wheel A k) b (A.clock.hatBeta k)
def surplus (A : Levels G) (k : ℕ) := more (wheel A k) (A.clock.hatBeta k)
def middle (A : Levels G) (b : ℝ) (k : ℕ) := k-height A b k
def width (A : Levels G) (b : ℝ) (k : ℕ) := middle A b k - surplus A k

def mag (A : Levels G) (b : ℝ) (k : ℕ) := A.clock.monitor k ^ b

def gap (A : Levels G) (b : ℝ) (k : ℕ) := A.S.a k * mag A b k

lemma before (A : Levels G) (b : ℝ) (k : ℕ) : middle A b k ≤ k := Nat.sub_le ..
lemma wider (A : Levels G) (b : ℝ) (k : ℕ) : width A b k ≤ middle A b k := Nat.sub_le ..
lemma mag_pos (A : Levels G) (b : ℝ) (k : ℕ) : 0 < mag A b k := Real.rpow_pos_of_pos (Real.exp_pos _) _
lemma gap_pos (A : Levels G) (b : ℝ) (k : ℕ) : 0 < gap A b k := mul_pos (A.S.a_pos k) (mag_pos ..)
lemma hat_rate (A : Levels G) (h : G.Simple) : Tendsto A.clock.hatBeta atTop atTop :=
  Filter.tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos h))
lemma mag_rate (A : Levels G) (h : G.Simple) {b : ℝ} (hb : 0<b) : Tendsto (mag A b) atTop atTop :=
  (tendsto_rpow_atTop hb).comp (Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (n:=2) (by norm_num)).comp
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (hat_rate _ h)))))
lemma gap_rate (A : Levels G) (h : G.Simple) (b : ℝ) : Tendsto (gap A b) atTop (𝓝 0) := by
  let r := A.clock.hatBeta
  let s := A.S.scale
  let c := G.slopeConstant
  let v m := Real.exp (-(s m)/2)
  have hm := (hat_rate A h).eventually (YM.Vac.Numbers.cost b 1 zero_lt_one)
  have he (m : ℕ) : v m * v m = A.S.a m := by
    dsimp only [v]; rw [← Real.exp_add, show -(s m)/2+ -(s m)/2 = -(s m) by ring, ← Stock.a_log]
  have hs : Tendsto v atTop (𝓝 0) := by
    have he := tendsto_neg_atBot_iff.mpr A.S.divergent
    exact Real.tendsto_exp_atBot.comp (he.atBot_div_const (by norm_num))
  have hx : ∀ᶠ m : ℕ in atTop, v m * r m ≤ 1 := by
    have hV : Tendsto (fun u : ℝ => Real.exp (-u/2)*(A.clock.bar+c*u)) atTop (𝓝 0) := by
      have hz := isLittleO_pow_exp_pos_mul_atTop 1 (show (0:ℝ)<1/2 by norm_num)
      have h1 : Tendsto (fun u : ℝ => u*Real.exp (-u/2)) atTop (𝓝 0) := by
        have he := hz.tendsto_div_nhds_zero
        refine he.congr (fun u => ?_)
        rw [pow_one, div_eq_mul_inv,← Real.exp_neg,show -((1/2:ℝ)*u) = -u/2 by ring]
      have h2 : Tendsto (fun u : ℝ => Real.exp (-u/2)) atTop (𝓝 0) := by
        have hu := tendsto_neg_atBot_iff.mpr (show Tendsto id (atTop : Filter ℝ) atTop from tendsto_id)
        exact Real.tendsto_exp_atBot.comp (hu.atBot_div_const (by norm_num))
      have hf := (h2.mul_const A.clock.bar).add (h1.const_mul c); rw [zero_mul,mul_zero,zero_add] at hf
      refine hf.congr (fun u => ?_); ring
    exact (hV.comp A.S.divergent).eventually (ge_mem_nhds zero_lt_one)
  refine squeeze_zero' (Eventually.of_forall fun x => (gap_pos A b x).le) ?_ hs
  filter_upwards [hm,hx] with i hi hu
  simp only [Real.rpow_one] at hi
  have ha : v i * mag A b i ≤ 1 := (mul_le_mul_of_nonneg_left hi (show 0≤v i from (Real.exp_pos _).le)).trans hu
  rw [gap,← he,mul_assoc]; exact mul_le_of_le_one_right (Real.exp_pos _).le ha
end

variable (A : Levels G) (b : ℝ)

structure Allowed (k : ℕ) : Prop where
  positive : 0<k
  reserves : height A b k + surplus A k ≤ k
  plateau (m : ℕ) : width A b k ≤ m → m≤k → A.clock.J m=A.clock.J k

namespace Allowed
variable {A b k} (h : Allowed A b k)
include h
lemma full : k-middle A b k=height A b k := by
  have hx := h.reserves; unfold middle; omega
lemma shift : middle A b k-width A b k=surplus A k := by
  have hx := h.reserves; unfold width middle; omega
lemma large : 1 < wheel A k := by
  obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero h.positive.ne'
  rw [hi]; unfold wheel; rw [A.fits.sameFactor i]; have := A.S.block_large i
  exact_mod_cast (by omega : 1 < (A.S.block i).val)
lemma blocks (i : ℕ) (hh : width A b k ≤ i) (hp : i<k) : ((A.S.block i).val:ℝ)=wheel A k := by
  unfold wheel; rw [← A.fits.sameFactor i, h.plateau (i+1) (by omega) (by omega)]
lemma scales (m j : ℕ) (he : width A b k ≤ m) (hr : m ≤ j) (hp : j≤k) : A.S.a m/A.S.a j=(wheel A k)^(j-m) := by
  induction j,hr using Nat.le_induction with
  | base => rw [div_self (A.S.a_pos _).ne', Nat.sub_self,pow_zero]
  | succ j hj ih =>
    have ht := h.blocks j (he.trans hj) (by omega)
    rw [show j+1-m=j-m+1 by omega, pow_succ, ← ih (by omega), A.S.a_step,ht]; field_simp
lemma delta (p : ℕ) (m j : ℕ) (he : width A b k ≤ m) (hr : m≤j) (hp : j≤k) :
    ((A.S.toDepth hr p).count.val:ℝ)=(wheel A k)^(j-m) := by
  let Y := A.S.toDepth hr p; rw [← h.scales m j he hr hp, eq_div_iff (A.S.a_pos j).ne',mul_comm, A.S.embeds_scale Y]
lemma dilation : mag A b k * A.clock.monitor k ^ 2 ≤ A.S.a (middle A b k) / A.S.a k := by
  rw [h.scales (middle A b k) k (wider ..) (before ..) le_rfl,h.full]
  exact (wanted h.large (mul_pos (mag_pos A b k) (pow_pos (Real.exp_pos _) _)) _).2 le_rfl
lemma surplusage (p : ℕ) : (A.clock.coverSize k)^(10:ℕ) ≤ (A.S.toDepth (wider A b k) p).count.val := by
  have e : 1 ≤ A.clock.coverSize k := (A.budget k).B_pos
  have hv := h.delta p _ _ le_rfl (wider A b k) (before ..)
  rw [h.shift] at hv
  have hx : ((A.clock.coverSize k:ℝ))^ (10:ℕ) ≤ ((A.S.toDepth (wider A b k) p).count.val:ℝ) := by
    rw [hv]; exact (wanted h.large (by exact_mod_cast (pow_pos e 10)) _).2 le_rfl
  exact_mod_cast hx
end Allowed
end YM.Next.Rank.Station
