import YM.Extension.UV.Shoot
import Mathlib.Analysis.PSeries
/-! Numerical sampling prices available before UV cutoffs. Not a bound on derivatives or a claim
of coupling limit. This makes the power radii and sum demanded in the analytic Banach comparison
explicit for the actual hats of sufficiently delayed levels. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
namespace YM.Extension.UV
open Set Filter Function Lattice RG Shoot
open Supply
variable {G : Gauge}

def contour (x:ℝ) := x ^ (39/40:ℝ)
def capacity (x:ℝ) := x ^ (-1/20:ℝ)
def advanceMin (G : Gauge):= G.slopeConstant*Real.log 3
lemma advance_pos (g:G.Simple) : 0<advanceMin G:=mul_pos (Gauge.slopeConstant_pos g) (Real.log_pos (by norm_num))
lemma step_hat (a:Levels G) (i:ℕ) : a.clock.hatBeta (i+1)=a.clock.hatBeta i+jump a i := by unfold jump Calendar.hatBeta Levels.S; rw [Schedule.scale_succ]; ring
lemma jump_lower (g:G.Simple) (a:Levels G) (i:ℕ): advanceMin G ≤ jump a i := mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) (by exact_mod_cast a.S.block_large i)) (Gauge.slopeConstant_pos g).le
lemma hat_positive (_g:G.Simple) (a:Levels G) (i:ℕ) : 1<a.clock.hatBeta i:= a.fits.delayed _
lemma contour_bound (a:Levels G) (i:ℕ) : 0<contour (a.clock.hatBeta i) ∧ contour (a.clock.hatBeta i) ≤ a.clock.hatBeta i := by
  have hx := a.fits.delayed i
  exact ⟨Real.rpow_pos_of_pos (by linarith) _,(Real.rpow_le_rpow_of_exponent_le hx.le (show (39:ℝ)/40 ≤ 1 by norm_num)).trans_eq (Real.rpow_one _)⟩
lemma contour_mono (g:G.Simple) (a:Levels G) : Monotone fun i=>contour (a.clock.hatBeta i):= by
  have hm := monotone_nat_of_le_succ (f:=a.clock.hatBeta) fun i => by rw [step_hat]; linarith [jump_lower g a i,advance_pos g]
  exact fun i j hij=> Real.rpow_le_rpow (zero_le_one.trans_lt <| a.fits.delayed i).le (hm hij) (by positivity)

lemma sum_cap_target (G : Gauge) (g:G.Simple) : ∃ b : ℝ, ∀ a : Levels G, b ≤ a.clock.bar → ∀ N : ℕ,
      ∑ i∈Finset.range N, capacity (a.clock.hatBeta (i+1)) / contour (a.clock.hatBeta (i+1)) ≤ 1/1000 := by
  let c := advanceMin G
  let f := fun i : ℕ=> c ^ (-(41:ℝ)/40) * (i:ℝ)^(-(41:ℝ)/40)
  have hc := advance_pos g
  have hf : Summable f:= (Real.summable_nat_rpow.mpr (show -(41:ℝ)/40 < -1 by norm_num)).mul_left _
  have hconv : ∀ᶠ i in atTop, (∑' k, f (k + i)) ≤ (1/1000:ℝ):= (tendsto_sum_nat_add f).eventually_le_const (show (0:ℝ) < 1/1000 by norm_num)
  obtain ⟨M,hM,hM0⟩ := (hconv.and (eventually_gt_atTop 0)).exists
  refine ⟨c*(1+M),fun a ha N=>?_⟩
  have hB i : c*(1+M+i) ≤ a.clock.hatBeta i:= by
    induction i with
    | zero => simpa [Calendar.hatBeta] using ha
    | succ i ih => rw [Nat.cast_add,Nat.cast_one,step_hat]; linarith [jump_lower g a i]
  calc
    _ ≤ ∑ i∈Finset.range N, f (i+M) := by
        refine Finset.sum_le_sum fun i _=>?_;
        have hv := a.fits.delayed (i+1)
        rw [capacity,contour,← Real.rpow_sub (by linarith : 0<a.clock.hatBeta (i+1)),show (-(1:ℝ)/20-39/40)=-(41:ℝ)/40 by ring]
        have hA:= hB (i+1)
        calc
          _ ≤ (c*(1+M+(i+1:ℕ)))^(-(41:ℝ)/40) := Real.rpow_le_rpow_of_nonpos (by have hc' : 0<c:=hc; positivity) hA (by norm_num)
          _ ≤ _ := by
            by_cases hi : 0< i+M
            · unfold f
              rw [← Real.mul_rpow (by have : 0<c:=hc; positivity) (by positivity)]
              apply Real.rpow_le_rpow_of_nonpos (by have : 0<c:=hc; positivity) _ (by norm_num)
              rw [Nat.cast_add,Nat.cast_add,Nat.cast_one]; nlinarith [show 0<c from hc]
            exfalso
            -- ensure M ≠ 0 by choosing tail with index+1 rather than depend f 0 lower
            omega
    _ ≤ _ := ((hf.comp_injective (i:=fun i:ℕ=>i+M) (by intro i j hij; dsimp only at hij; omega)).sum_le_tsum _ (fun i _=> by have : 0<c:=hc; exact mul_nonneg (Real.rpow_nonneg this.le _) (Real.rpow_nonneg (by positivity) _))).trans hM

variable {a : Levels G} {T : Recipe a}
lemma center_error (_g:G.Simple) (h:Drifting a) {f : ℕ → ∀ p, Trail a p} (hf:T.Stays f) {N p i:ℕ} (hx:(f N p 0).beta=a.clock.bar) (hi:i ≤ N) : |(f N p i).beta-a.clock.hatBeta i| ≤ (G.slopeConstant/4)*a.S.scale i:= by
  induction i with
  | zero => simp [hx,Calendar.hatBeta]
  | succ i ih=>
    have ht := ((hf N p).persists i (by omega) hi).drift
    calc
      _ = |(f N p i).beta-a.clock.hatBeta i + ((f N p (i+1)).beta-(f N p i).beta-jump a i)| := by congr 1; rw [step_hat]; ring
      _ ≤ _ := (abs_add_le ..).trans ((add_le_add (ih (by omega)) ht).trans (by have H:= (div_le_iff₀ (block_positive a i)).mp (h i); rw [Schedule.scale_succ]; linarith))

def demand (G:Gauge) {s:Sheet G} (w:Rolls s) (j:ℕ):=G.slopeConstant*(w.L j).val
lemma demand_ratio (g:G.Simple) {s:Sheet G} {w:Rolls s} {Θ:Protection w} {W:Delays Θ} {Y : Bar W} {I:Wait Y} {a:Levels G}
    (h:Paid I a) (hx:demand G w ≤ W.betaEntry) i: a.clock.hatBeta (i+1) ≤ 2*a.clock.hatBeta i:= by
  have hh := h.pays i
  have hb := (hx (a.clock.J (i+1))).trans hh
  have hl : w.L (a.clock.J (i+1))=a.S.block i:= by rw [← h.lengths,a.fits.sameFactor]
  unfold demand at hb; rw [hl] at hb
  have hep:= Real.log_le_sub_one_of_pos (x:=((a.S.block i).val:ℝ)) (by positivity)
  have hg := Gauge.slopeConstant_pos g
  have he := step_hat a i
  unfold jump at he
  nlinarith

structure NumericAdmission (a:Levels G) (T : Recipe a) (f:ℕ→∀ p,Trail a p) : Prop where
  positive i : 1 < a.clock.hatBeta i
  near i : a.clock.hatBeta (i+1) ≤ 2*a.clock.hatBeta i
  radius i : 0<contour (a.clock.hatBeta i) ∧ contour (a.clock.hatBeta i) ≤ a.clock.hatBeta i
  monotoneRadius : Monotone (fun i=>contour (a.clock.hatBeta i))
  capacitySum N : ∑ i∈Finset.range N, capacity (a.clock.hatBeta (i+1))/contour (a.clock.hatBeta (i+1)) ≤ 1/1000
  reaches N p : (f N p 0).beta = a.clock.bar
  intended N p i (hi:i ≤ N) t : |t-(f N p i).beta| ≤ contour (a.clock.hatBeta i)/8 → t ∈ band a i
  actual : T.Stays f
lemma numerical_admission (g:G.Simple) {s:Sheet G} {w:Rolls s} {Θ:Protection w} {W:Delays Θ} {Y : Bar W} {I:Wait Y} {a:Levels G}
    (h:Paid I a) (hx:demand G w ≤ W.betaEntry) (hb:(sum_cap_target G g).choose ≤ Y.value) {T:Recipe a} {f:ℕ→∀p,Trail a p} (hf:T.Stays f) (hr:T.make f|>.Selected) : NumericAdmission a T f := by
  refine ⟨hat_positive g a, demand_ratio g h hx, contour_bound a, contour_mono g a, (sum_cap_target G g).choose_spec a (by rwa [h.bar]),hr.reaches,?_,hf⟩
  intro n p i hi t ht
  have he := center_error g (Drifting.pay h) hf (hr.reaches n p) hi; have hz := (contour_bound a i).2
  have hg := Gauge.slopeConstant_pos g; have hs := scale_nn a i
  have hb' := a.clock.bar_pos; obtain ⟨h1,h2⟩ := abs_le.mp he; obtain ⟨h3,h4⟩ := abs_le.mp ht
  unfold band; simp only [mem_Icc]; unfold Calendar.hatBeta Levels.S at *
  constructor <;> nlinarith
end YM.Extension.UV
