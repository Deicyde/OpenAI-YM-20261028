import YM.OPE.Therm.Rarity
import YM.OPE.Loom.ExtraDelays
/-! # Strengthen plateau delays for thermodynamic entropy program -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm
open Function Filter Set MeasureTheory Lattice Wilson RG RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Push.PriceCompiler Next.Foundations
open scoped ENNReal Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {X:History G} {K:Levels G}
/-- Polylog estimates on pre-block objects become uniform after L. -/
structure Offstage (G:Gauge) (i:ℕ)(b:Stage)(L:Side)(x:ℝ):Prop where
   track : (L.val:ℝ) ≤ Real.log x
   strip : 10/b.width ≤ Real.log x
   strain : 10/b.clip.linear ≤ Real.log x
   price : Vac.fiat G b x+ Fintype.card PlaqAxes ≤ Real.log x^2
   pedestal : 100000*(i+1:ℝ) ≤ Real.log x
   jobs : 100000*(1+b.paths+b.supportExponent+b.clip.relaxation+b.width+b.columns+b.clip.direct+b.clip.linear) ≤ Real.log x
lemma offstage_willing (G : Gauge)(i:ℕ)(b:Stage)(L:Side): ∀ᶠ x:ℝ in atTop, Offstage G i b L x:= by
    let k:ℝ:= Fintype.card PlaqAxes; let H:ℝ:= 100000*(1+b.paths+b.supportExponent+b.clip.relaxation+b.width+b.columns+b.clip.direct+b.clip.linear)
    let B:ℝ:=2*(1+(4*b.paths+1))+1+k*(b.clip.direct+b.paths^2)+4*(Module.finrank ℝ G.Mat)*Real.log 16+k; let R:ℝ:= 2*Module.finrank ℝ G.Mat
    have ht:= Real.tendsto_log_atTop
    filter_upwards [ht.eventually_ge_atTop 1,ht.eventually_ge_atTop ((L.val):ℝ),ht.eventually_ge_atTop (10/b.width),ht.eventually_ge_atTop (10/b.clip.linear),ht.eventually_ge_atTop (100000*((i:ℝ)+1)),ht.eventually_ge_atTop H,ht.eventually_ge_atTop B,ht.eventually_ge_atTop (R+1)] with x h1 hx hh he hq hH hB hR
    refine ⟨hx,hh,he, ?_,hq,hH⟩; unfold Vac.fiat
    have hz:0≤ Real.log x:= zero_le_one.trans h1; have hu:= mul_le_mul_of_nonneg_right hR hz; unfold B k at hB; unfold R at hu; linarith
structure Poetry (K:Levels G) : Prop where
   stage k : Offstage G (K.clock.J k) (K.params k) (K.S.block k) (K.clock.hatBeta k)
variable {s:Sheet G} {D:Rolls s} {T:Protection D}
lemma poetry_delay (V:Delays T) : ∃ W, DelayLe V W ∧ ∀ W', DelayLe W W' →
    ∀ {X:Bar W'} (P:Wait X) (K:Levels G), Paid P K → Poetry K := by
   obtain ⟨u,-,hv,H⟩:=collect_upper V.betaEntry (fun j x=> ∀ i ∈ Finset.range (j+1), Offstage G i (s.profile i) (D.L j) x)
     (fun j=> ((Finset.range (j+1)).eventually_all.mpr fun i _=> offstage_willing ..))
   refine ⟨{ V with betaEntry:=u}, ⟨hv,le_rfl,le_rfl,le_rfl⟩, fun W hW X P K h=>⟨fun i=> ?_⟩⟩
   rw [params_eq h i, Extra.Iteration.block_eq h]; exact H (K.clock.J (i+1)) _ ((hW.beta _).trans (h.pays i)) _ (Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr (K.fits.mono i.le_succ)))
section
variable (Y:Poetry K)(h:G.Simple)
local notation "X" => K.clock.hatBeta
local notation "s" => K.S.a
omit Y in
lemma shelter (i:ℕ) (r:ℝ) : r>1 → s i*r < 1 → ∃ j:ℕ,j < i ∧ s (j+1) ≤ r*s i ∧ r*s i < s j:= by
   intro hr hi; let p m:=s m ≤ r*s i; letI (m:ℕ):Decidable (p m):= Classical.propDecidable _; have hx:s i*r=r*s i:=mul_comm ..; rw [hx] at hi
   have hz:p i:= by exact le_mul_of_one_le_left (K.S.a_pos _).le hr.le
   have ht:∃ n,p n:=⟨i,hz⟩; have he:¬p 0:= by unfold p; rw [K.S.a_zero]; exact hi.not_ge
   let j:= Nat.find ht; have ha: j≠0:= fun h=>he (h ▸ Nat.find_spec ht); have hh:j-1+1=j:=Nat.sub_add_cancel (by omega)
   refine ⟨j-1, (by have hj:=Nat.find_le hz (h:=ht); change j ≤ i at hj; omega), hh.symm ▸ Nat.find_spec ht, lt_of_not_ge (Nat.find_min ht (show j-1<j by omega))⟩ -- binder pos
include h
lemma log_raised : Tendsto (fun k=>Real.log (X k)) atTop atTop:= Real.tendsto_log_atTop.comp (Station.hat_rate K h)
lemma ember_mul (d:ℕ) : Tendsto (fun k=>s k* X k^d) atTop (𝓝 0):= by
   have H : Tendsto (fun k=> s k*(K.S.scale k)^d) atTop (𝓝 0):= by
       have hh:= (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp K.S.divergent; refine hh.congr fun i=>?_ ; change _*Real.exp _=_;rw [← Stock.a_log,mul_comm]
   let a:=G.slopeConstant+K.clock.bar; have ha : 0<a:= add_pos (Gauge.slopeConstant_pos h) K.clock.bar_pos
   refine squeeze_zero' ?_ ?_ (show Tendsto (fun k=> s k*(K.S.scale k)^d*(a^d)) atTop (𝓝 0) from (by simpa only [zero_mul] using H.mul_const (a^d)))
   · exact Eventually.of_forall fun k=> mul_nonneg (K.S.a_pos _).le (pow_nonneg (zero_le_one.trans (K.fits.delayed _).le) _)
   filter_upwards [K.S.divergent.eventually_ge_atTop 1] with i hi
   rw [mul_assoc,←mul_pow]; have hx := le_mul_of_one_le_left K.clock.bar_pos.le hi
   apply mul_le_mul_of_nonneg_left _ (K.S.a_pos _).le; exact pow_le_pow_left₀ (zero_le_one.trans (K.fits.delayed _).le) (by unfold a Calendar.hatBeta; linarith only [hx]) _
omit h in
lemma curtain (d:ℕ) (ζ k:ℝ) (hh:ζ>0)(hk: k>0) : ∀ᶠ i:ℝ in atTop, k* Real.log i^d ≤ ζ*Vac.Numbers.P i := by
   -- should omit h
   have hT:= Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop)
   filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0,hT.eventually_ge_atTop d,hT.eventually_ge_atTop (d+1:ℝ),hT.eventually_ge_atTop (Real.log (k/ζ))] with i hi hz hY hp
   set l:= Real.log (Real.log i)
   have hl:0<l:= lt_of_lt_of_le (by positivity) hY; apply (le_of_mul_le_mul_left (a:=ζ⁻¹) ?_ (inv_pos.mpr hh)); rw [← mul_assoc,inv_mul_eq_div, ← Real.exp_log (div_pos hk hh), ← Real.exp_log hi,← Real.exp_nat_mul,← Real.exp_add, Vac.Numbers.P, ← mul_assoc,inv_mul_cancel₀ hh.ne',one_mul]
   change Real.log (k / ζ) ≤ l at hp
   exact Real.exp_le_exp.mpr (by change _ + (d:ℝ)*l ≤ l^2; change (d:ℝ)+1 ≤ l at hY; nlinarith only [hp,mul_le_mul_of_nonneg_right hY hl.le])
end
end YM.OPE.Therm
