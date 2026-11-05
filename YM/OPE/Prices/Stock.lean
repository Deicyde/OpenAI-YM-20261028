import YM.OPE.Height
import YM.MergeProof.Strudel

/-!
# Origin receipts on varying array sizes including shrinking probes

Implements stock phase of Crew billing at the same position. See proofs in
`Overlay/Prior` and `Winter` for the fixed-source costs at chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Filter Function Set Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open scoped Topology
variable {G:Gauge}{C:Family G}{ι κ : Type*} {l : Filter ι} {f : Filter κ} {T : ι→ℝ} {a b c : ℝ}
variable {S : Schedule} {m k : ι→ℕ}
variable (t: Stock.Tabs C.path.levels)
lemma stock_fiat (C:Family G) (i:ℕ) : 1≤ Vac.fiat G (C.path.levels.params i) (C.path.levels.clock.hatBeta i) := by
    let b:=C.path.levels; unfold Vac.fiat; have he := (b.params i).paths_pos; have ha := (b.params i).clip.quadratic_pos; have hp : 0≤ (Fintype.card PlaqAxes:ℝ)*((b.params i).clip.direct + (b.params i).paths^2) +
      4*Module.finrank ℝ G.Mat*(Real.log 16+Real.log (b.clock.hatBeta i)/2) := by
      have hu := Real.log_pos (b.fits.delayed i)
      positivity
    linarith only [hp,he]
set_option quotPrecheck false
local notation "J"=> Stock.Tabs.chosen C.path.levels 1 t
local notation "P'"=> C.path.levels
lemma stock_step : Tendsto (fun i=> C.S.scale i/C.S.scale (J i)) atTop (𝓝 1):=by
    let x i:= C.S.scale (J i)
    let y:= C.S.scale
    have he(i): i ≤ J i:= (Stock.Tabs.opened _ _ _ i).1
    have hp:Tendsto J atTop atTop:= tendsto_atTop_mono he tendsto_id
    have hz:Tendsto x atTop atTop:= C.S.divergent.comp hp
    rw [tendsto_order]; constructor
    · intro r hr; obtain ⟨v,hv,hv'⟩:= exists_between (sub_pos.mpr hr);
      filter_upwards [Stock.Tabs.pay C.path.levels 1 t le_rfl v hv,hz.eventually_gt_atTop 0] with i hi ht
      rw [lt_div_iff₀ ht]
      let u := C.S.a i/C.S.a (J i)
      let B := Vac.fiat G (P'|>.params (J i)) (P'|>.clock.hatBeta (J i))
      have hs : 1≤u := (one_le_div (C.S.a_pos _)).2 (C.S.strictAnti.antitone (he i))
      have hF : x i-y i=Real.log u := by
         unfold x y Schedule.scale u; rw [Real.log_div (C.S.a_pos _).ne' (C.S.a_pos _).ne', Real.log_inv, Real.log_inv]; ring
      have hB : 1 ≤ B:= stock_fiat C _
      have hW : x i-y i ≤ v*x i:= by
         rw [hF]; calc
            _ ≤ u:= Real.log_le_self (by linarith)
            _ ≤ u^4 := by nth_rw 1 [← pow_one u]; exact pow_le_pow_right₀ hs (by norm_num)
            _ ≤ u^4*B:= le_mul_of_one_le_right (by positivity) hB
            _ ≤ _ := hi
      change r*x i < y i; linarith only [hW,mul_lt_mul_of_pos_right hv' ht]
    intro r hr; filter_upwards [hz.eventually_gt_atTop 0] with i hi using lt_of_le_of_lt ((div_le_one hi).2 ((scale_mono C.S).monotone (he i))) hr
lemma Height.stock (h:Height C.S l T m a) : Height C.S l T (fun i=> J (m i)) a:=by
    have hv i: m i ≤ J (m i):=(Stock.Tabs.opened ..).1
    refine ⟨tendsto_atTop_mono hv h.grows, ?_⟩
    have hx := h.pace.mul (((stock_step t).comp h.grows).inv₀ one_ne_zero)
    simp only [Function.comp_apply, inv_one,mul_one] at hx
    refine hx.congr' ?_; filter_upwards [(C.S.divergent.comp h.grows).eventually_gt_atTop 0] with i hi; change 0<C.S.scale (m i) at hi; rw [inv_div]; field_simp
lemma stock_price (hG:G.Simple) (h:Height C.S l T m a)(hT:Tendsto T l atTop) : RateLE l T (fun i=> stakes C (m i) (J (m i))) 0 :=by
    cases l.eq_or_neBot with
    | inl hh=> rw [hh]; intro r _; simp
    | inr hl =>
    let v i:= C.S.a (m i)/C.S.a (J (m i)); intro r hr; let u:=r/3/(1+a)
    have ha:=h.nonneg hT; have hf:0< u:= div_pos (by positivity) (by positivity); have hs :u*(a+1)+r/3 ≤ r:=by unfold u; rw [add_comm a 1, div_mul_cancel₀ _ (by linarith only [ha])]; linarith only [hr]
    filter_upwards [h.grows.eventually (Stock.Tabs.pay C.path.levels 1 t le_rfl u hf),
       (h.stock t).grows.eventually (Vac.treasury_stage C.path.levels hG),
       (h.stock t).pace.eventually (gt_mem_nhds (show a<a+1 by linarith)),hT.eventually_gt_atTop 0,(hT.const_mul_atTop (div_pos hr (by norm_num : (0:ℝ) < 3))).eventually_ge_atTop 5] with i hi hv he hT he'
    rw [stakes,Real.norm_of_nonneg (Real.exp_pos _).le]; apply Real.exp_monotone
    let z:= J (m i); have hZ:C.S.scale z /T i<a+1:= he; have hε:= le_of_lt ((div_lt_iff₀ hT).1 hZ); have hp:v i^4 * Vac.treasury (P') z ≤ u*C.S.scale z:= le_trans (mul_le_mul_of_nonneg_left hv (by positivity)) hi
    have he':= show (5:ℝ) ≤ (r/3)*T i from he'; change v i^4 * Vac.treasury _ z +_ ≤ _; linarith only [he',hp,mul_le_mul_of_nonneg_left hε hf.le, mul_le_mul_of_nonneg_right hs hT.le]
end YM.OPE
