import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Source
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tablets
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Stagecraft
import YM.PhysicalNext.PHYSICAL_JOINT_ENDPOINT_LOAD_F16.DLog.Fund
import YM.Push.RELAY_DIFFERENCE.Dictionary

/-!
# Pay arithmetic for the hat-relative physical Q/y addressing

No volume/storage tax. Just rank-zero post-L (can spend powers of **x**
after tower choices). Uses micro broad, never calls E at χ. ETA adjusted
with the very same forest & mean, no symmetric modification of μ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Barge
open Lattice Wilson Pressure RG RG.Supply Matrix Finset Filter Tree
    Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Pressure.Stores
    Function AnalyticBridge.RelativeLogdet Physical Push.AbsoluteSums FreeResolvent
    AnalyticBridge.LocalGaussianLaws Dictionary Dictionary.Wires Dictionary.Notify
    AnalyticBridge.MarginalMultiplier3b1d SourceBounds AnalyticNext.ConnectedActivity
    Wisps Next.SectorChange.Schur Gaussian PhysicalGuard7f546.Curved
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {V : Config G c} {P : Teller G} {D : Patch} {T : Tube G S} {x r : ℝ}
structure Sound (x β ℓ : ℝ) (T : Tube G S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices) (A : Stores S) (q : Chi) (d : ℝ) : Prop where
  taxes : Pours (fog A F T x V k) (Wisps.front A F) (Wisps.front A F) 0 ℓ
  lift (Y i) : |meanLog A F T x V k q d Y i| ≤ 1
  rows Y i : |Rows.direct T x V k (shots S x) A F q d Y (meanLog A F T x V k q d Y) i|≤1
  buzz Y i : |Rows.eta T x V k (shots S x) A F q d Y (meanLog A F T x V k q d Y) (coupling β) i| ≤ x^(-(4:ℝ))
  dust Y z : doors q d (displaced (meanLog A F T x V k q d Y) (coupling β) z) ≠ 0 → ∀ i, |z i| ≤ x^2

lemma dredge (P : Teller G) (D : Patch) (hp : D.Branches P.bind G) (hr :0≤r) : ∃ ℓ:ℝ, 1≤ℓ ∧
    ∀ᶠ x in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=D → P.Funds S T → 100*(1+radiusB x) ≤ c.val →
    ∀ β d, 0<β → β≤4*x → 0<d → d≤r*fiery G x D.L → ∀ (F : Forest S.ratio) (V : Config G c) (k : S.Choices) A q,
      Positioned x A V → Sound x β ℓ T F V k A q d:= by
  obtain ⟨η,K,u,v,hη,hK,hu,hv,H⟩:=kernel_post P D hp
  obtain ⟨Z,hZ,hS⟩:= source_bound P D hp hr
  obtain ⟨L,hL,hM⟩:= move_bound P D hp; let Y:=Z+K*(L*Z)+L*(K*(L*Z))+K*u*(L*Z)+2*r
  have hK' :0<K:= zero_lt_one.trans_le hK
  have ht : Tendsto (fun x=>Y*fiery G x D.L) atTop (nhds 0):= by simpa [Rates.allowance,Rates.pieces] using! (Rates.slow G D).const_mul Y
  refine ⟨K,hK,?_⟩
  filter_upwards [H,hS,hM, ht.eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num)),Lift.plume v 5 hv,eventually_ge_atTop (4:ℝ)] with x hx hS hM h hb hy c f S T he hT hN β d hβ hg hd hr' F V k A q hA
  let t:=fiery G x D.L; have ht:0≤t:=temp_nonneg _; change Y*t≤1 at h
  have hy' :0<x:=lt_of_lt_of_le (by norm_num) hy
  have hc:= signal_bound (q:=q) (d:=d) (hx S T he hN hT A F k V hA) (mul_nonneg hZ.le ht) hu.le ((hM S T he hN hT A F V k hA).weaker (by have h := P.top.width_pos; positivity) le_rfl) hβ
    (hS S T he hN hT A F V k hA d hd hr' q)
  obtain ⟨h1,h2,h3⟩:=hc
  have hΔ₁ :0<K*(L*Z):=by positivity
  have hΔ₂ :0<L*(K*(L*Z)):=by positivity
  have hΔ₃ :0<K*u*(L*Z):=by positivity
  let m Y:= meanLog A F T x V k q d Y; have hμ Y' i : |m Y' i| ≤ 1:= (h1 Y' i).trans ((le_of_eq (by ring : K*(L*(Z*t))=(K*(L*Z))*t)).trans ((mul_le_mul_of_nonneg_right (show K*(L*Z)≤Y by unfold Y; linarith only [hΔ₁,hΔ₂,hΔ₃,hZ,hr]) ht).trans h))
  let g:= coupling β; have he : 0<g:=coupling_pos hβ
  have hf:g⁻¹ ≤ x:= by unfold g coupling; rw [inv_inv]; nlinarith [Real.sq_sqrt hβ.le]
  refine ⟨(hx S T (by assumption) hN hT A F k V hA).2.1,hμ,fun Y' i => ?_,fun Y' i=> ?_,?_⟩
  · apply (h2 Y' i).trans (le_trans ?_ h)
    calc
      _ = (L*(K*(L*Z))+Z)*t:=by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by unfold Y; linarith only [hΔ₁,hΔ₂,hΔ₃,hZ,hr]) ht
  · apply (h3 Y' i).trans
    let E:= rate (-v) (radiusB x/60)
    have hw : E ≤ x^(-(5:ℝ)):= by
      apply le_trans _ hb; apply Real.exp_monotone
      apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hv.le); exact_mod_cast (show till x≤radiusB x/60 by unfold till; omega)
    calc
      _ = (K*u*(L*Z)*t)*(g⁻¹*E):=by change g⁻¹*(K*(u*E)*(L*(Z*t)))=_; ring
      _ ≤ 1*(x*x^(-(5:ℝ))):= mul_le_mul ((mul_le_mul_of_nonneg_right (by unfold Y; linarith only [hΔ₁,hΔ₂,hΔ₃,hZ,hr]) ht).trans h) (mul_le_mul hf hw (Wisps.rate_pos ..).le hy'.le) (mul_nonneg (inv_nonneg.mpr he.le) (Wisps.rate_pos ..).le) zero_le_one
      _ = _ := by norm_num only [one_mul]; nth_rw 1 [← Real.rpow_one x]; rw [←Real.rpow_add hy']; norm_num
  intro Y' z hx i; specialize hμ Y' i
  let u':=displaced (m Y') g z
  have hl:2*d ≤1:= (show 2*d ≤ 2*r*t by linarith only [show d ≤ r*t from hr']).trans ((mul_le_mul_of_nonneg_right (show 2*r≤Y by unfold Y; linarith only [hΔ₁,hΔ₂,hΔ₃,hZ,hr]) ht).trans h)
  have hz : |m Y' i+g*z i| ≤ 1:= (show _ ≤ ‖u' i.1‖ from PiLp.norm_apply_le _ i.2).trans ((broad_span q hd (u' i.1) (every_door q hx i.1)).le.trans hl)
  have hr' :|z i| ≤ 2*g⁻¹:= by
    rw [← div_eq_mul_inv, le_div_iff₀ he, mul_comm]; have he := abs_mul g (z i); rw [abs_of_pos (by assumption:0<g)] at he; rw [← he]; rw [abs_le]; constructor <;> linarith only [abs_le.mp hμ,abs_le.mp hz]
  nlinarith only [hr',hy,hf]
end YM.PhysicalNext.InteractingRank.Barge
