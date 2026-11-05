import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Gains
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Year


/-!
# Ticket payments for fixed derivative budgets

Same M and room(tag layout, reserves) independent of y chosen *before*
period. Motion prices e.g. from position_move or radial_move. A supplier
only furnishes Knew on the actual fixed record at the Price. No inverse
prices (input to the pricing theorem); no chosen period. `radiusB x`
growing to pay long-label over all possible addresses, as always for these
sector-level estimates. No prices from any implicit limit of measures.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet.Physical
open Function Filter Set Matrix MeasureTheory Lattice RG Wilson Pressure Tree
open Next.SectorChange Completion FreeResolvent Ink TestD Differential
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {σ M η ε v U a C d b b' x : ℝ} {k l B : ℕ}

def faceBudget (σ M η : ℝ) (k : ℕ) := cash (room σ M η k) k

/-- Compact bill. Joint across both alphabets and root tests.
Buyer in `march_future` below. -/
structure Stipend (G : Gauge) (S : StepData c f) (l k : ℕ) (a σ M η U C b b' d : ℝ) (B : ℕ) : Prop where
  left : 1 ≤ C
  orig : 0<σ
  limit : 0≤M
  root : 0<η
  paid : 1≤U
  /-- price after budget. -/
  charge : Speech.drawer M η U (ceiling G S.patch (room σ M η k)) k *
    Real.exp (-(k+1:ℕ)*room σ M η k*((B/60:ℕ):ℝ)) ≤ currency b B
  lip : M ≤ C
  stay : meter k k M U (rise (ceiling G S.patch (room σ M η k)) η) ≤ C
  draw : ceiling G S.patch (room σ M η k)*meter k k M U (rise (ceiling G S.patch (room σ M η k)) η) ≤ C
  binds : multiplier U k*currency b B ≤ currency b' B
  goods : 120 ≤ B
  worthy : currency b B < 1
  width : multiplier U k * currency b B * ceiling G S.patch (faceBudget σ M η k)<1
  size : parcel G S l a (faceBudget σ M η k) C b' d B 0
  size' : parcel G S l a (faceBudget σ M η k) C b' d B 1

lemma march_future (G : Gauge) (P : Patch) (hs : 0<σ) (hm : 0≤M) (he : 0<η) (k : ℕ) (h : 1≤ U)
    {l : ℕ} (hl : 1 ≤ l) {a : ℝ} (hn : 0 ≤ a) : ∃ C b b' d : ℝ, 1 ≤ C ∧ 0 < b ∧ 0 < b' ∧ 0 < d ∧
      ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f), S.patch=P →
        Stipend G S l k a σ M η U C b b' d (radiusB x) := by
  let y:=room σ M η k
  let v:=faceBudget σ M η k
  let L:=ceiling G P y; let L' := ceiling G P v
  have ht : 0<y := (room_grid hs hm he k).1
  have hv : 0<v := cash_pos k ht
  let T:= meter k k M U (rise L η)
  let C:=max 1 (max (max M T) (L*T))
  have hc : 1≤C := le_max_left ..
  let R := Speech.drawer M η U L k
  have hT : 0≤ T := meter_nn _ _ hm (zero_le_one.trans h) (rise_nn (ceiling_nn ..) he)
  have hR : 0 ≤ R := by
    have hh := tag_poss h hm (mul_nonneg (ceiling_nn P G y) hT) k
    exact add_nonneg hh (tag_poss h hm (tag_poss h hT hh k) k)
  let r : ℝ := ((k+1:ℕ):ℝ)*y/120
  have hr : 0 < r := by unfold r; positivity
  let b:=r/2; let b':=b/2
  have hb : 0 < b := half_pos hr; have hb' : 0 < b' := half_pos hb
  let d:=b'/2; let θ:=d/2/(l+2:ℕ)
  have hd : 0<d := half_pos hb'
  have hθ : 0<θ := by unfold θ; positivity
  have hN : θ*((l+2:ℕ):ℝ)=d/2 := div_mul_cancel₀ _ (by positivity)
  have ht' : θ<b' := by unfold d at *; push_cast at *; nlinarith only [hb',hN,hθ,mul_nonneg hθ.le (show 0≤(l:ℝ) by positivity)]
  have hy (n : ℕ) (hj : n ≤ 1) := worth a l n (ceiling_nn P G θ) (show 0 ≤ L' from ceiling_nn ..) (zero_le_one.trans hc)
    ht' (show d < b'-θ*((n+1+l:ℕ):ℝ) by
    have he : θ*((n+1+l:ℕ):ℝ) ≤ d/2 := by rw [← hN]; apply mul_le_mul_of_nonneg_left _ hθ.le; exact_mod_cast (show n+1+l ≤ l+2 by omega)
    unfold d at *; linarith)
  have hx : Tendsto (fun x=>multiplier U k * currency b x * L') atTop (𝓝 0) := by simpa only [mul_zero,zero_mul] using!
    (((currency_small hb).const_mul (multiplier U k)).mul_const L')
  refine ⟨C,b,b',d,hc,hb,hb',hd, Work.E01.radiusB_tendsto.eventually (p:=fun B => ∀ {c f : Side} (S : StepData c f), S.patch=P → Stipend G S l k a σ M η U C b b' d B) ?_⟩
  filter_upwards [eventually_ge_atTop 120, currency_eventual (show b<r from half_lt_self hr) R,
    currency_eventual (show b'<b from half_lt_self hb) (multiplier U k), (currency_small hb).eventually (gt_mem_nhds zero_lt_one),
    hy 0 (by omega),hy 1 le_rfl, hx.eventually (gt_mem_nhds zero_lt_one)] with B hB hx hr hp hj hJ hz
  intro c f S HE
  subst P
  have hi (n : ℕ) (hh : pass L' (currency b' B) a θ l B < 1) (he : totalCost n L' (ceiling G S.patch θ) C (currency b' B) a θ l B ≤ currency d B) :
      parcel G S l a v C b' d B n := by
    intro s
    obtain ⟨ha,hy,hQ⟩ := Counting.passports hv.le (zero_le_one.trans hc) (currency_pos b' B).le (by omega) hl hn hθ.le (ceiling_nn S.patch G v)
       (audience S G hv) (audience S G hθ) hh n s
    exact ⟨ha,hy,hQ.trans he⟩
  refine ⟨hc,hs,hm,he,h,le_trans ?_ hx,le_max_of_le_right ((le_max_left M T).trans (le_max_left ..)),
    le_max_of_le_right ((le_max_right M T).trans (le_max_left ..)),le_max_of_le_right (le_max_right ..),hr,hB,hp,hz,
      hi _ hj.1 hj.2, hi _ hJ.1 hJ.2⟩
  apply mul_le_mul_of_nonneg_left _ hR; apply Real.exp_monotone
  have ht' : (B:ℝ) ≤ 120*((B/60:ℕ):ℝ) := by exact_mod_cast (show B ≤ 120*(B/60) by omega)
  let w:= (k+1:ℕ)*y
  have hf : 0≤w := mul_nonneg (by positivity) ht.le
  rw [neg_mul,neg_mul]; change -(w*_) ≤ -(w/120)*_
  linarith only [mul_le_mul_of_nonneg_left ht' hf]

namespace Stipend
variable (J : Stipend G S l k a σ M η U C b b' d (radiusB x))
include J
lemma apertureRoom (i j : Key G f) (he : i ∉ windows S x j) :
    radiusB x/60 ≤ separation (place S j) (place S i) := Nat.le_of_not_ge (mt (near_contains J.goods) he)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {τ : Type*} {H : Mark τ (Site c)} {v : τ → E} {A : E → Square (Key G f)} {z : E}

lemma treasury (h : Knew H (native c) (place S) v z k σ M η ε A) (hi : 0≤ε) (he : ε≤1)
    (hs : ∀ᶠ y in 𝓝 z, (A y).IsHermitian) (hM : H.Move (native c) (faceBudget σ M η k) U) :
    Speech (native c) (place S) (windows S x) H v A z k (faceBudget σ M η k) U C (currency b (radiusB x)) ε := by
  let r := room σ M η k; let L:=ceiling G S.patch r
  have hp : Price σ M η r U L ε k := ⟨J.root,J.limit,J.orig,rfl,J.paid,ceiling_nn S.patch G r,hi,he⟩
  refine Speech.display h hs hp hM (audience S G hp.pos) (centered J.goods) ?_ J.left J.lip J.draw J.stay
    ((mul_comm ..).trans_le J.charge)
  intro i j hh
  have he := J.apertureRoom j i (fun hx => hh ⟨⟨j,hx⟩,rfl⟩)
  change (↑(radiusB x/60:ℕ):ℝ) ≤ (separation (place S i) (place S j):ℝ)
  exact_mod_cast (show radiusB x/60 ≤ separation (place S i) (place S j) from he)

end Stipend
end YM.AnalyticBridge.RelativeLogdet.Physical
