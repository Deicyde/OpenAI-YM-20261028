import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.AddressGap
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.IndexCost
import YM.Next.BOUNDARY.Core

/-!
# Buy the precision gap in actual geometry

Not a premise about the result of a Gaussian integration. Even when
ALL links frozen, provides invertibility and uniform bottom. The E02
contract is specialized at the gauge site, including periodic side test.
Supports used even in nonzero-derivative tests; no assumption of a count
bound based on number of possible root *choices*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Turn
open Matrix Work.F03 Progress.StationaryScenes Push.AbsoluteSums Tree Next.Fluctuations
open Win Finset Filter Green
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

def ode (u v : ℝ) := 2*(u*v)^2

def heel (D : Patch) (R : ℕ) := density_home D.L*(1+(R:ℝ))^4

lemma inflow (P : Teller G) (D : Patch) (x : ℝ) (T : Tube G S) (F : Forest S.ratio)
    (A : Stores S) (v : ArrayR G f) (V : Config G c) {t : ℝ} (hu : Warning P D t)
    (hD : S.patch=D) (hh : P.Funds S T) {C : ℝ} (hC : 0≤C) (s : S.Choices)
    (hE : ∀ U : Config G f, SliceSet S F U → ∀ e : Bond f, usable S U (home S e) s →
      Bid.Cops U (S:=S) 1 (S.prediction U s) e C) (hf : A.flags=RG.flags (temp x) V)
    (hb : ∀ i : Vars G f, i.1∉activeB A F (radiusB x) → v i=0)
    (hR : endowment D+1 ≤ radiusB x) (he : 2*(endowment D+1)<c.val) :
    let δ := tariff (endowment D+1) x
    let W := Dmat T F x A V *ᵥ v; let Y := debit P D C
    dotProduct v v ≤ ode Y (Real.sqrt weight)⁻¹ * heel D (city D) * dotProduct W W +
      ode Y (t*δ) * heel D (endowment D) * dotProduct v v := by
  intro δ W Y
  let Dp := ode Y (Real.sqrt weight)⁻¹
  let Dt := ode Y (t*δ)
  have hl : 0 ≤ Dp := mul_nonneg (by norm_num) (sq_nonneg _)
  have hz : 0 ≤ Dt := mul_nonneg (by norm_num) (sq_nonneg _)
  let a (e : Bond f) := ‖lie v e‖; let b (e : Pos S) := ‖descend W e‖
  let I := purse (base S) b (city D); let J := purse (home S) a (endowment D)
  have hx : ∀ i : Bond f, a i^2 ≤ Dp*I (home S i)^2 + Dt*J (home S i)^2 := by
    intro i
    by_cases h : i∈activeB A F (radiusB x)
    · have hr := expense P D x T F A v V i hu hD hh hC s (fun U H => hE U H i) hf hb h hR he
      let p := I (home S i); let q := J (home S i); let z := (Real.sqrt weight)⁻¹
      change a i ≤ Y*(z*p+t*δ*q) at hr
      apply (pow_le_pow_left₀ (norm_nonneg _) hr 2).trans
      change _ ≤ 2*(Y*z)^2*p^2 + 2*(Y*(t*δ))^2*q^2
      nlinarith only [sq_nonneg (Y*(z*p-t*δ*q))]
    have hy : lie v i = (0:G.Color) := by ext j; exact hb (i,j) h
    unfold a at *
    rw [hy,norm_zero,zero_pow (by decide : 2≠0)]; positivity
  have hm : governs (home S) (density_home D.L) := by rw [← hD]; exact governs_home _
  have he₁ : ∑ i,a i^2=dotProduct v v := descend_sq v
  have he₂ : ∑ i,b i^2=dotProduct W W := descend_sq W
  calc
    _ = ∑ i,a i^2 := he₁.symm
    _ ≤ ∑ i : Bond f,(Dp*I (home S i)^2+Dt*J (home S i)^2) := sum_le_sum fun i _ => hx i
    _ ≤ _ := by
      rw [sum_add_distrib,← Finset.mul_sum, ← Finset.mul_sum]
      refine add_le_add ?_ ?_
      · apply le_trans (mul_le_mul_of_nonneg_left (whole (home S) (base S) b (city D) _ hm) hl)
        rw [he₂,← mul_assoc]; rfl
      apply le_trans (mul_le_mul_of_nonneg_left (whole (home S) (home S) a (endowment D) _ hm) hz)
      rw [he₁,← mul_assoc]; rfl

-- bank uses Tendsto only on fixed Patch; NOT volume-dependent threshold.
lemma surplus (P : Teller G) (D : Patch) (h : D.Branches P.bind G) :
    ∃ r : ℝ, 0<r ∧ r≤1 ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch=D →
      100*(1+radiusB x) ≤ c.val →
      ∀ (F : Forest S.ratio) (A : Stores S) (V : Config G c), A.flags=RG.flags (temp x) V →
      ∀ (v : ArrayR G f), (∀ i : Vars G f,i.1∉ activeB A F (radiusB x) → v i=0) →
      let W := Dmat T F x A V *ᵥ v
      r*dotProduct v v ≤ dotProduct W W := by
  obtain ⟨C,hC,he⟩ := Work.E02.answer G D.L D.J P.bind
  obtain ⟨t,ht,hW⟩ := warning P D h
  let Y := debit P D C; let K := endowment D
  let V := ode Y (Real.sqrt weight)⁻¹ * heel D (city D)
  let r := (2*(1+V))⁻¹
  have hv : 0 ≤ V := by unfold V ode heel density_home; positivity
  have hr : 0<r := by unfold r; positivity
  have ht : r ≤ 1 := by unfold r; rw [inv_le_one₀ (by positivity : 0<2*(1+V))]; linarith
  let a x := tariff (K+1) x
  have hh : Tendsto a atTop (𝓝 0) := by
    have hf : Tendsto temp atTop (𝓝 0) := by simpa using Work.E09.radiusB_temp 0
    let v := 16*(2*((K+1:ℕ):ℝ)+1)^5 * (Fintype.card PlaqAxes:ℝ)
    simpa only [mul_zero,a,tariff,v] using! hf.const_mul v
  have hk : Tendsto (fun x => ode Y (t*a x)*heel D K) atTop (𝓝 0) := by
    have hu := (((((hh.const_mul t).const_mul Y).pow 2).const_mul 2).mul_const (heel D K)); simpa [ode] using hu
  refine ⟨r,hr,ht,?_⟩
  filter_upwards [hk.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)),
    Work.E01.radiusB_tendsto.eventually_ge_atTop (K+macroR D+1)] with x hx hR c f S T hF hD hS F A U ha v hV W
  have hs : ∀ s : S.Choices, ∀ u : Config G f, SliceSet S F u → ∀ e : Bond f,
      usable S u (home S e) s → Bid.Cops u (S:=S) 1 (S.prediction u s) e C := by
    intro s u hu e ht
    have hl : c.val ≤ f.val := S.sizes ▸ le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property
    exact he c f S hF.knobs (congr_arg Patch.L hD) (congr_arg Patch.J hD) (by rw [hD]; omega) (by omega)
      F u hu 1 e s ht
  let s : S.Choices := Classical.ofNonempty
  have hh := inflow P D x T F A v U hW hD hF hC.le s (hs s) ha hV (show K+1≤radiusB x by omega)
    (show 2*(K+1)<c.val by omega)
  have hq : 0 ≤ dotProduct v v := Centered.dot_nonneg _
  have hp : 0 ≤ dotProduct W W := Centered.dot_nonneg _
  change dotProduct v v ≤ V*dotProduct W W+ode Y (t*a x)*heel D K*dotProduct v v at hh
  change ode Y (t*a x)*heel D K < 1/2 at hx
  have hy := mul_le_mul_of_nonneg_right hx.le hq
  unfold r; rw [← div_eq_inv_mul]; apply (div_le_iff₀ (by positivity : 0<2*(1+V))).2
  linarith

section projections

variable (F : Forest S.ratio) (A : Stores S) (x : ℝ)

def mute (v : ArrayR G f) (j : Vars G f) := if j.1∈activeB A F (radiusB x) then v j else 0
def dormant (v : ArrayR G f) := v - mute F A x v

lemma split_sq (v : ArrayR G f) : dotProduct v v=dotProduct (mute F A x v) (mute F A x v)+
    dotProduct (dormant F A x v) (dormant F A x v) := by
  unfold dotProduct
  rw [← sum_add_distrib]; apply sum_congr rfl; intro i _
  by_cases h : i.1∈activeB A F (radiusB x) <;> simp [dormant,mute,h]

lemma vertical (T : Tube G S) (V : Config G c) (v : ArrayR G f) :
    let W := Dmat T F x A V
    W *ᵥ v = W *ᵥ mute F A x v := by
  intro W; funext i; unfold Matrix.mulVec dotProduct; refine sum_congr rfl ?_; intro j _
  by_cases h : j.1∈activeB A F (radiusB x) <;> simp [W,mute,Dmat,h]

lemma decomposes (T : Tube G S) (V : Config G c) (v : ArrayR G f) :
    let a := dormant F A x v; let y := Dmat T F x A V *ᵥ v
    dotProduct v (gram T F x A V *ᵥ v)=dotProduct y y + dotProduct a a := by
  intro a y; dsimp only [gram]; rw [Matrix.add_mulVec,dotProduct_add, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]; congr 1
  unfold a dotProduct; apply sum_congr rfl; intro i _
  rw [Matrix.mulVec_diagonal]; by_cases H : i.1∈activeB A F (radiusB x) <;> simp [dormant,mute,H]
end projections

theorem bedrock (P : Teller G) (D : Patch) (h : D.Branches P.bind G) :
    ∃ M : Win.Promise, ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
      P.Funds S T → S.patch=D → 100*(1+radiusB x) ≤ c.val →
      ∀ (F : Forest S.ratio) (A : Stores S) (V : Config G c), A.flags=RG.flags (temp x) V →
      M.Served (gram T F x A V) (dcol S) := by
  obtain ⟨r,hr,ht,hh⟩ := surplus P D h
  obtain ⟨W,hW,hC⟩ := gram_budget P D h
  let y := 1+density_variables G D.L
  have hy : 0 ≤ density_variables G D.L := by unfold density_variables density_home; positivity
  refine ⟨⟨W^2+1,r,P.top.width/2,y,by positivity,hr,half_pos P.top.width_pos,by unfold y; positivity⟩,?_⟩
  filter_upwards [hh] with x hx c f S T hT hS hF F A V ht'
  refine ⟨steal T A F x V,fun v => ?_,fun i M => ?_,(hC c f S T hT hS F A V x).price⟩
  · rw [decomposes, split_sq F A x v, mul_add, vertical F A x T V v]
    refine add_le_add (hx _ _ S T hT hS hF F A V ht' (mute F A x v) (fun i hi => by simp [mute,hi]))
      (mul_le_of_le_one_left (Centered.dot_nonneg _) ht)
  apply (governs_vars S i M).trans; rw [hS]; gcongr
  unfold y; linarith
end YM.AnalyticNext.ConnectedActivity.Aff
