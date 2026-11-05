import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.NearDelay
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Step
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Subtotal
import YM.Extra.ITERATION_NO_LOSS.Continuity


/-!
# Cost after log extension

τ_T,D here only at fixed smoothing step. x and gates after L.
Even if exact x sequence of a Pearl grows fast, provide these waits
prior to freezing Bars. Include true cutoff cost conversion in native
coarse radius (the full $x^{-7/8}$ BEFORE division by coupling).

Important: no conclusion on how many steps can be taken before using
these comparisons, or uniform epsilon over the smoothing history of
an already fixed Family--apply with actual delays later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Lift
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent Remote Extra.Iteration.Scales
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

-- arithmetic & placement. Avoid `Tiny cover` with shift here.
def BCost (x : ℝ) := 1+(radiusB x:ℝ)
lemma BCost_one (x : ℝ) : 1≤BCost x := le_add_of_nonneg_right (Nat.cast_nonneg _)
def boundaryCost (k : ℝ) (x : ℝ) := k*16*3^5*(Fintype.card PlaqAxes:ℝ)*BCost x^5
lemma boundary_small (k : ℝ) (hk : 0≤k) : Tiny id (boundaryCost k) :=
  Tiny.mul (Tiny.const tendsto_id _ (by positivity)) (Tiny.cover_size.pow tendsto_id 5) tendsto_id

lemma boundary_fit (x k : ℝ) (hk : 0≤k) : k*clearanceFare x ≤ boundaryCost k x*temp x := by
  unfold boundaryCost clearanceFare
  have ht:=temp_nonneg x
  have h : 2*((radiusB x+1:ℕ):ℝ)+1 ≤ 3*BCost x := by unfold BCost; push_cast; have hx : 0 ≤ (radiusB x:ℝ) := Nat.cast_nonneg _; linarith
  calc
    _ ≤ k*(16*(3*BCost x)^5*(Fintype.card PlaqAxes:ℝ)*temp x) := by gcongr
    _ = _ := by ring

lemma plume (a ε : ℝ) (ha : 0<a) : ∀ᶠ x : ℝ in atTop, Real.exp (-a*(till x)) ≤ x^(-ε) := by
  have ht := first (a/200000) ε (by positivity)
  filter_upwards [ht, Work.E01.radiusB_tendsto.eventually_ge_atTop 200000] with x hx hB
  apply le_trans _ hx; apply Real.exp_monotone
  have he : radiusB x ≤ 200000*till x := by unfold till; omega
  have hh : (radiusB x:ℝ) ≤ 200000*(till x:ℝ) := by exact_mod_cast he
  nlinarith [mul_le_mul_of_nonneg_left hh ha.le]

lemma boundary_limited (k : ℝ) (hk : 0≤k) : Tendsto (fun x => k*clearanceFare x) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (g:=fun x => x^(-(1/4):ℝ)) (tendsto_rpow_neg_atTop (by norm_num : 0<(1/4:ℝ)))
  · filter_upwards with x; unfold clearanceFare; have ht:=temp_nonneg x; positivity
  filter_upwards [eventually_gt_atTop (0:ℝ),boundary_small k hk _ (by norm_num : 0<(1/8:ℝ)), Work.E09.temp_cost (1/8) (by norm_num)] with x hx he hv
  exact (boundary_fit x k hk).trans ((mul_le_mul he.2 hv (temp_nonneg x) (by change 0≤x^(_ : ℝ); positivity)).trans_eq (by change x^(1/8:ℝ)*(x^(_ : ℝ))=_; rw [← Real.rpow_add hx]; norm_num))

-- one x payment (k costs the log extension; don't apply this to the group
-- if reordering beta steps before reading receipts.)
lemma pay_mean (G : Gauge) (P : Patch) (k A X s E N M τ : ℝ) (hk : 0≤k) (hs : 0<s) (hτ : 0<τ) (hA : 0≤A) (hX : 0≤X) (hN : 0≤N) (hM : 0≤M) (hE : 0≤E) :
    ∀ᶠ x : ℝ in atTop,
      let t := k*clearanceFare x
      let D:= pieces P G*LocalJet.grain (span P x)
      N*(D*M*(A*t*widen (till x) t τ))+M*(E*Real.exp (-s*(radiusB x)))*(X*t) ≤ x ^ (-(7/8):ℝ) := by
  -- tiny all multiplier factors including grain
  let B:=boundaryCost k
  have hB := boundary_small k hk
  let C:=pieces P G
  let d (x) := (3*BCost x)^4
  have H := ((Tiny.mul (Tiny.const tendsto_id 3 (by norm_num)) (Tiny.cover_size) tendsto_id).pow tendsto_id 4)
  have Hd : Tiny id d := H
  let Y x:=N*C*d x*M*A*B x*(BCost x*B x)+N*C*d x*M*A*B x+M*E*X*B x
  have hh : Tiny id Y := by
    have hC0 := pieces_nonneg P G
    let hC1 := Hd
    let H : Tiny id (fun x => N*C*d x*M*A*B x) := Tiny.mul (Tiny.mul (Tiny.mul (Tiny.mul (Tiny.const tendsto_id _ (mul_nonneg hN hC0)) Hd tendsto_id) (Tiny.const tendsto_id _ hM) tendsto_id) (Tiny.const tendsto_id A hA) tendsto_id) hB tendsto_id
    exact ((Tiny.add ((H.mul (Tiny.mul Tiny.cover_size hB tendsto_id) tendsto_id)) H tendsto_id).add (Tiny.mul (Tiny.const tendsto_id _ (by positivity)) hB tendsto_id) tendsto_id)
  filter_upwards [eventually_gt_atTop (1:ℝ), small_span P, plume τ 1 hτ,
    hh _ (by norm_num : 0<(1/16:ℝ)), first s 1 hs, Work.E09.temp_cost (1/32) (by norm_num)] with x hx hh0 hp hy he ht
  intro t D
  have h₁:=BCost_one x; have h₀ : 0 ≤ B x := by unfold B boundaryCost; positivity
  have h₂ : LocalJet.grain (span P x) ≤ d x := by
    unfold LocalJet.grain d BCost; push_cast; gcongr; have hh : (span P x:ℝ) ≤ radiusB x := by exact_mod_cast hh0.trans (by omega : radiusB x/50≤radiusB x)
    linarith only [hh,Nat.cast_nonneg (α:=ℝ) (radiusB x)]
  let u:=x^(-(1/2:ℝ)+(1/32:ℝ)); have ht' : t ≤ B x*u := (boundary_fit x k hk).trans (mul_le_mul_of_nonneg_left ht h₀)
  have hu : 0 ≤ u := by unfold u; positivity
  have hz : 0 ≤ t := by unfold t clearanceFare; have ht := temp_nonneg x; positivity
  have h : x^(-1:ℝ) ≤ u := Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
  have hd : (till x:ℝ) ≤ radiusB x := by exact_mod_cast (show till x ≤ radiusB x by unfold till; omega)
  have hd' : (1+(till x:ℝ)) ≤ BCost x := by unfold BCost; linarith only [hd]
  have hv : widen (till x) t τ ≤ BCost x*(B x*u)+u := add_le_add (mul_le_mul hd' ht' hz (zero_le_one.trans h₁)) (hp.trans h)
  have hC : 0≤C := pieces_nonneg ..
  have hn := widen_nonneg (till x) (τ:=τ) hz
  have hd : 0≤d x := by unfold d; positivity
  calc
    _ ≤ N*((C*d x)*M*(A*(B x*u)*(BCost x*(B x*u)+u)))+M*(E*u)*(X*(B x*u)) := by unfold D; gcongr; exact he.trans h
    _ = (Y x)*u*u := by unfold Y; ring
    _ ≤ (x^(1/16:ℝ))*u*u := by gcongr; exact hy.2
    _ = _ := by unfold u; simp_rw [← Real.rpow_add (zero_lt_one.trans hx)]; norm_num
variable {G : Gauge}
theorem mean_shot (G : Gauge) (P : Patch) (Pt : Teller G) (h : P.Branches Pt.bind G) :
    ∃ K : ℝ, 1≤K ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Booth Pt S T →
    100*(1+radiusB x)≤c.val →
    ∀ (U : Stores S) (o : Site c), Clears U x o (radiusB x) → ∀ V : Config G c, U.flags=RG.flags (temp x) V →
      (∀ i : Bond c, separation o i.1≤radiusB x → G.chord (V i)≤clearanceFare x) →
      Remote.paid S (replica S.ratio V) o (radiusB x) (clearanceFare x) →
      ∃ v : Dir G c, (AgreeNear id o (radiusB x) V (represent v) ∧ ‖v‖ ≤ K*clearanceFare x) ∧
      ∀ (F : Forest S.ratio) (k : S.Choices) (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen U x F)),
      let a:=marked U x F (doc T F v)
      ∀ i : In x U F (G:=G), separation o (front U F i) ≤ radiusB x/4 → ∀ g : Assembly.Geometry,
        let Q:=Rows.gram T x V k (shots S x) U F; let b:=blame T x V k (shots S x) U F q d Y
        let ν:=pane (Assembly.sectorW G S x U F g) Q 0
        let M := match g with | .endpoint => meanLog U F T x V k q d Y | .midpoint => midLog U F T x V k q d Y
        offCenter ν b=M ∧ |M i-a i| ≤ x ^ (-(7/8):ℝ) := by
  obtain ⟨A,X,s,E,N,M,τ,δ,hA,hX,hs,hE,hN,hM,hτ,hδ,H⟩ := focused G P Pt.bind Pt h rfl
  obtain ⟨C,b,hC,hb,hB⟩ := extend_interior G; let K:=max 1 C
  have hK : 1≤K := le_max_left ..
  have hK' : 0≤K := zero_le_one.trans hK
  refine ⟨K,hK,?_⟩
  filter_upwards [H, pay_mean G P K A X s E N M τ hK' hs hτ hA hX (zero_le_one.trans hN) (zero_le_one.trans hM) hE,
    (boundary_limited K hK').eventually (ge_mem_nhds (lt_min hb hδ))] with x H he hp
  intro c f S T hP hT hF U o hh V hV hQ hD
  let t:=K*clearanceFare x; have h0 : 0 ≤ clearanceFare x := by unfold clearanceFare; have := temp_nonneg x; positivity
  have ht : 0≤t := mul_nonneg hK' h0
  have he' : clearanceFare x≤t := le_mul_of_one_le_left h0 hK
  obtain ⟨v,hv,hz⟩ := hB id o (radiusB x) V _ h0 (he'.trans (hp.trans (min_le_left ..))) hQ
  have hw : Remote.paid S (replica S.ratio V) o (radiusB x) t := fun i hi => (hD i hi).trans he'
  have hX : ‖v‖ ≤ t := hv.trans (mul_le_mul_of_nonneg_right (le_max_right ..) h0)
  refine ⟨v,⟨hz,hX⟩,fun F k q d y => ?_⟩
  intro a i hi g Q b ν M'
  have hx := H t ht (hp.trans (min_le_right ..)) S T hP hT hF U o F hh V hV v hX hw hz k q d y i hi g
  have h : offCenter ν b=M' := by cases g; unfold ν; rw [pane_zero]; rfl; rfl
  change _ ∧ |_ - marked U x F (doc T F v) i| ≤ _
  rw [← h]; exact ⟨rfl,hx.trans he⟩
end YM.AnalyticBridge.LocalGaussianLaws.Lift
