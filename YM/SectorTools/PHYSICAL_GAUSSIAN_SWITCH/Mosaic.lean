import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Bias
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.LocalLpWindows


/-!
# A real post-L physical application, fixed step

Finitely many columns of the centered window prescription at the ACTUAL
selected precision and mean source. `post` buys the estimates before V,
period, kernel and other history choices, all with the same kernel/frozen
geometry hypotheses as `purchase` and `Bias.sources_read`. x is hat
beta; no confusing it with beta in the stochastic/multiplier portions
(here g for the latter is tracked independently). Cost exponent fixed p;
must pay its threshold AFTER fixing p. No estimates from unrelated S.

No integrating V predicates or claiming same dV kernel if changing
prescription; this receipt is on the conditional law itself. For using
on a sector integral keep all original multiplier factors, chartCost and
permissions. -/
set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch.Mosaic
open Function Filter Set Matrix MeasureTheory
open Lattice Wilson RG Precision Exterior Tree Pressure Pressure.Stores Pressure.Tube Bid
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.SectorChange.Wisps Next.SectorChange.Schur
open AnalyticBridge.GaussianFieldAlignment
open AnalyticBridge.GaussianFieldAlignment.Relative (symPart sym_pours trade)
open ColumnCosts (License hybrid sumPrice)
open LocalLpWindows
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (A : Stores S) (F : Forest S.ratio)
  (x : ℝ) (V : Config G c) (k : S.Choices)
local notation "Area" => In (G:=G)
local notation "Covar" => Next.SectorChange.Gaussian.Table

def selected : Covar (Area x A F) := Rows.gram T x V k (shots S x) A F

def startWin : Covar (Area x A F) := per (panels A F) (selected T A F x V k)
def nextWin (X : Finset (Area x A F)) : Covar (Area x A F) := per (mosaicWindows A F x X) (selected T A F x V k)
def covNew (X : Finset (Area x A F)) : Covar (Area x A F) := clouded (mosaicWindows A F x X) (selected T A F x V k)
def centerNew (q : Push.SectorMeasure.Chi) (d : ℝ) (X : Finset (Area x A F)) (Y : LinkArray G (Frozen A x F)) : Prices G (Active A x F) :=
  -(nextWin T A F x V k X).transpose *ᵥ Rows.blame T x V k (shots S x) A F q d Y

/-- smallness of the ordered displacement retained; use as input even
to the tilted shift cost (other coupling factors still spent there)
-/
def decrease (M s x : ℝ) := 2*(M*Real.exp (-s*((radiusB x /60:ℕ):ℝ)))

/-- turn accepted Ready into actual license price for these comparators -/
lemma cash {s M η e : ℝ} (h : Ready A F x T k V s η M e) (hs : 0<s) (he : max 1 M * decrease M s x ≤ 1/2) :
    License (startWin T A F x V k) (per (mids A F x) (selected T A F x V k)) (front A F) s (max 1 M) (decrease M s x) := by
  let U:=startWin T A F x V k; let M' := selected T A F x V k; let V':=per (mids A F x) M'
  have hm:=h.ends; have ht:=h.mids; have hp:M≤max 1 M:=le_max_right ..
  change License U V' _ _ _ _
  have hx := ht.tail.bind (TableCosts.pour_neg hm.tail)
  refine ⟨?_,hm.pos,(sym_pours hm.order).weaker le_rfl hp,hm.charges.weaker le_rfl hp,le_max_left ..,hs.le,he⟩
  convert! hx using 1
  · abel
  unfold decrease; ring

lemma aft (p s M : ℝ) (hs : 0<s) : ∀ᶠ x in atTop,
    let K:=max 1 M; let δ:=decrease M s x
    K*δ ≤ 1/2 ∧ (2*K)*(2*p*(2*K^2*δ)) ≤ 1/4 := by
  have he : Tendsto (fun x => Real.exp (-s*((radiusB x /60:ℕ):ℝ))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hs)
      (tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp ?_)
    refine tendsto_atTop.mpr fun i => ?_
    filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (60*i)] with x hx
    omega
  have hx : Tendsto (fun x => decrease M s x) atTop (𝓝 0) := by simpa only [decrease,mul_zero] using! (he.const_mul M).const_mul 2
  let K:=max 1 M
  have hp : Tendsto (fun x => K * decrease M s x) atTop (𝓝 0) := by simpa only [mul_zero] using hx.const_mul K
  have ht : Tendsto (fun x => (2*K)*(2*p*(2*K^2*decrease M s x))) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((hx.const_mul (2*K^2)).const_mul (2*p)).const_mul (2*K)
  filter_upwards [hp.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2)), ht.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/4))] with x hh h
  exact ⟨hh,h⟩

/-- Exact comparison in the true Gaussian substitution space:
OLD with respect to new; this
is the direction that writes an existing calculation using the comparator.
Includes:
* recomputing the indicated window law only (same actual precision)
* exact spectral & integral price check on a Schur marginal
* post-L uniform `sumPrice` MGF estimate without even halo charge
* transfer of normalized expectations to the fresh mean/covariance
* the support charge if using the exact supported formula instead.
For WCs with p fixed. Other ancillary support lookups not included in this
charge.
-/
def StepResult (p M s C₀ : ℝ) :=
    let orig:=fog A F T x V k
    ∀ X : Finset (Area x A F), let newA:=covNew T A F x V k X
    let H:=haloSet A F x X; let e:=Embedding.subtype (·∈H)
    let P:=schurCov e orig; let D:=schurCov e newA
    let K:=max 1 M; let δ:=decrease M s x
    orig.PosDef ∧ newA.PosDef ∧ Elliptic K P ∧ Elliptic (2*K) D ∧
      ((mixed orig newA p).PosDef ∧ (mixed P D p).PosDef) ∧
      (H.card : ℝ) ≤ X.card * (LocalJet.chips S (radiusB x+2)*Fintype.card G.ColorIndex) ∧
      ∀ (q : Push.SectorMeasure.Chi) (d g : ℝ) (Y : LinkArray G (Frozen A x F)),0<d → 0<g →
        let m:=meanLog A F T x V k q d Y; let m':=centerNew T A F x V k q d X Y
        let z:=g⁻¹ • (m'-m); let t := C₀*(temp x+d); let r:=Real.conjExponent p
        price orig newA p z=price P D p (Support.pick e z) ∧
          price orig newA p z ≤ sumPrice p K δ g t X.card ∧
          ∀ f : Prices G (Active A x F) → ℂ, MemLp (fun a => f (m'+g • a)) (ENNReal.ofReal r) (cloud newA) →
          Integrable (fun a => f (m+g • a)) (cloud orig) ∧
          ‖∫ a,f (m+g • a) ∂cloud orig‖ ≤ sumPrice p K δ g t X.card ^ (1/p)*
            (∫ a, ‖f (m'+g • a)‖ ^ r ∂cloud newA) ^ (1/r)

-- avoid defeq between different inverses on large matrices
lemma deliver {p M s C₀ : ℝ} (hp : 1<p) (hl : License (startWin T A F x V k) (per (mids A F x) (selected T A F x V k))
    (front A F) s (max 1 M) (decrease M s x))
    (hδ : let K:=max 1 M; let δ:=decrease M s x; 2*K * (2*p*(2*K^2*δ))≤1/4)
    (hb : ∀ (q : Push.SectorMeasure.Chi) d (Y : LinkArray G (Frozen A x F)), 0<d →
      ‖Rows.blame T x V k (shots S x) A F q d Y‖ ≤ C₀*(temp x+d)) : StepResult T A F x V k p M s C₀ := by
  let Q:=selected T A F x V k; let U:=per (panels A F) Q; let N:=per (mids A F x) Q
  unfold StepResult
  intro orig X newA H e P D K δ
  have he : newA=symPart (hybrid U N X) := congr_arg symPart (mosaic _ _ _ _ X)
  have hnew := hl.positive X; have ho : orig=symPart U:=rfl
  have hn : Elliptic (2*K) newA := by rw [he]; exact hnew
  have hi : Elliptic K orig := hl.pure
  let hW:=columns_confined A F x Q X
  have hz := (ColumnCosts.paid hl hp.le hδ X (g:=1) (by norm_num) 0 (y:=0) (by simp)).1
  have hd : (mixed orig newA p).PosDef := by rw [he]; exact hz
  -- Pose on this exact e (so no unfold/identification across DecidableEq instances)
  have hh (g) (b : Vec (Area x A F)) :
      let z := ColumnCosts.delta U N X g b
      Sufficient (view (residual e newA)) orig (-z) newA 0 P D := by
    intro z
    unfold D; rw [he]
    apply ConfinedCovariance.reduces hl.pos (hl.positive X).posDef
    rw [zero_sub,neg_neg]; exact ColumnCosts.on_halo hW g b
  have ht : (mixed P D p).PosDef := ((hh 1 0).spectral_iff _).mp hd
  refine ⟨hl.pos,hn.posDef,hi.schur e,hn.schur e,⟨hd,ht⟩,halo_card _ _ _ X,?_⟩
  intro q d g Y hD hg m m' z t r
  let b:=Rows.blame T x V k (shots S x) A F q d Y
  have hf : m=ColumnCosts.mean U b:=rfl
  have hg' : m'=ColumnCosts.mean (hybrid U N X) b := by unfold m' centerNew nextWin; rw [mosaic]; rfl
  have hx : z=ColumnCosts.delta U N X g b := by unfold z ColumnCosts.delta; rw [hf,hg']
  have hv : ‖b‖ ≤ t := hb _ d _ hD
  let d' := ColumnCosts.delta U N X g b
  have hl' : ConfinedCovariance e orig newA (0-(-d')) := by rw [zero_sub, neg_neg,he]; exact ColumnCosts.on_halo hW g b
  have hL := (hh g b).price_eq ht
  have ha := ConfinedCovariance.marks (a:=-d') (d:=0) hn.posDef hl'.center
  change price orig newA p (0-(-d'))=_ at hL
  rw [ha, zero_sub,neg_neg] at hL
  refine ⟨by rw [hx]; exact hL, ?_,?_⟩ <;> rw [he]
  · rw [hx]; exact (ColumnCosts.paid hl hp.le hδ X hg b hv).2
  rw [hf,hg']; exact fun f => ColumnCosts.normalized hl hp hδ X hg b hv f

/-- Post-L production with the accepted phase/flags conventions. Constants
don't depend on period, β (which is not tested here), branches selected,
number of changed columns, realized V, etc. Keep permit hypotheses when using.
-/
theorem post (p : ℝ) (hp : 1<p) (P : Teller G) (d : Patch) (hb : d.Branches P.bind G) :
    ∃ M s C : ℝ,0<M ∧ 0<s ∧ 0≤C ∧ ∀ᶠ x in atTop,
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=d → Larger (G:=G) S → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
      ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices), A.flags=RG.flags (temp x) V →
        StepResult T A F x V k p M s C := by
  obtain ⟨s,η,M,e,hs,_,hm,_,h⟩ := purchase P d hb
  obtain ⟨C,hC,hb'⟩:=Bias.sources_read d P hb
  refine ⟨M,s,C,hm,hs,hC,?_⟩
  filter_upwards [aft p s M hs,h,hb'] with x ht hv hT
  intro c f S T hd hL hg hP A F V k hA
  obtain ⟨h1,h2⟩ := ht
  exact deliver T A F x V k hp (cash _ _ _ _ _ _ (hv _ _ _ _ hd hL hg hP A F k V (Or.inl hA)) hs h1) h2
    (hT S T hd hg hP A F k V hA)
end YM.SectorTools.PhysicalGaussianSwitch.Mosaic
