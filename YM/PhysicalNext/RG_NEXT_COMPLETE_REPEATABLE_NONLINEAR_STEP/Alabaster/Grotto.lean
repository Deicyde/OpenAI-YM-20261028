import YM.Further.CURVED_GAUSSIAN_JETS.Centers
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Alarum
/-!
 # Simultaneous sector integral tag comparisons through bill (orig flag Convention).
 Uniform over ALL θ and choices; purchase on Works after delay, rates. Needs actual grant
 as from H for underlying data. Not promising Gram equivalence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ} {x d μ C : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R : RG.Rep G f} (H : Cash W x μ L Q o C T R)
section bounds
variable (T)
/- rough second comparison receipt PACK normalized. -/
def Covers (T : Tube G S) (p : ℝ) (_H : Cash W p μ L Q o C T R) := ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (F:Forest S.ratio) (X:Coat T F), X.width=o.K → X.x=p → X.manifest → ∀ (I : RG.Rep G f) (a b : ℕ→ℝ) (t:ℝ), Equalized Q.table R I a b t→ t ≤ 1 → t ≤ R.beta/2 →
    ∀ (u : Directions G f) (s : Stores S) (l : Finset ℕ), |X.Pack I Q.table l W o.a s u-X.Pack R Q.table l W o.a s u| ≤ C'*t
lemma ired (P : Teller G) (D : Patch) (L : Side) (hd : D.Branches P.bind G) (W : ℝ) (o : Target.Order G W) (Q : ConnectedActivityE6.Target G P) : ∀ᶠ x in atTop,
    ∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D→ ∀ (R:RG.Rep G f) (μ C:ℝ) (H : Cash W x μ L Q o C T R), Covers T x H:= by
  obtain ⟨A,U,hA,hU,hV⟩ := max_prices P
  let a:= o.a; let f x:= (2*a)*Pressure.fiery G x L; have ha : 0 < a:= o.large
  obtain ⟨E,hE,H⟩ := Coat.earns P L D hd A hA (w:=f) (Rate.flame.mul_left _) (Eventually.of_forall fun x=> mul_nonneg (by positivity) (by unfold Pressure.fiery temp; positivity))
  obtain ⟨M,hM,hP⟩:= germ_charge Q.table_exists L o.large
  filter_upwards [H,hV L,hP] with p hp hx hs c f' S T hS R μ C H
  let n : ℝ := Fintype.card (Bond f'); let z:= univ.sup fun i: Stores S=>i.shares; let v : ℝ := z
  have hv:0 ≤ v:=Nat.cast_nonneg _; have hn:0 ≤ n:=Nat.cast_nonneg _; have hl (i:Stores S) : (i.shares:ℝ)≤ v := by unfold v; exact_mod_cast Finset.le_sup (f:=Stores.shares) (mem_univ i)
  let b x:= Real.log (measure_g Q.table x); let h:=H.laws.data; have hL:= h.funds.length_eq
  let g:= tollFee S.patch (300*radiusB p); let y:= Real.exp (|g| *v)
  let t := Pressure.fiery G p L
  have he := h.room; have hT :0<t:=by unfold t; rw [← hL]; exact he.fiery
  let C' := Fintype.card G.ColorIndex*((o.ample+1)*payE o.eta o.gap o.ample (tubularPrice G L)); let M':= M*t
  have hm':0 ≤ M':= by unfold M'; positivity
  let J:= n*|C'|+ n*M'+n*|b R.beta|
  obtain ⟨K,hK,hV'⟩:= notchCost R.beta H.laws.intake.positive (|E p| *v) J n (by positivity) hn
  refine ⟨y*K, mul_nonneg (by unfold y; positivity) hK,?_⟩; intro F X hZ hY h₀ I a' b' x hh hg hk u s l
  have hy:=hp.1; have hL':= h.localP F X hY hZ h₀; have hQ := hh.fund_pos; have hχ:0 ≤ y:= Real.exp_nonneg _
  by_cases ht: X.Pack R Q.table l W o.a s u=0
  · rw [risingMoon a W hh.toFacing,ht,zero_mul,sub_self, abs_zero]; positivity
  unfold Pack at ht; split at ht
  next he' =>
    unfold Pack; rw [if_pos he', if_pos he']
    obtain ⟨hz,hG⟩ := he'
    unfold steam at ht; dsimp only at ht
    have hf' : X.B=radiusB p:= congr_arg _ hY
    have hG' : X.t=t:= by unfold Coat.t t; rw [hY,hL]
    have hq := left_ne_zero_of_mul ht
    have hq' := Mask.masks_wide s X.χ (300*X.B) X.x W (X.input u) X.k X.V h.W_pos hL'.sails.room.fiery (right_ne_zero_of_mul hq) (right_ne_zero_of_mul (left_ne_zero_of_mul hq)) hG
    have hf : Controlled X (304*X.B) s u ((2*a)*X.t) := X.protection_pack (show 0 < a*X.t from mul_pos ha hL'.sails.room.fiery) s (304*X.B) u (right_ne_zero_of_mul ht)
    rw [hG'] at hf
    let w:= tickets s (300*X.B) (X.input u) X.k
    have hw:= tickets_le s (300*X.B) (X.input u) X.k
    let z:=Contract.order R l (vias S s (300*X.B)) (X.input u)
    have hpp : o.γ * (2*(X.width*X.t)) ≤ (2*a)*t:= by rw [hZ,hG']; nlinarith only [mul_le_mul_of_nonneg_right o.gamma hT.le,show a=o.a from rfl] -- nlin?
    have hb := (hp.2 c f' S T F X hY hS hL he s u W o.γ μ hz (fun V=> ((hx c f' S T h.funds).2 V).1) (hY.symm ▸ h.grant) ((by rw [hY,hZ]; exact h.access)) hpp hf hq') -- maximum x check
    let y':=X.quoteNear s u+X.far_bills s
    have hc' : 0 ≤ X.far_bills s := by rw [← av_const 0]; exact av_mono fun j=>sum_nonneg fun _ _=> X.extracted_nn ..
    have hF:0<μ:= h.μ_pos
    have ht :- (|E p| *v) ≤ y':= by
      have := mul_le_mul_of_nonneg_left (hl s) hy
      rw [abs_of_nonneg hy]; unfold y'
      nlinarith only [hb,this,hc',show 0 ≤ μ * X.t^2 * (s.shares:ℝ) from (by positivity)]
    let Y i:= (∑ i∈visit s (200*X.B),X.condensation i)+(∑ j∈X.plaza (s.dome (304*X.B)), X.gentry Q.table a u j)-(X.pens s).card*b i
    have hΦ i : |X.gentry Q.table o.a u i|≤ M':= by
      have hx:= (hs _ _ S T F X hY hL hL'.sails.room.fiery).2 i u; rw [hG'] at hx; exact hx
    have hΨ i : |X.condensation i| ≤ |C'|:= (X.postedBase hL'.sails hL'.empty i).trans (le_abs_self _)
    have h n' (y : ℝ) (f:Bond f'→ℝ) (he:0 ≤ y) (h:∀ i,f i≤ y) : ∑ i∈n',f i ≤ n*y:= by
      apply (sum_le_sum (fun i _=> h i)).trans; rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by unfold n; exact_mod_cast Finset.card_le_univ _) he
    let k:ℝ:= (X.pens s).card
    have hhV : k≤n:= by unfold k n; exact_mod_cast Finset.card_le_univ _
    have hY':Y R.beta≤J:= by
      apply sub_le_iff_le_add.mpr
      apply (add_le_add (h _ |C'| _ (abs_nonneg _) (fun i=> (le_abs_self _).trans (hΨ i))) (h _ M' _ hm' (fun i=> (le_abs_self _).trans (hΦ i)))).trans
      unfold J; nlinarith only [mul_le_mul_of_nonneg_left (neg_le_abs (b R.beta)) (show 0≤k from Nat.cast_nonneg _),mul_le_mul_of_nonneg_right hhV (abs_nonneg (b R.beta))]
    have eh : |Y I.beta-Y R.beta|≤ x*n:= by
      have hv : Y I.beta-Y R.beta=k*(b R.beta-b I.beta) := by unfold Y k; ring
      rw [hv,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),mul_comm]; exact mul_le_mul hh.amount hhV (Nat.cast_nonneg _) hQ
    let M := profiles s X.χ (300*X.B) X.x W (X.input u) X.k X.V; let T:= X.enforce o.a u (X.plaza (s.dome (304*X.B))); let K':=z*w*M*T
    have hm : M∈Set.Icc (0:ℝ) 1:=profiles_range ..; have hγ:T∈Set.Icc (0:ℝ) 1:=X.conserve ..; have hx': z∈Set.Icc (0:ℝ) 1:=Contract.valid_pay ..
    have hh' :0 ≤ w:=ticket_nonneg ..; have hb':0 ≤ z*w:= mul_nonneg hx'.1 hh'; have hc:= mul_nonneg hb' hm.1
    have hg' : w≤ y:= by
      apply hw.trans; apply Real.exp_le_exp.mpr; rw [hf']; exact mul_le_mul (le_abs_self _) (hl s) (Nat.cast_nonneg _) (abs_nonneg _)
    have hk' : K'≤y:= (mul_le_of_le_one_right hc hγ.2).trans ((mul_le_of_le_one_right hb' hm.2).trans ((mul_le_of_le_one_left hh' hx'.2).trans hg'))
    have he i (H:i=I ∨ i=R): X.steam i Q.table l W o.a s u=K'*Real.exp (-i.beta*y'+Y i.beta):= by
      unfold steam; dsimp only; have hp : X.steamLog i Q.table o.a s u=-i.beta*y'+Y i.beta:= by unfold steamLog Y a y' b; ring
      rw [hp,show Contract.order i l =Contract.order R l from (H.elim (fun r=>r.symm ▸ (charged hh.toFacing _).symm) (by rintro rfl; rfl))]
      unfold K' z w M T; ring
    rw [he _ (Or.inl rfl), he _ (Or.inr rfl)]
    apply (hV' x _ _ _ _ _ ht (by rw [abs_sub_comm]; exact hh.β) eh hY' hQ hg hk (mul_nonneg hc hγ.1)).trans; calc
      _ ≤ (x*y)*K := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk' hQ) hK
      _ = _ := by ring
  exact False.elim (ht rfl)
end bounds
end YM.PhysicalNext.Repeat.Alabaster
