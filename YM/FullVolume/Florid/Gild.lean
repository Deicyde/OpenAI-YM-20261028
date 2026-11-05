import YM.FullVolume.Florid.Enact
import YM.FullVolume.Florid.Payee
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire.Imago
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray Daisy Lotus
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R}
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' fq:ℝ} {K:ℕ} {χ:Chi}
open Lyre Jams
set_option quotPrecheck false
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
namespace Mill
variable (V:Mill U)
local notation "Λ"=> U.pole
local notation "Rv"=> V.pole
variable (D: dust j o χ L x₀ d fq)
open Lyre Charity Blaze.March
variable {p:Signal j} {ν α:ℝ} (hc:Clear Q L μ ν x₀ v p) (hr:Clarity H j A' δ ν)
variable {V':ℝ→ℝ} (W':Lake G L (payE o.eta o.gap o.ample (Census.tubularPrice G L)) (K*j*2) V' k)
variable (Y':Margin G L x₀ α δ) (w:Rung) (η:ℝ) (hh : ∀ i:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/v)^i)‖ ≤ η)
set_option quotPrecheck false
local notation "τ"=> V.pole.turn.badge S
local notation "Q'" => Empire.stella Q
local notation "Φ"=> jewelDebt V.pole (Empire.stella Q) L x₀
local notation "B₀" => radiusB x₀
local notation "π"=> Lyre.spicesF G (r+fq) L' (V' x₀) K j
-- selected under stellar props. Keep Φ factors integrated outside tree.
local notation "hτ" => lushE M V α ν (π) p (k+j)
open Greenbelt
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March Match
local notation "π₀"=> Lyre.spicesF G r L' (V' x₀) K j
local notation "e₁"=> hopes M V (spicesF G r L' (V' x₀) K j) (π) α ν (k+j) p
local notation "X₀" z=> H.bookFoot (.inr z)
variable (hp:foam Q L)(hb:R.p.B≤2*radiusB x₀)(hA:(Daisy.swing (stella Q) L μ R.beta x₀ ν).Buy S.patch.L Q.halo (radiusB x₀))(hv:2≤v)
set_option quotPrecheck false
local notation "δ₀"=> billsD Q (π₀) (π) L μ x₀ j (k+j)
local notation "P₀"=>FullVolume.Ray.Weigh.pattern j
private lemma degreeW {A : ℝ→ℝ}(hp:Rate G L v A) (u:ℝ) : Rate G L v (fun x=> Trees.degreePrice (radiusB x) (A x) u) := by
  have ht:= width_rate G L 1 0; simp only [one_mul,add_zero] at ht
  simpa only [Trees.degreePrice,Trees.stretch, zero_add, div_eq_mul_inv] using! ((((ht.mul hp).mul_right u⁻¹).mul_left 4))
private lemma beaconK (r b v : ℝ→ℝ) (hr:Rate G L 0 r)(hp:Rate G L 0 b)(hv:Rate G L 0 v) (j k:ℕ) : Rate G L 0 (fun x=> spicesF G (r x) (b x) (v x) k j):=by
  have ht:= Rate.const (G:=G) (L:=L) 1; unfold spicesF
  simpa only [zero_mul,zero_add] using! (((ht.add ((hp.mul_right (2^k:ℝ)).add (hr.mul_left 2))).pow j).mul_left (FullVolume.Ray.Fold.charge j * FullVolume.Ray.Weigh.pattern j)).mul (ht.add (hv.compare (v:=fun x=> |v x|) (Eventually.of_forall fun x=>(abs_abs _).le)))

structure Jam (H:Cash W x₀ μ L Q o C T R)(U:Tune H v δ)(p:BudgetPoint)(χ:Chi)(e t:ℝ) :Prop where
    phases (V:Mill U) (y:Site c) (h:y∈ V.pole.crest.image S.ratio.parent): ∃ f:H.fragrances→ℝ, SumBudget (fun i=> f i*Real.exp (e*coverNumber (radiusB x₀) (locus V.pole H y i))) ((jewelDebt V.pole (stella Q) L x₀)*t) ∧ ∀ i,∀ (w:Rung) (η:ℝ),Stripe w (v/2) η → p.supBounds y (locus V.pole H y i) (fun x=> Jams.mix w (fun t=> signalAt V χ t i x)) (η*f i)
lemma projects (hQ: Q.rate ≤ -(7/16:ℝ)): ∃ N:ℕ,∀ (L:Side),N≤L.val→∀ (D:Patch), D.Branches P.bind G→∀ (j m:ℕ) (χ:Chi)(W μ:ℝ),0<W→0<μ→∀ (o:Target.Order G W) (C e:ℝ), 0≤e→ e<Q.exp → ∀ᶠ x in atTop,∀ (c f:Side) (S:StepData c f)(T:Tube G S), S.patch=D→ Stamp T→ ∀ (R:Rep G f) (H:Cash W x μ L Q o C T R), ∀ (U:Tune H (fire G L x) (thaw G L x)) (P:BudgetPoint), P.power=m→ P.threshold=Pressure.temp x → P.order=j →Jam H U P χ e (pottery G L x):=by
  obtain ⟨n',H⟩:= wombPlus P Q; obtain ⟨n,HF⟩:=early Q
  refine ⟨max n n',?_⟩; intro L hL D hD i m χ W μ hW hμ o C e he hx
  obtain ⟨d,A,hp⟩:= Eider.weave G; obtain ⟨K,hK,hG⟩:= March.oar G i
  let a x:=2*Pressure.fiery G x L; let f x:= ((i:ℝ)+1)*K*a x
  have hr : Rate G L (-(1/2)) a:= Rate.flame.mul_left _; have hR : Rate G L (-(1/2)) f:=hr.mul_left _
  have hQ' : ∀ᶠ x in atTop,0<a x:= ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  obtain ⟨C',d',r,p,k,hC,hpp,hK₁,hVV,hX⟩:= H L (by omega) D hD i χ W hW μ hμ o d A hp f hR (hQ'.mono fun x h=> by unfold f; positivity)
  obtain ⟨V,t,hv,hF⟩:= Flux.walksW G L (payE o.eta o.gap o.ample (tubularPrice G L)) (k*i*2)
  have hF' : Lake G L (payE o.eta o.gap o.ample (tubularPrice G L)) (k*i*2) V t:=⟨hF⟩
  let α:= (Q.exp-e)/4; have hs : 0<α:= by unfold α; linarith
  have hΛ:e+3*α ≤ Q.exp:=by unfold α; linarith
  obtain ⟨F,hU,hM⟩:= morph i o χ L _ hVV
  let g x:= spicesF G (r x) (p x) (V x) k i; let v₀ x:= spicesF G (r x+F x) (p x) (V x) k i; let z x:= billsD Q (g x) (v₀ x) L μ x i (t+i); let q:= stella Q
  have hg:= beaconK r p V hK₁ hpp hv i k
  have huT:= beaconK (fun x=> r x+F x) p V (hK₁.add hU) hpp hv i k
  have hB : Rate G L q.rate z:=by
    have ht:= (Daisy.strides L (stella Q) hμ (t+i)).1
    have hs := ((huT.mul_left 2).mul ht); change Rate _ _ q.rate _ at ht -- q.rate
    exact (Rate.mul_left (show Rate G L q.rate (fun x=>((1+ 2*g x)*q.overture L μ x (t+i)+2*v₀ x*(Daisy.swing q L μ 1 x 0).ceiling 0 (t+i) 0 0)) from by
      apply Rate.add
      · simpa only [zero_add] using! (((Rate.const 1).add (hg.mul_left 2)).mul (q.rate_none L hμ 0 (t+i) 0))
      simpa only [zero_add] using! hs) ((2:ℝ)^(i+2)))
  obtain ⟨ν,hν,hz,hα,hT⟩:= crown G L i 0 C'
  obtain ⟨s⟩:= Lyre.signed_signal i
  have hz':Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
  have hP : Rate G L q.rate (fun x=>FullVolume.Ray.Weigh.pattern i*(collars G α x i m *(z x * (1-1/2)⁻¹))) :=by unfold collars; simpa only [zero_mul,zero_add] using! ((((hz'.pow (m*i)).mul_right _).mul (hB.mul_right (1-1/2:ℝ)⁻¹)).mul_left _)
  have hd :∀ᶠ x in atTop, 2≤ fire G L x := ((tendsto_rpow_atTop (show (0:ℝ)<1/256 by norm_num)).comp (Work.E09.betaF_growth G L)).eventually_ge_atTop _
  filter_upwards [hX, hM, (sailsW (L:=L) (stella Q) hμ),(Daisy.stables L (stella Q) hμ (fun _=>1) (e:=α) hs (show e+α+α ≤ q.exp from (by change _≤ Q.exp; linarith)) he (Rate.const _) 0 0 0), hQ',pocketsC G L hs,shows Q L μ hα s hμ hQ,
    (degreeW hB α).below q.stop (1/2) (by norm_num), hP _ (by change -(2/5:ℝ)< -(3/8); norm_num),hd] with x ha hF hV htG hp' hσ H hb' hJ hδ c f' S T hS ht R B U P hp₀ hP hI
  let y:=K*a x; have hy:0≤y:= by unfold y; positivity
  let Y:= Lyre.mk (ha c f' S T hS ht R C B).some (fun i hi=>(ha c f' S T hS ht (U.notes i) C (U.beams i hi)).some)
  have hl':Clarity B i C' (thaw G L x) ν:=⟨fun F X m hh hz'=> hT c f' S T F X m x _ _ C' hz le_rfl hh B.laws.data.funds.length_eq hz' U.pole.full.2.2 U.pole.active⟩ -- argument βCost !!! b,v and α= gain
  have hy':Sailor G P.threshold y i:= by
    refine ⟨fun c v he => hG c (a x) hp'.le v (he.trans ?_)⟩
    have hh := B.laws.data.room.temperatures; rw [B.laws.data.funds.length_eq] at hh; exact hP.trans_le hh
  have hn:i*y≤f x:=by unfold f y; nlinarith only [mul_nonneg hK.le hp'.le]
  constructor; intro Φ' l hx₁
  have hBk := B.laws.data.funds.length_eq
  have hvK:R.p.B≤2*radiusB x:= by rw [B.laws.intake.sizes,hBk]; exact htG.1.covers
  obtain ⟨hv',hZ⟩:= B.laws.intake.window; rw [hBk] at hv'
  have hV':(Daisy.swing (stella Q) L μ R.beta x ν).Buy S.patch.L Q.halo (radiusB x):=by rw [hBk]; exact hV R.beta ν (H.forcer _ hv')
  have hp:=HF L (by omega)
  have ht:= marginalS Y Φ' hF H hl' hF' hσ hp hvK hV' hδ he hΛ ((le_abs_self _).trans hb') l hx₁ m
  refine ⟨_,budget_loosen ht (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hJ) (scentL Φ'.pole B|>.2.1)),fun i w b hb=> ?_⟩; have ht:= resumes Y Φ' hF H hl' hF' hσ hp hvK hV' hδ hI hP hy' hy hn l hx₁ i w b hb; rw [hp₀] at ht; exact ht

end Mill
end YM.ConnectedActivityE6.Empire.Imago
