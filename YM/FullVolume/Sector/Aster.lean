import YM.FullVolume.Sector.Gift
/-! second unforced tree: R-powers, orientation real jets with assigned budgets.V's*.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R} -- implicit v
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
open Greenbelt Gas Ursell Trees Blaze.March
namespace Lyre
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
local notation "B₀" => radiusB x₀
local notation "Q'"=> stella Q
variable {V:ℝ→ℝ} (W':Lake G L (payE o.eta o.gap o.ample (Census.tubularPrice G L)) (K*j*2) V k)
variable {p:Signal j} {ν α β':ℝ} (hc:Clear Q L μ ν x₀ v p) (hr:Clarity H j A' δ ν) (hM:Margin G L x₀ α δ)
local notation "F₀" => M.mouth ν p
local notation "π"=> spicesF G r L' (V x₀) K j
local notation "Ψp"=> M.payment (k+j) (π) ν α p
local notation "δe" => U.notes
-- recover Probe from Trace on self, yields EACH factor for all combos not just difference quotient
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U₀:E→ Config G c} {s:E}
private lemma cost_of {p a:ℝ} (x:E) (k:ℕ) (f : ℝ→E→ℝ) (hp:2≤p)(hQ : 0≤a)
    (h :∀ (w:Rung) (v:ℝ), (∀ i:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/p)^i)‖ ≤ v)→ Brush k (v*a) 1 (fun x=> FullVolume.Ray.trace w (fun t=>f t x)) x): Weigh k x (p/2) (2*a) 1 f:=by
  have hv (i:↑FullVolume.Ray.sun):ContDiffAt ℝ k (f i.val) x:= by
    let w:Rung:= Finsupp.single i 1
    have he:∀ j:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/p)^j)‖≤1:= fun j=> by
      simp only [FullVolume.Ray.trace,w,Finsupp.support_single_ne_zero _ (by norm_num: (1:ℝ)≠0),sum_singleton, Finsupp.single_eq_same, one_smul, Real.norm_eq_abs]; rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (ratio_le (by linarith) i.property)
    have hh:= (h w _ he).smooth; change ContDiffAt ℝ _ (f i.val) x; simpa [FullVolume.Ray.trace,w] using hh
  have h₀ :0<p:=by linarith
  refine ⟨zero_le_one,fun i hi=> hv ⟨i,hi⟩,fun u hu j hj=>?_⟩
  have he: Rebar p (fun t=> FullVolume.Ray.marked j (f t) x u) a := by
    refine ⟨by linarith,hQ,fun w v he=> ?_⟩
    have h' := point_norm (h w v he) hj hu
    rw [one_pow,mul_one] at h'
    refine (le_of_eq (congr_arg (‖·‖) ?_)).trans h'; unfold FullVolume.Ray.marked FullVolume.Ray.trace
    have hb (i:↑sun) : ContDiffAt ℝ j (f i.val ∘ FullVolume.Ray.tintM x u) 0:= sheen ((hv i).of_le (Nat.cast_le.mpr hj)) u
    exact ((iteratedDeriv_fun_sum (fun i (hi:i∈w.support)=> (hb i).const_smul (w i))).trans (sum_congr rfl fun i hi=> iteratedDeriv_fun_const_smul (hb i) (w i))).symm
  have hi:= he.recovery (a:=p/2) (by linarith) (half_lt_self h₀); rw [show (1-p/2/p)⁻¹=2 by field_simp; ring] at hi; simpa using hi
variable (ht:2≤v)
include M W' hc hr hM ht
local notation "L'₁"=> fruit (χ:=χ) (U:=U)
lemma grill (i:H.ThinP)(hp:Healthy (Pressure.temp x₀) (H.smallAt i) (U₀ s)) (h:Mode U₀ s j u):Weigh j s (v/2) (2*(Ψp i.val)) 1 (fun t x=> fruit (χ:=χ) (U:=U) i t (U₀ x)):=cost_of s j _ ht (M.paid_sky ..) fun w v he=> taste M W' hc hr hM w v he _ _ hp E U₀ s rfl h
omit W' hc hr hM ht
def stamina (i:H.fragrances) t (V₀:Config G c):= Gas.term H.seam (fun i=>L'₁ i t V₀) i
def wonder (ρ ν α:ℝ) (p:Signal j) (k:ℕ)(i:H.fragrances):ℝ:= clusters H.seam (fun i=> (2:ℝ)^j*(2*M.payment k ρ ν α p i.val)) i.2
local notation "rD"=> M.wonder (π) ν α p (k+j)
include W' hc hr hM ht
variable (w:Rung)(η:ℝ) (hT:∀ i:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/(v/2))^i)‖ ≤ η)
set_option quotPrecheck false
local notation "Z"=> stamina (U:=U) (χ:=χ)
include hT
lemma tour (i:H.fragrances)(X: Config G c)(hZ:Healthy (Pressure.temp x₀) (H.bookFoot (.inr i)) X): Ore X (fun U=> FullVolume.Ray.trace w (fun t=> Z i t U)) u (FullVolume.Ray.Weigh.pattern j * (η * rD i)) j:=by
  intro E _ _ _ A y hp h
  let v k:= 2*(Ψp (i.2 k).val); let F k t x:= fruit (χ:=χ) (U:=U) (i.2 k) t (A x)
  have hh k:= M.grill W' hc hr hM ht (i.2 k) (hp.symm ▸ Finset.disjoint_of_subset_left (show H.smallAt (i.2 k)⊆ _ from Finset.subset_biUnion_of_mem (H.smallAt ∘ i.2) (Finset.mem_univ k)) hZ) h
  have he := FullVolume.Ray.Weigh.prod univ F v (fun _=> 1) (show 1≤_ from FullVolume.Ray.Weigh.ray (hh none)) (fun k _=> hh k); let x : ℝ:= ↑(i.fst+1).factorial; let q:= coefficient H.seam i.snd / (x:ℝ)
  have hs := ((he.timber w η hT).smul q).trim; let g t x:=∏ k,F k t x; have hg t x: stamina (U:=U) (χ:=χ) i t (A x)=q*g t x:=by unfold q stamina g F Gas.term; ring
  refine (hs.climb ?_ le_rfl).shimmy (Eventually.of_forall fun x=>?_)
  · rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_option,Fintype.card_fin,mul_one]
    let Y:=∏ k,v k; have hx : 0≤ (∏ k,v k):= Finset.prod_nonneg fun k _=> mul_nonneg (by norm_num) (M.paid_sky ..)
    have hv:(1+((i.fst+1:ℕ):ℝ))^j ≤ (2^j:ℝ)^(i.fst+1):=by rw [← pow_mul,Nat.mul_comm,pow_mul]; gcongr; rw [add_comm]; exact_mod_cast Nat.lt_two_pow_self (n:=i.fst+1)
    have hu : 0 ≤ FullVolume.Ray.Weigh.pattern j := by unfold Weigh.pattern; exact Finset.sum_nonneg (fun i _=> zero_le_one.trans (Planned.AtomRegular.polar_one i))
    have ha : 0 ≤ η:=(norm_nonneg _).trans (hT 0)
    apply (mul_le_mul_of_nonneg_left hv (show 0 ≤ ‖q‖ * (FullVolume.Ray.Weigh.pattern j*(η*Y)) from mul_nonneg (norm_nonneg _) (mul_nonneg hu (mul_nonneg ha hx)))).trans_eq
    unfold wonder clusters q; change _= FullVolume.Ray.Weigh.pattern j * (η * (_ * (∏ i:Option (Fin i.fst),(2:ℝ)^j * v i)/_)); rw [prod_mul_distrib,prod_const]; simp only [card_univ, Fintype.card_option, Fintype.card_fin,Real.norm_eq_abs,abs_div,abs_of_nonneg (by unfold x; positivity : 0≤ x)]
    unfold x Y v; ring
  change ∑ z∈w.support,w z * Z i z.val (A x)= q * ∑ z∈w.support,w z*g z.val x
  rw [mul_sum]; apply Finset.sum_congr rfl; intro z _; rw [hg,mul_left_comm]
end Lyre
end YM.ConnectedActivityE6.Empire
