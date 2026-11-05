import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Enigma
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Passenger
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Spreaders
/-! # Quadratic auxiliary and relative log prices. Budgets per site through retained ERA. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Port
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute Physical
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps Display Display.Docking Display.Sew Pot Push.AbsoluteSums
    AnalyticNext.ConnectedActivity Milk Dictionary Dictionary.Notify Wires Barge EndpointLoadF16.DetLong Print Completion
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Completion
variable {c f : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {x y W a e g L η C b d : ℝ} {p q : Pilot G S x} {X : Support c} {v : Dyed G S}
local notation "N"=>Physical.Key G f
local notation "P0"=>Physical.place S (G:=G)
local notation "B"=>radiusB x
local notation "q₀"=>Barge.stamp P0 (radiusB x) g C (currency b (radiusB x))
-- all lengths. β already stored by d. Dust here BEFORE moving rotations.
def froth (v : Dyed G S) (p:Pilot G S x) := ∑' i:Trip N,toll v i p
lemma paid_froth (h : Chips v P W x) (hc : Certified S v.things x g C η b) (hT : Coffer.noises v L x) (hs : 0≤C) (he : 0≤e)
    (hh : Ac.Hit (berth P0 40 B) B q₀ e y) : Petty v W B e (x^4*y) (froth v (x:=x)) := by
  let Z:=x^2; have hz:0≤Z:= sq_nonneg _; let r:=x^4; have hr:0 ≤ r:=by unfold r; positivity
  have hm i:0≤ q₀ i:= stamp_nn _ _ _ hs (currency_pos ..).le i
  refine Petty.receives (L:=toll v) (fun i=> toll_read h.boost i) (fun i=> ⟨_, (first_lens ..) (lens_root ..)⟩) (fun i=> mul_nonneg hr (hm i)) (fun i=> budget_mono (budget_scale hr (hh i)) ?_ ?_) he ?_
  · intro j; split; exact mul_nonneg (mul_nonneg hr (hm _)) (Real.exp_pos _).le; exact le_rfl
  · intro j; split
    next h=> exact (mul_assoc ..).le
    next h=> rw [mul_zero]
  intro i p hp hv
  have hx (j:N): |soapy p j| ≤ Z:= by
    let F:= sorted p.key p.park (x:=x) (G:=G); obtain ⟨t,rfl⟩:= F.surjective j
    cases t with
    | inl u=> rw [show soapy p _=_ from doggy p u]; exact (hT p hp).dust p.y.1 p.y.2 (v.participates W h.heated h.lives p hp hv).2.2 u
    | inr u=> rw [show soapy p _=_ from zeroY p u, abs_zero]; exact hz
  unfold toll; dsimp only; rw [abs_div,abs_mul,abs_mul]
  apply (div_le_self (by positivity) (by norm_num : (1:ℝ) ≤ |2|)).trans
  exact (mul_le_mul (mul_le_mul (hx _) ((award p.tag h.boost hp hc).2 _) (abs_nonneg _) hz) (hx _) (abs_nonneg _) (mul_nonneg hz (hm (show Trip N from i)))).trans_eq (by unfold r Z; ring)

def satin (v : Dyed G S) (j : Bond f) (p:Pilot G S x) :=
    if h:j∈ Aff.activeB p.key p.park (radiusB x) then logGuard v.chi v.ratio v.arc (v.tapeAt p (Milk.fundedB j h)) else 0
lemma sat (v : Dyed G S) (p:Pilot G S x) (i:Active p.key x p.park): satin v i.val.val p=logGuard v.chi v.ratio v.arc (v.tapeAt p i):= dif_pos ((Milk.stillActive ..).2 i.property)

def lining (v : Dyed G S) (p:Pilot G S x):= ∑ i,satin v i p

def tallyQ (v : Dyed G S) (p:Pilot G S x):=∑ i,v.issue i p
lemma census (p:Pilot G S x) (f:Bond f→ℝ) (h:∀ i, i∉Aff.activeB p.key p.park (radiusB x) → f i=0): (∑ i,f i)=∑ i:Active p.key x p.park,f i.val.val:=by
  symm; rw [← sum_subset (subset_univ (Aff.activeB p.key p.park B)) (fun i _ hi=>h i hi)]
  apply Finset.sum_bij (fun i _=>i.val.val); exact fun i _=>(Milk.stillActive ..).2 i.property
  exact fun i _ j _ he=>Subtype.ext (Subtype.ext he)
  · exact fun i hi=> ⟨fundedB (x:=x) i hi, mem_univ _,rfl⟩
  exact fun i _=>rfl
lemma results (v : Dyed G S) (p:Pilot G S x) :
    lining v p = ∑ i:Active p.key x p.park,logGuard v.chi v.ratio v.arc (v.tapeAt p i) ∧
      tallyQ v p=(eta v.things x p.view p.tag (shots S x) p.key p.park v.chi v.arc p.y.1 (meanLog p.key p.park v.things x p.view p.tag v.chi v.arc p.y.1) (coupling v.source.beta)) ⬝ᵥ p.y.2 := by
  unfold lining tallyQ dotProduct
  rw [Fintype.sum_prod_type (fun i: In x p.key p.park (G:=G)=> eta v.things x p.view p.tag (shots S x) p.key p.park v.chi v.arc p.y.1 (meanLog p.key p.park v.things x p.view p.tag v.chi v.arc p.y.1) (coupling v.source.beta) i*p.y.2 i),census p (fun i=> satin v i p) (fun i hi=> dif_neg hi),census p (fun i=>v.issue i p) (fun i hi=>dif_neg hi)]; exact ⟨sum_congr rfl (fun i _=>sat v p i),sum_congr rfl (fun i _=> v.issue_at p i)⟩
lemma reproduces (h : Chips v P W x) (i:Bond f): Pulled (satin v (x:=x) i) (plotB S x i):= by
  let f:=logGuard v.chi v.ratio v.arc; have hf : Measurable f:= (logGuard_smooth _ h.data h.arc_pos h.inner).continuous.measurable; let X:=plotB S x i
  have hB:=h.boost.produced.scale
  have ht : Shields X (S.ratio.parent i.1) (420*B):= fun i hi=> halo_spec.mpr ⟨_,mem_singleton_self _,hi⟩
  constructor
  · intro A F k; unfold satin;dsimp only; by_cases he:i∈ Aff.activeB A F (radiusB x)
    · simp_rw [dif_pos he]; obtain ⟨p,hp,H⟩:= v.tape_read h.boost h.arc_pos h.vista A F k (Milk.fundedB i he)
      refine ⟨f∘ p,hf.comp hp,fun V hb y=> congr_arg f (H V hb y)⟩
    simp_rw [dif_neg he]; exact (Pulled.fetch 0 (X:=X) (E:=ℝ)).enter A F k
  intro p q he hf' hx; unfold satin
  have hh : i∈ Aff.activeB p.key p.park B ↔ i∈ Aff.activeB q.key q.park B:= by
    have he (p:Pilot G S x): i∈Aff.activeB p.key p.park B↔ Physical.openBond p.key p.park x i:= by
      refine ⟨fun hi=>⟨Milk.fundedB i hi,rfl⟩,fun ⟨j,h⟩=>?_⟩; subst i; exact (Milk.stillActive ..).2 j.property
    rw [he,he]; exact hx.reads.frozen_bits hB i (ht.shrink (by omega))
  by_cases hp : i∈ Aff.activeB p.key p.park B
  · rw [dif_pos hp,dif_pos (hh.mp hp)]; exact congr_arg f (v.tape_scans h.boost.ready _ _ hx (ht.shrink (by omega)) rfl)
  rw [dif_neg hp, dif_neg (mt hh.mpr hp)]

lemma fareCity (P : Patch) (e m r : ℝ) (a : ℝ) (hr : m < r) (he : 0≤e) (ha : 0≤a) : ∀ᶠ x:ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f),S.patch=P → Ac.Hit (plotB S x) (radiusB x) (fun _=> a*x^(-r)) e (x^(-m)):= by
  filter_upwards [Grid.poly_hit (by unfold Aff.density_home; positivity : 0≤Aff.density_home P.L) ha hr he 420, eventually_gt_atTop (0:ℝ)] with x hx hy c f S h; subst P
  exact hx _ _ _ (Aff.governs_home S) (fun i=> show plotB S x i⊆_ from Finset.Subset.refl _) _ fun _=>⟨by positivity,le_rfl⟩
open Next.Rank.Perch
lemma bolsters (P : Patch) (J : ChartRatio G) (hJ : LocalRatio J) (d : ℝ) (_hd : 0≤d) (e : ℝ) (he : 0≤e): ∀ᶠ x in atTop,
    ∀ {c f : Side} (S : StepData c f) (v: Dyed G S), S.patch=P → v.ratio=J →∀ (T : Teller G) (W L : ℝ), Coffer.noises v L x → Chips v T W x → v.arc ≤ d*fiery G x S.patch.L →
      Petty v W (radiusB x) e (x^(-(1/8):ℝ)) (lining v (x:=x)) ∧ Petty v W (radiusB x) e (x^(-(1/8):ℝ)) (tallyQ v (x:=x)) := by
  obtain ⟨u,r,hu,hr,hR,hP⟩:= ratio_price hJ
  let C:=u*(4*d)^2; have hc:0≤C:= by unfold C; positivity
  let N₀ : ℝ:= Fintype.card G.ColorIndex; have hn:0≤N₀:= by unfold N₀; positivity
  have hB : Tendsto (fun x => 4*d*fiery G x P.L) atTop (𝓝 0):= by simpa [Rates.allowance, Rates.pieces] using! (Rates.slow G P).const_mul (4*d)
  filter_upwards [fareCity P e _ _ C (by norm_num : (1/8:ℝ)< 1/4) he hc, fareCity P e _ _ N₀ (by norm_num : (1/8:ℝ)<2) he hn, trim_rate G P 2 0 (3/4) (by norm_num), hB.eventually (ge_mem_nhds hr), eventually_gt_atTop (0:ℝ)] with x hx hz ha hh he' c f S v hp hy T W L h hT h₀
  subst P J; let a:= v.arc; let t:= fiery G x S.patch.L
  have hu' : ∀ p:G.Color, ‖p‖≤4*a → |Real.log (v.ratio.J p)| ≤ u*‖p‖^2:=by
    intro p hp; refine (hP p (le_trans hp ?_)).2.2; change 4*d*t ≤r at hh; linarith only [hh,h₀]
  have hv i: (plotB S x i).Nonempty:=⟨_,halo_subset _ _ (mem_singleton_self _)⟩
  constructor
  · refine Petty.acceptsList (L:=satin v) (ι:=Bond f) (fun i=> reproduces hT i) hv (fun _=>mul_nonneg hc (Real.rpow_pos_of_pos he' _).le) (hx S rfl) he fun i p hp _=>?_
    unfold satin; split; next hl=>
      let q:= v.tapeAt p (fundedB i hl)
      have ht : t^2 ≤ x^(-(1/4):ℝ):= by unfold t; simp only [Rates.allowance,Rates.pieces,pow_zero,one_mul] at ha; exact ha.trans_eq (by push_cast;norm_num)
      have hd:0<a:=hT.arc_pos
      have he' : |logGuard v.chi v.ratio a q| ≤ u*(min ‖q‖ (4*a))^2:=by simpa only [extended,Real.log_exp] using price_extended v.chi hd hu' hu.le q
      apply he'.trans
      calc
        _ ≤ u*(4*(d*t))^2:= by gcongr; exact (min_le_right ..).trans (mul_le_mul_of_nonneg_left h₀ (by norm_num))
        _ = C*t^2:= by unfold C; ring
        _ ≤ _:= mul_le_mul_of_nonneg_left ht hc
    next hl => rw [abs_zero]; positivity
  · refine Petty.acceptsList (L:=fun i=>v.issue i) (ι:=Bond f) (fun i=>Dyed.issue_read hT i (fun j hj=>halo_spec.mpr ⟨_,mem_singleton_self _,hj.trans (by change _ ≤420*radiusB x; omega)⟩)) hv (fun _=> mul_nonneg hn (Real.rpow_pos_of_pos he' _).le) (hz S rfl) he fun i p hp hW=>?_
    unfold Dyed.issue; split; swap; next hl=> rw [abs_zero]; positivity
    next hl=>
      apply (Finset.abs_sum_le_sum_abs ..).trans; apply (Finset.sum_le_sum (g:=fun _=> x^(-(2:ℝ))) (fun j _=>?_)).trans_eq ?_
      swap
      · rw [abs_mul]; refine (mul_le_mul ((h p hp).buzz _ _) ((h p hp).dust _ _ (v.participates W hT.heated hT.lives p hp hW).2.2 _) (abs_nonneg _) (Real.rpow_pos_of_pos he' _).le).trans_eq ?_
        rw [←Real.rpow_two, ← Real.rpow_add he']; norm_num
      rw [sum_const,nsmul_eq_mul,card_univ]
end YM.PhysicalNext.InteractingRank.Pump.Port
