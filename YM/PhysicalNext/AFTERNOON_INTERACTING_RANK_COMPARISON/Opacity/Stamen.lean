import YM.Extra.MULTISOURCE_BOUNDS.Merger
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Plotter
/-!
# Tap packet and occupancy estimates at x retime

Core and optional powers here purely on scalar epoch. Fit via Packets
counting, even at broad on post-L constant width. No plate or μ used here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Grid
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute Packets Display Display.Sew Pot Marker Milk
    Local Next.SectorChange.Rows Gaussian Schur Wisps Next.Rank Next.Rank.Perch Next.Rank.Value Next.Rank.Flux  Display.Docking Next.Scheduling
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ENNReal
variable {c f : Side} {G : Gauge} {S : StepData c f} {x W t q Κ r l a o C δ η e : ℝ} {A : Stores S} {v : Dyed G S} {P : Teller G} {F : Forest S.ratio}
lemma coverPays {ι : Type*} {X : ι→Support c} {n b : ℕ} {z : ι→ℝ} (hX : Ac.Hit X n z t a)
    (hv :∀ i, 0≤z i) (hp : n≤ b) (ht : 0≤t): Ac.Hit X b z t a := by
  intro i; refine budget_mono (hX i) (fun j=>?_) fun j=>?_
  · split; exact mul_nonneg (hv _) (Real.exp_pos _).le; exact le_rfl
  split_ifs
  · exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast cover_earns hp (X j)) ht)) (hv j)
  exact le_rfl
lemma unionPay {ι ψ : Type} [Fintype ι] [Fintype ψ] {X : ι→Support c} {Z : ψ → Support c} {b : ℕ} {f : ι→ℝ} {g : ψ→ℝ} (hx : Ac.Hit X b f e a) (hz : Ac.Hit Z b g e t) : Ac.Hit (Sum.elim X Z) b (Sum.elim f g) e (a+t):= by
  intro i; refine budget_finite (by rintro (j|j); exact (hx i).1 j; exact (hz i).1 j) ?_
  rw [Fintype.sum_sum_type]; exact add_le_add (budget_sum (hx i) univ) (budget_sum (hz i) univ)
lemma grows_size (n : ℕ) (k : ℝ) (h : 0≤k) (η : ℝ) (he : 0<η) : ∀ᶠ x : ℝ in atTop, k*(radiusB x:ℝ)^n ≤ x^η:= by
  have hx : Tendsto (fun x:ℝ=> (Real.log x)^(2*n)/x^η) atTop (𝓝 0):= rpath n η he
  filter_upwards [((hx.const_mul (k*2^n)).eventually (ge_mem_nhds (show _< (1:ℝ) by rw [mul_zero]; norm_num))), Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0:ℝ)] with x hf hz hp
  have hh:(radiusB x:ℝ) ≤ 2*(Real.log x)^2:= by apply (Nat.ceil_lt_add_one (sq_nonneg (Real.log x))).le.trans; nlinarith
  change k*(2:ℝ)^n*(Real.log x^(2*n)/x^η)≤1 at hf; rw [← mul_div_assoc,div_le_one (Real.rpow_pos_of_pos hp _),pow_mul] at hf
  calc
    _ ≤ k*(2*(Real.log x)^2)^n:=by gcongr
    _ ≤ _ := by rw [mul_pow,← mul_assoc]; exact hf
where
  rpath (n : ℕ) (r : ℝ) (hr : 0<r) : Tendsto (fun x:ℝ=> (Real.log x)^(2*n)/x^r) atTop (𝓝 0):= by
    apply Asymptotics.IsLittleO.tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (↑(2*n):ℝ) hr

-- Ω. Price helpers
lemma poly_hit {H K : ℝ} {k q : ℝ} (Hh : 0 ≤ H) (hK : 0≤K) (hq : q< k) (he : 0≤e) (b : ℕ) : ∀ᶠ x : ℝ in atTop,
    ∀ {c : Side} (ι : Type) [Fintype ι] (f : ι→Site c) (U : ι→ Support c), Win.governs f H → (∀ i, U i ⊆ Jewels.den (f i) b (radiusB x)) → ∀ v : ι→ℝ,(∀ i,0≤v i ∧ v i≤ K*x^(-k)) → Ac.Hit U (radiusB x) v e (x^(-q)) := by
  let v:= K*Real.exp (e*(((b+b+1:ℕ)^4:ℕ):ℝ))
  filter_upwards [Jewels.seed_count H b Hh, Work.E01.radiusB_tendsto.eventually_ge_atTop 1, grows_size 5 v (mul_nonneg hK (Real.exp_pos _).le) (k-q) (sub_pos.mpr hq), eventually_gt_atTop (0:ℝ)] with x hx hv ht heX c ι i f U h hl w hp s
  have hh : 0≤ x^(-k):=(Real.rpow_pos_of_pos heX _).le
  refine budget_of_sum (fun i=>?_) fun g=>?_
  · split; exact mul_nonneg (hp _).1 (Real.exp_pos _).le; exact le_rfl
  rw [← sum_filter]; let G:= g.filter fun i=> s∈ U i
  apply le_trans (Finset.sum_le_sum (g:=fun i=> v*x^(-k)) (fun i hi=>?_))
  · rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (hx s ι _ f G h (fun i hi=>hl _ (mem_filter.mp hi).2)) (mul_nonneg (mul_nonneg hK (Real.exp_pos _).le) hh)).trans
    change (radiusB x:ℝ)^5* (v*x^(-k))≤ _; rw [← mul_assoc,mul_comm _ v]; refine (mul_le_mul_of_nonneg_right ht hh).trans_eq ?_; rw [← Real.rpow_add heX]; ring_nf
  refine le_trans (mul_le_mul (hp _).2 (Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ he)) (Real.exp_pos _).le (mul_nonneg hK hh)) (show K*x^(-k)*_≤v*x^(-k) by unfold v; apply le_of_eq; ring)
  exact_mod_cast (Corona.cover_mono (hl i) _).trans (Corona.tile (f i) b _ hv)

-- horticultural multiplicities
private def ballEff (L : Side) (c : ℕ) := ((4*c+9:ℕ)^4 * Packets.typesAt L)
lemma seedPrice (L : Side) (c : ℕ) (B : ℕ) (hb : 1≤B) :
    stepCost L c B ≤ ballEff L c * B^4 ∧ hitCost L c B ≤ ballEff L c * B^4:= by
  unfold stepCost hitCost Animals.ballCost ballEff
  have he : (2*(c*B+1)+2*(c*B+1)+1) ≤ (4*c+9)*B:=by simp only [Nat.add_mul,Nat.mul_assoc]; omega
  have hx : c*B+1+(c*B+1)+1 ≤ (4*c+9)*B:= le_trans (by omega) he
  have hm:(4*c+9)^4*Packets.typesAt L * B^4= ((4*c+9)*B)^4 * Packets.typesAt L:=by rw [mul_pow]; ring
  rw [hm]; exact ⟨Nat.mul_le_mul_right _ (Nat.pow_le_pow_left he _),Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hx _)⟩
lemma herb_count (L : Side) (e : ℝ) (he : 0≤ e) : ∀ᶠ x : ℝ in atTop,
    let B:=radiusB x; let g:=4*Real.log x-Real.log 16; let q:=x^(-(2:ℝ))
    fit L 500 B e 0 g q ∧ totalCharge L 1 500 B q 0 ≤ x^(-(1/2):ℝ) := by
  let C := (ballEff L 500:ℝ); have hC:0≤C:= Nat.cast_nonneg _
  let h:= Real.exp (e*seedCover 500)
  let J:= 16*C^2*h; have hJ:0 ≤ J:= mul_nonneg (by positivity) (Real.exp_pos _).le
  filter_upwards [grows_size 8 J hJ 2 (by norm_num),Work.E01.radiusB_tendsto.eventually_ge_atTop 1, grows_size 4 (C*2) (by positivity) 1 zero_lt_one,eventually_ge_atTop (4:ℝ)] with x hx hB h' he'
  intro B g q; let v:=Real.exp (-4*Real.log x)
  have hp : 0<x:= lt_of_lt_of_le (by norm_num) he'
  have hu: q≤1/2:= by unfold q; rw [Real.rpow_neg hp.le,Real.rpow_two]; calc
    _ ≤ 4⁻¹:=inv_anti₀ (by norm_num) (show (4:ℝ)≤x^2 by nlinarith only [he'])
    _ ≤ _:=by norm_num
  have hq:0<q:= Real.rpow_pos_of_pos hp _
  have hq' : q=(x^2)⁻¹:= by unfold q; rw [Real.rpow_neg hp.le,Real.rpow_two]
  obtain ⟨h₁,h₂⟩:= seedPrice L 500 B hB
  constructor
  · have ht : oneCost 500 e 0 g = 16*h*x^(-(4:ℝ)):= by
      unfold oneCost g h; rw [show 0-(_-Real.log 16)+_=Real.log 16+e*↑(seedCover 500)+Real.log x*(-4) from by ring,Real.exp_add,Real.exp_add (Real.log 16),Real.exp_log (by norm_num), Real.rpow_def_of_pos hp]
    refine ⟨he,?_,lt_of_le_of_lt hu (by norm_num)⟩
    unfold ratioCost; rw [ht];
    calc
      _ ≤ (C*(B:ℝ)^4)^2 * (16*h*x^(-(4:ℝ))):= by
        rw [Nat.cast_pow]; have hb : (stepCost L 500 B:ℝ) ≤ C*(B:ℝ)^4:= by unfold C; exact_mod_cast h₁
        apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hb _) (by unfold h; positivity)
      _ = (J*(B:ℝ)^8)*x^(-(4:ℝ)):= by unfold J; ring
      _ ≤ x^(2:ℝ) * x^(-(4:ℝ)) := mul_le_mul_of_nonneg_right hx (Real.rpow_pos_of_pos hp _).le
      _ = _:= by rw [← Real.rpow_add hp]; norm_num [q]
  unfold totalCharge; norm_num only [max_eq_left (show (0:ℕ) ≤ 1 by decide),pow_one,mul_one]
  have hf : (1-q)⁻¹≤2:= by
    apply (inv_le_comm₀ (by linarith) (by norm_num)).2; linarith
  have hb : (hitCost L 500 B:ℝ) ≤ C*(B:ℝ)^4:= by unfold C; exact_mod_cast h₂
  calc
    _ ≤ C*(B:ℝ)^4 * q*2:= by gcongr; exact inv_nonneg.mpr (by linarith)
    _ = (C*2*(B:ℝ)^4)*q:= by ring
    _ ≤ x^(1:ℝ)*q:= mul_le_mul_of_nonneg_right h' hq.le
    _ ≤ _:= by unfold q; rw [← Real.rpow_add hp]; gcongr <;> linarith
lemma bought_grain (L : Side) (e : ℝ) (he : 0≤e) : ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f), L=S.patch.L → Ac.Hit (fun i:Rung S x=>acre (rips i)) (radiusB x) (fun i=>(x^(-(4:ℝ)))^(rips i).val.shares) e (x^(-(1/2):ℝ)):= by
  filter_upwards [herb_count L e he,eventually_gt_atTop (0:ℝ)] with x hv hx c f S h; intro i
  subst L; let g:= 4*Real.log x-Real.log 16
  let p:= x^(-(2:ℝ)); let j:=x^(-(4:ℝ)); have hj:0<j:= Real.rpow_pos_of_pos hx _
  refine budget_loosen (packet_variants S 500 (radiusB x) (fun i:Rung S x => (rips i).val) _ _ zero_le_one hv.1 (fun i=>pow_nonneg hj.le _) (fun i _=>⟨(rips i).property,Subset.refl _⟩) ?_ i) hv.2
  intro A ha s h
  have hs : s.card ≤ 16^A.shares:= by
    let D:= s.image markT
    have he : D⊆(bloom S A).powerset := by intro i hi; obtain ⟨l,hl,rfl⟩:=mem_image.mp hi; exact mem_powerset.mpr (show markT l⊆ bloom S A from h l hl ▸ l.property)
    have hx : D.card=s.card:= card_image_of_injOn fun i hi j hj he=>Subtype.ext (Prod.ext (Subtype.ext ((h i hi).trans (h j hj).symm)) he)
    rw [← hx]; refine (card_le_card he).trans ?_; rw [card_powerset]; apply (Nat.pow_le_pow_right (by omega) (banner_cap A)).trans_eq; rw [pow_mul]; norm_num
  have hp : Real.exp (0-g)=16*j:= by rw [show 0-g=Real.log 16+Real.log x*(-4) from by unfold g; ring,Real.exp_add, Real.exp_log (by norm_num)]; unfold j; rw [Real.rpow_def_of_pos hx]
  rw [show (∑ i∈s,j^(rips i).val.shares) = ∑ _i∈ s,j^A.shares from Finset.sum_congr rfl (fun i hi=>by rw [h i hi]), Packets.income, mul_comm (0- _), Real.exp_nat_mul,hp,sum_const,nsmul_eq_mul,one_mul,mul_pow]
  gcongr; exact_mod_cast hs
end YM.PhysicalNext.InteractingRank.Pump.Grid
