import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Freight
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Shards
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Stamen
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Tipping
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Turret

/-!
# Rent at same F. Sales for all shifts post-L. Arithmetic depending on true branch AND forecast purchase.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Port
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute Physical
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps Display Display.Docking Display.Sew Pot Push.AbsoluteSums
    AnalyticNext.ConnectedActivity Milk Dictionary Dictionary.Notify Wires Barge EndpointLoadF16.DetLong
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {x y W a e g L η C b d : ℝ} {p q : Pilot G S x} {X : Support c} {v : Dyed G S}
local notation "PS"=>Physical.place S (G:=G)
local notation "u"=>radiusB x
local notation "K"=>Real.log (spare v.ratio v.source.beta)
open Print AnalyticBridge.Annulus1AD
-- Per-cap accounting uses Anchor; include inactive F every chart. Later core
-- clamp bound may depend V-space cardinality, not cost.
def franc (v : Dyed G S) (p : Pilot G S x) (i : Bond f) := if Print.winter x p.key p.park i then -Real.log (spare v.ratio v.source.beta) else 0
def gold (v : Dyed G S) (p : Pilot G S x) (i : Bond f) := franc v p i + sect v i p

def warm (o : Stores S) (x : ℝ) := univ.filter fun i:Bond f=> S.ratio.parent i.1∈ o.dome (200*radiusB x)

def rents (i : Core S x) (v : Dyed G S) (p:Pilot G S x) := ∑ j∈warm i.val x,gold v p j
def balm (v : Dyed G S) (i:Bond f) (p : Pilot G S x):= if i∈warm p.key x then 0 else gold v p i

def nightly (v : Dyed G S) (p:Pilot G S x):=∑ i,balm v i p
lemma rate_pass (h : Chips v P W x) (hc : Certified S v.things x g C η b) (hA : Matched p) (he : 0≤e)
    (h0 : Physical.parcel G S 20 e g C b d u 0) (h1 : Physical.parcel G S 20 e g C b d u 1) :
    v.keptEarly p=(∑ i∈owners p.key x,rents i v p)+nightly v p+(introTax v p+showTax v p):= by
  rw [book_price h hc hA he h0 h1]; apply congr_arg₂ HAdd.hAdd _ rfl
  let T:= univ.filter fun i:Bond f=> winter x p.key p.park i
  let E : Frozen p.key x p.park ↪ Bond f:= ⟨fun i=> i.val.val,fun i j h=>Subtype.ext (Subtype.ext h)⟩
  have hh : univ.map E=T:= by
    ext i; rw [Finset.mem_map,mem_filter]; constructor
    · rintro ⟨j,h,rfl⟩; exact ⟨mem_univ _,(sees_frost x p.key p.park _).2 j.property⟩
    rintro ⟨h,hx⟩; exact ⟨⟨⟨i,hx.1⟩,(sees_frost x p.key p.park ⟨i,hx.1⟩).1 hx⟩,mem_univ _,rfl⟩
  have hp : (∑ i, franc v p i)=-(Fintype.card (Frozen p.key x p.park):ℝ)* K:= by unfold T at hh; unfold franc; rw [←sum_filter, ←hh,sum_const,card_map,card_univ,nsmul_eq_mul]; ring
  rw [← hp, ← sum_add_distrib]; change (∑ i,gold v p i)= _; rw [Coffer.summers _ (fun i:Bond f=> S.ratio.parent i.1) p (gold v p) (200*radiusB x) (by omega)]; apply congr_arg₂ HAdd.hAdd rfl
  unfold nightly balm warm; simp only [mem_filter, mem_univ,true_and]

lemma gold_le (h : Matched p) (hc : Certified S v.things x g C η b) (i:Bond f) : |gold v p i|≤ Fintype.card G.ColorIndex*((C+1)*C)+|Real.log (spare v.ratio v.source.beta)| := by
  unfold gold
  have hu: |franc v p i| ≤ |Real.log (spare v.ratio v.source.beta)|:= by unfold franc;split <;> simp
  apply le_trans (abs_add_le ..); exact (add_le_add hu (gross p h hc i)).trans_eq (by ring)
lemma gold_read (i:Bond f) (h : Boosted v.things P x) (he : Shields X (S.ratio.parent i.1) (64*u)): Pulled (fun p=> gold v (x:=x) p i) X := by
  have hp:= estate_at h i (he.shrink (by omega))
  refine Pulled.plus ?_ hp; refine ⟨fun A F k=> ⟨fun _=> if winter x A F i then -(Real.log (spare v.ratio v.source.beta)) else 0,measurable_const,fun _ _ _=>rfl⟩,?_⟩
  intro p q ha hb ht; unfold franc; exact if_congr (Print.winter_read x ht.reads _ h.produced.scale (he.shrink (by omega))) rfl rfl
lemma rents_read (i : Core S x) (h : Boosted v.things P x): Pulled (rents i v) (acre i):= by
  refine Pulled.sum (warm i.val x) ?_; intro j hj; apply gold_read j h
  obtain ⟨s,hs,hv⟩:= halo_spec.mp (mem_filter.mp hj).2; exact fun o hn=> halo_spec.mpr ⟨s,hs,(separation_triangle s (S.ratio.parent j.1) o).trans (by omega)⟩
def plotB (S : StepData c f) (x : ℝ) (i : Bond f) := halo (420*radiusB x) {S.ratio.parent i.1}
lemma balm_uses (i : Bond f) (h : Boosted v.things P x) : Pulled (balm v (x:=x) i) (plotB S x i):= by
  have hp: Shields (plotB S x i) (S.ratio.parent i.1) (420*u):= fun k hk=> halo_spec.mpr ⟨_, mem_singleton_self _,hk⟩
  have ht:= gold_read i h (hp.shrink (by omega))
  constructor; swap
  · intro p q ha hb hv; unfold balm warm; simp only [mem_filter,mem_univ,true_and]; exact if_congr (hv.reads.dome_agrees _ _ (hp.shrink (by have hb:= h.produced.scale; omega))) rfl (ht.agreed ha hb hv)
  intro A F k; unfold balm;dsimp only; by_cases he : i ∈ warm A x
  · simp_rw [if_pos he]; exact (Pulled.fetch 0 (X:=plotB S x i)).enter A F k
  simp_rw [if_neg he]; exact ht.enter ..
open Exterior Next.Rank.Perch
lemma bills (P : Teller G) (D : Patch) (Q : Fund) (a:ℝ) (ha : 0 ≤ a) : ∀ᶠ x in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S) (v : Dyed G S) (W κ C η b:ℝ), v.things=T → S.patch=D → Chips v P W x → 100*(1+radiusB x) ≤ c.val → Q.Stock P D 20 2 1 a x → Certified S T x κ C η b →
      Petty v W (radiusB x) a (x^(-(1/8):ℝ)) (nightly v (x:=x)) := by
  let Z:=Aff.density_home D.L;have hp:0≤Z:=by unfold Z Aff.density_home; positivity
  filter_upwards [Grid.poly_hit hp zero_le_one (show (1/8:ℝ) < 1/4 by norm_num) ha 420,
    intro_paid P D Q, Work.E01.radiusB_tendsto.eventually_ge_atTop 120,eventually_gt_atTop (0:ℝ)] with x hx he hf hA c f S T v W κ C η b hl hd hv ht hq hc
  subst T D; let z:=x^(-(1/4):ℝ); let p:=S.ratio.parent; let B:=radiusB x; have hh :0≤z:=(Real.rpow_pos_of_pos hA _).le
  refine Petty.acceptsList (L:=balm v) (ι:=Bond f) (fun i=> balm_uses i hv.boost) (fun i=> ⟨_,halo_subset _ _ (mem_singleton_self _)⟩) (fun _=>hh) (hx _ _ _ (Aff.governs_home S) (fun i=> show plotB S _ i⊆_ from Finset.Subset.refl (plotB S _ i)) _ fun _=>⟨hh,by unfold z; rw [one_mul]⟩) ha fun i q hp hH=>?_
  unfold balm; split; rw [abs_zero]; exact hh
  rename_i hz
  unfold gold franc
  have hy : p i.1 ∉ q.key.dome (200*B):= fun h=>hz (mem_filter.mpr ⟨mem_univ _,h⟩)
  have hi : ¬winter x q.key q.park i:= by
    rintro ⟨hv,h|h⟩
    · exact hy (Aff.placed q.key (10*B) (200*B) (by omega) h)
    apply hy; obtain ⟨y,hh,hy⟩:=halo_spec.mp h; refine halo_spec.mpr ⟨y,hh,(separation_triangle y _ _).trans (Nat.le_trans (Nat.add_le_add hy ?_) (show 10*B+1 ≤ _ by unfold B; omega))⟩
    rw [separation_comm]; exact Work.E03.parent_step ..
  rw [if_neg hi, zero_add]
  exact he S v.things rfl hv.boost.funded ht hq hc q.key q.view q.tag q.park hp i (fun h=> hy (Aff.placed q.key (30*B) (200*B) (by omega) h))
lemma wages (P : Patch) (J : ChartRatio G) (C : ℝ) (hc : 0≤C) (d : ℝ) (hd : 0<d) : ∀ᶠ y in atTop,∀ {c f : Side} (S : StepData c f) (v : Dyed G S) (κ η b : ℝ),
    S.patch=P → v.ratio=J → LocalRatio J → v.source.beta ∈ Set.Icc (betaF G y S.patch.L/2) (2*betaF G y S.patch.L) → Certified S v.things (retime y) κ C η b →
      ∀ (p:Pilot G S (retime y)),Matched p→ ∀ i, |rents i v p|≤ d*hot (betaF G y S.patch.L)^2*(i:Core S (retime y)).val.shares := by
  let t:=logCash J; let Y:= (Fintype.card G.ColorIndex:ℝ)*((C+1)*C); let A:= Aff.density_home P.L; let L := (4*200^4*A)*(Y+4*t)
  have hY:0 ≤ Y:=by unfold Y; positivity
  have ht:0 ≤ t:= logCash_nonneg J; have hA:0 ≤ A:= by unfold A Aff.density_home; positivity
  filter_upwards [Grid.hopper P.L G 4 1 L hd, (Real.tendsto_log_atTop.comp tall_limit).eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop (Real.log 2), eventually_ge_atTop (G.slopeConstant*Real.log P.L.val), eventually_ge_atTop 1, burst_limit] with y hL hμ hy ht' h he c f S v κ η b hP hV hR hβ hv p he' i
  subst P J; let x:=retime y; let μ:= Real.log x; let q:=betaF G y S.patch.L; let s:=v.source.beta
  have hx :0<y:= zero_lt_one.trans_le h; have h₁ : y ≤ q:= le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
  have hZ : q ≤ 2*x:=le_trans (show q≤2*y from by unfold q betaF; linarith only [ht']) (by linarith only [show y ≤ x from he.1])
  have h' :1≤ μ:=hμ
  have hy : Real.log 2 ≤ μ:= hy.trans (Real.log_le_log hx he.1)
  have hh : Real.log q ≤ 2* μ:= le_trans (Real.log_le_log (hx.trans_le h₁) hZ) (by rw [Real.log_mul (by norm_num) (hx.trans_le he.1).ne']; linarith only [hy])
  have hu: |Real.log (spare v.ratio v.source.beta)|≤4*t*μ:= by apply (price_spare _ hR.scale (h.trans h₁) hβ).trans; linarith only [mul_le_mul_of_nonneg_left hh ht,mul_le_mul_of_nonneg_left h' ht,ht]
  let Q:= i.val.shares; let V:= warm i.val x; let H:=1+(radiusB x:ℝ); have hH:0≤H:=by unfold H; positivity
  have hk: ∀ j : Bond f,|gold v p j|≤(Y+4*t)*μ:= fun j=> (gold_le he' hv j).trans (by linarith only [hu,mul_le_mul_of_nonneg_left h' hY])
  have hC:(V.card:ℝ) ≤ 4*200^4*A*H^4*Q:= by
    apply (Aff.count_dome (A:=i.val) (Aff.home S) V hA (Aff.governs_home S) (fun j h=> show Aff.home S j∈i.val.dome (200*radiusB x) from (mem_filter.mp h).2)).trans
    push_cast
    apply le_trans (b:= 4*(Q:ℝ)*(A*(200*H)^4)); swap; · apply le_of_eq; ring
    change 4*(Q:ℝ)*(A*(1+200*_)^4) ≤ _; gcongr; unfold H; linarith only
  unfold rents; apply (Finset.abs_sum_le_sum_abs (gold v p) V).trans; apply (Finset.sum_le_sum (g:=fun _=>(Y+4*t)*μ) (fun i hi=>hk i)).trans
  rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right hC (by positivity : 0≤(Y+4*t)*μ)).trans
  apply le_trans (b:= (L*H^4*μ^1)*Q); swap; · exact mul_le_mul_of_nonneg_right hL (by positivity)
  apply le_of_eq; unfold L; ring
end YM.PhysicalNext.InteractingRank.Pump.Port
