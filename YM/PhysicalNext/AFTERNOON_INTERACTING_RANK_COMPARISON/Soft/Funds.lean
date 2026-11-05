import YM.AnalyticNext.QUARTIC_MATCH.Radius.Basin
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Petiole
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Sevres
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Weaves

/-!
# Fully masked scalar resolution

Switching from true BodyGrant to Whitened R affects identity consumption later,
but the unforced weights/program here are from the same Body alphabet and the
same path and K. The negative-log representation on all fields *itself*
is masked. In Soft (no flat recentering, no beta change) sufficient to make a
new E with it and the masked path corrections. Not a query that the old E
be aligned by a flag-only discrepancy from a different normalizer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision
open Pressure Push.SectorMeasure Next.Rank RankCovariance Thirst Pump
open Display Display.Docking Display.Sew Value Flux SectorNext.Vacuum
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {V ι : Type} [Fintype V] [DecidableEq V] [Fintype ι] {v : V→Site c}
    {a d δ e μ x : ℝ}

section
variable (p : BudgetPoint) (X : ι → Inner G v)
set_option quotPrecheck false
local notation "Y" => fun i=>(X i).extent
local notation "Z" => fun i (a:Config G c)=> ((X i).value a).re

def ember (i : Glade c) : Piece G c p.threshold where
  atWay:= ⟨i.property.choose,i.val,i.property.choose_spec⟩
  value:= ReLog.locked Y p Z i.val
  gauge:=Alarm.sails _ _ _ (ReLog.retest_gi Y Z (fun i t a=> congr_arg _ ((X i).inv t a)) _)
  probes:= masked_measurable _ _ _ (ReLog.retest_meas _ _ (fun i=> Complex.continuous_re.measurable.comp (X i).meas) _)
  look:= masksLook (ReLog.retest Y Z (fun i U V h=> congr_arg _ ((X i).loc U V h)) _)
  leave U h:= Classical.byContradiction fun he=> h (masked_ne _ _ _ U he)
variable (w : ι→ℝ) (h : ReLog.Tags (fun i=> (X i).extent) p (fun i a=> ((X i).value a).re) w) (H : ReLog.Fund (fun i=> (X i).extent) p.B a e μ w)
include h H
lemma ember_cost (he : p.supportExponent≤a) : Pieces (p:=p) (ember p X) e:= by
  let g:= ReLog.ceiling (ReLog.fumes Y (-w)); let A:= ember p X
  obtain ⟨-,h,H,-⟩:= ReLog.intake Y h p.B H
  have ht i:0≤g i := (abs_nonneg _).trans (h (1:Config G c) i)
  refine ⟨fun i=>g i.val,fun i=> ⟨ht _,fun u=> h ..⟩,fun i=> ?_⟩
  refine ⟨fun j=> ?_, (hasSum_fintype _).summable,le_trans ?_ (H i)⟩
  · dsimp only; split; exact mul_nonneg (Real.exp_pos _).le (ht _); exact le_rfl
  rw [tsum_fintype]; let D:Finset (Glade c):=univ.filter fun j=> i∈j.val
  have hx:(∑ j∈D,ReLog.native p.B a j.val*g j.val) = ∑ j∈ univ.filter (fun j:Support c=>i∈j),ReLog.native p.B a j*g j:= by
    refine sum_bij (fun i _=>i.val) (fun i hi=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩) (fun i _ j _ h=>Subtype.val_injective h) ?_ (fun i _=>rfl)
    · intro j h; have h':= (mem_filter.mp h).2; exact ⟨⟨j,i,h'⟩,mem_filter.mpr ⟨mem_univ _,h'⟩,rfl⟩
  rw [← hx,Finset.sum_filter]; apply Finset.sum_le_sum; intro j _
  have h0:(A j).atWay.site ∈ j.val:= (A j).atWay.anchor
  split_ifs with h h' h'
  · exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))) (ht _)
  · exact False.elim (h' (h ▸ h0))
  · exact mul_nonneg (Real.exp_pos _).le (ht _)
  exact le_rfl
lemma real_load (U : Config G c) : realGas X p ∅ U=Real.exp (-(∑' i,(ember p X i).value U)) := by
  obtain ⟨he,-,-,hL⟩:= ReLog.intake Y h p.B H
  unfold realGas; rw [sdiff_empty, tsum_fintype]; refine ((hL U univ).2.1).trans (congr_arg (fun i : ℝ=> Real.exp (-i)) ?_)
  let z i := ReLog.locked Y p Z i U; have hp:(univ:Finset (Support c)).erase ∅=Finset.univ.image (fun i:Glade c=>i.val):= by
    ext i; simp only [mem_erase, mem_univ,and_true,mem_image,true_and]
    constructor
    · exact fun h=>⟨⟨_,nonempty_iff_ne_empty.mpr h⟩,rfl⟩
    exact fun ⟨j,h⟩=> h ▸ j.property.ne_empty
  change ∑ i∈ _, z i= _
  rw [powerset_univ,← Finset.sum_erase_add _ z (mem_univ ∅),show z ∅=0 from he _,add_zero,hp,sum_image Subtype.val_injective.injOn]; rfl
end
section
variable {O : Teller G} {T : Tube G S} {L : Lantern G S} (R : Rep G f) (Q : Rep G c)
  (p : ι→ Zest G S x L.park Q.p.threshold) (A : Boosted T O x)
  (hs : 25*radiusB x+30 ≤ Q.p.B) {o ℓ g r η M l σ y : ℝ} (hR : R.Lawful o ℓ g r η)
  (hB : Veins R Q p A hs hR a M l σ)
local notation "Xi"=> unmarked R Q p A hs (blink S) hR
local notation "X" => germ Xi A
local notation "p0"=>Q.p
variable (Ly : Lease S.patch.L R.p Q.p a M l σ y η)
-- new Q E palette, before K
variable {o' ℓ' g' : ℝ} (hc : Q.path.Bounds Q.clip o' ℓ' g')
def dustE (i: (Signed × (ix c ⊕ ix c ⊕ ix c)) ⊕ Glade c) := Sum.elim (mounts Q hc) (ember p0 X) i
local notation "T0"=> dustE R Q p A hs hR hc
-- plants total symmetric
include hB Ly
lemma ripe (ht : Q.p.supportExponent/Q.p.B≤o') : Pieces (p:=Q.p) T0
    (boxesCost p0 Q.beta ℓ' g'+16*σ) := by
  obtain ⟨w,h,H⟩:=v_interval_earns R Q p A hs hR hB _ _ (blink S) Ly (fun _=>1) (fun _=>zero_lt_one); exact (mount_cost Q hc ht).combine (ember_cost p0 X w h H (Ly.output.trans (by unfold ucap; linarith only)))
lemma dustValues (ht : Q.p.supportExponent/Q.p.B≤o') (U) :
    realGas X p0 ∅ U = Real.exp (-(Q.path.inChannels Q.clip Q.p Q.beta U + (∑' i,(T0 i).value U) - Q.beta*basis Q U)) := by
  obtain ⟨w,h,H⟩:=v_interval_earns R Q p A hs hR hB _ _ (blink S) Ly (fun _=>1) (fun _=>zero_lt_one)
  rw [real_load p0 X w h H U]
  let f i:=(T0 i).value U
  have he : (∑' i,f i)=(∑' i,(mounts Q hc i).value U)+∑' j,(ember p0 X j).value U:= Summable.tsum_sum (f:=f) ((mount_cost Q hc ht).all U) (hasSum_fintype _).summable
  apply congr_arg Real.exp; change _=-(_+tsum f-_); rw [he,← add_assoc,mount_price Q hc ht]; ring
lemma dustTurns (ht : Q.p.supportExponent/Q.p.B≤o') (e : Wheel c) (V : Config G c): (∑' i,(T0 i).value (pull e.1 e.2 V))=∑' i,(T0 i).value V:= by
  obtain ⟨U⟩:= hB.voyages e.1 e.2
  let D:=pull e.1 e.2 V; let f i := (X i).extent; let H:= U.orientation
  let J (V:Config G c) i:= masked (p0).threshold (f i) (fun j=> ((X i).value j).re) V
  have hm(i): f (H.exe i) = swath e.1 e.2 (f i):= (H.zone_covers i.val).trans (Finset.map_eq_image ..)
  have hv(i): Healthy (p0).threshold (f i) D ↔ Healthy (p0).threshold (f (H.exe i)) V:= by rw [hm]; exact s_healthy ..
  have he (i): J D i=J V (H.exe i):=by
    unfold J; by_cases h:Healthy (p0).threshold (f i) D
    · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ ((hv i).1 h)]; exact congr_arg _ (U.tribute A i.val V)
    rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (mt (hv i).2 h)]
  have hJ : realGas X p0 ∅ D=realGas X p0 ∅ V:=by
    unfold realGas; rw [sdiff_empty]; dsimp only
    apply (roofGas f f H.exe (orient e) (fun i=> H.zone_covers i.val) (J D) (J V) he univ).trans; refine congr_arg _ (Finset.ext ?_); intro k; obtain ⟨i,rfl⟩:= (orient e).surjective k; exact ⟨fun _=>mem_univ _,fun _=> mem_map_of_mem _ (mem_univ i)⟩
  rw [dustValues R Q p A hs hR hB Ly hc ht V,dustValues R Q p A hs hR hB Ly hc ht D,(Real.exp_strictMono).injective.eq_iff] at hJ
  have hX : Q.path.inChannels Q.clip p0 Q.beta D=Q.path.inChannels Q.clip p0 Q.beta V:= Push.Local.channels_pull ..; rw [hX, show basis Q D=basis Q V from basis_turn Q e V] at hJ
  change _=_ at hJ; unfold D at *; linarith only [hJ]
def pyro := appendE Q T0 (@Denumerable.eqv (Wheel c × ((Signed × (ix c ⊕ ix c ⊕ ix c)) ⊕ Glade c)) (Classical.choice (nonempty_denumerable _))).symm
local notation "LZ"=> pyro R Q p A hs hR hc
lemma pyro_gen (ht : Q.p.supportExponent/Q.p.B≤o') : (∀ s i,Nonempty (Q.activities.Moves s i)) →
    Petals LZ (boxesCost p0 Q.beta ℓ' g'+16*σ) ∧
      (∀ s i, Nonempty ((LZ).activities.Moves s i)) ∧ ∀ V,
      Real.exp (Q.v * Fintype.card (Site c) - Q.beta*basis Q V) * realGas X p0 ∅ V = Real.exp ((LZ).exponent V):= by
  intro h
  let Z:= ripe R Q p A hs hR hB Ly hc ht
  refine ⟨pollen Q _ _ Z, fun s i=> subjects Q _ _ _ _ (h s i), fun V=>?_⟩
  rw [dustValues R Q p A hs hR hB Ly hc ht, ← Real.exp_add]; apply congr_arg
  rw [Rep.exponent]; unfold pyro; rw [represented Q _ _ Z _ (fun i=> dustTurns R Q p A hs hR hB Ly hc ht i V)]
  change _ = Q.v * Fintype.card (Site c) - Q.path.inChannels Q.clip Q.p Q.beta V-_; ring
end
end YM.PhysicalNext.InteractingRank.Soft
