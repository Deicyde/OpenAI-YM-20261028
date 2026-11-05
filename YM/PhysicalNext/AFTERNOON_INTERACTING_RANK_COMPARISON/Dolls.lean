import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Parades
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Arity
import YM.Push.LOCAL_SPLITTING.Comparison
import YM.SectorNext.VACUUM_NORMALIZATION.Bulk

/-! # Actual unmarked ReLog holes before any marker extension

At values, only need real masked log from THIS abridged gas.
Tags coherence paid at stencil/point without differentiating log;
issue pressure for all occupied/excluded ratios. For Root compensation
need not equate background system with its gas at a different mask;
this is prior to exact scalar passport (on unrestricted gas root).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Sew
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph Thirst
     Flux Bid SectorNext.Vacuum Precision
open scoped Topology BigOperators Classical
variable {G : Gauge} {c : Side}
    {R : Rep G c} {W V ι κ α β : Type} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] {u : W → Site c} {v : V→Site c} {ρ d m : ℝ}
variable [Fintype ι]
-- Scalar unmarked only
def scalar (W : Type) [Fintype W] [DecidableEq W] : ℝ→+* veil W := (algebraMap ℂ (veil W)).comp Complex.ofRealHom
lemma evening_one (W : Type) [Fintype W] [DecidableEq W] (z : ℝ) : Poly.send (Glyph.quiet W) ↑z = scalar W z:= rfl
lemma scalar_inj (W : Type) [Fintype W] [DecidableEq W] : Injective (scalar W):= by
  intro a b h; apply Complex.ofReal_injective; rw [← evening_one,←evening_one] at h
  have ht:=congr_arg (fun i:veil W=>i.part (quiet _)) h; simpa only [Poly.part_send,↓reduceIte] using ht
lemma send_price (p : W → ℝ) (r : ℂ) : Poly.price p (Poly.send (quiet W) r)= ‖r‖ := by simp only [Poly.solo,Poly.toll, Glyph.quiet,Census.quiet, Finset.prod_empty,one_mul]

section
variable (X : ι → Inner G u) (b : BudgetPoint) (w : ι → ℝ) {z : Config G c}

def realGas (X : ι→ Inner G u) (b : BudgetPoint) (D : Support c) (U : Config G c) : ℝ:=
    let A i:=(X i).extent; ReLog.fumes A (ReLog.herald A b (fun i z=> ((X i).value z).re) U) (univ\D)
set_option quotPrecheck false
local notation "Ψ"=>fun i=> (X i).extent
local notation "Ξ"=>fun i z=> ((X i).value z).re
omit [Fintype ι] in
lemma start_local (hx : ∀ i U, ‖masked b.threshold (X i).extent (X i).value U‖ ≤ w i) : ReLog.Tags Ψ b Ξ w := by
  refine ⟨fun i=>(X i).active,fun i U V h=>congr_arg _ ((X i).loc U V h),fun i k V=>congr_arg _ ((X i).inv k V),fun i=>Complex.continuous_re.measurable.comp (X i).meas,fun i U h=>?_⟩
  exact (Complex.abs_re_le_norm _).trans (masked_eq _ _ (X i).value _ h ▸ (hx i U))
-- This expression **needs** hypotheses on REAL (Sewer uses unmasked card)
lemma evening_table (he : ∀ i,(X i).fires=quiet W) (hc : ∀ i z,(X i).value z=((((X i).value z).re:ℝ):ℂ)) (D : Support c) (V : Config G c) :
    backgroundU X b.threshold D V=scalar W (realGas X b D V):= by
  let A:= Ψ; let E i:= ((X i).glow b.threshold).covets V; let a i:= ReLog.herald Ψ b Ξ V i
  have h i:E i = scalar W (a i) := by
    unfold E a ReLog.herald CoverReads.covets; simp only [Inner.glow,he,← evening_one]
    apply congr_arg; by_cases h:Healthy b.threshold (X i).extent V
    · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]; exact hc ..
    simp only [masked_ne _ _ _ _ h,Complex.ofReal_zero]
  unfold backgroundU realGas chair ReLog.fumes; rw [tsum_fintype, map_sum]
  let B:= univ.filter fun i=> Disjoint (A i) D
  have hb (s : Finset ι) : ReLog.allowed A (univ\D) s ↔ s⊆B∧packed A s:= by
    unfold ReLog.allowed; rw [ReLog.accepts, ReLog.stays]; simp only [subset_refl,true_and]
    refine and_congr ?_ Iff.rfl
    constructor
    · intro ht i hi; exact mem_filter.mpr ⟨mem_univ _,Finset.disjoint_left.mpr fun j hj hp=> (mem_sdiff.mp (ht i hi hj)).2 hp⟩
    intro h i hi x hx; exact mem_sdiff.mpr ⟨mem_univ _, Finset.disjoint_left.mp ((mem_filter.mp (h hi)).2) hx⟩
  let q(s:Finset ι):=scalar W (ReLog.note A a (univ\D) s)
  change (∑ i∈ B.powerset, _)= ∑ s:Finset ι,q s
  symm; rw [← Finset.sum_subset (s₁:=B.powerset) (s₂:=univ) (subset_univ _) (f:=q)]
  · apply Finset.sum_congr rfl; intro i hi; unfold q ReLog.note; rw [hb, and_iff_right (mem_powerset.mp hi)]
    split_ifs with hP; swap; · rw [map_zero]
    rw [map_prod]; exact prod_congr rfl fun i _=>(h i).symm
  intro i _ hi; unfold q ReLog.note; rw [if_neg (fun h=>hi (mem_powerset.mpr ((hb i).1 h).1)),map_zero]

abbrev Glade (c : Side) := {s : Support c // s.Nonempty}
-- ReLog on this X (e.g. Exe)

def scroll (s : Glade c) : Inner G u where
  extent:=s.val
  active:=s.property
  fires:= Glyph.quiet _
  remembers:=fun _ h=>False.elim (Finset.notMem_empty _ h)
  value U:= (↑(Real.exp (ReLog.raw Ψ Ξ s.val U)-1):ℂ)
  meas:= Complex.continuous_ofReal.measurable.comp (((ReLog.retest_meas Ψ Ξ (fun i=>Complex.continuous_re.measurable.comp (X i).meas) s.val).exp).sub measurable_const)
  loc:= fun i j h=>by dsimp only; rw [ReLog.retest Ψ Ξ (fun i U V H=>congr_arg _ ((X i).loc U V H)) _ i j h]
  inv:= fun i t=>by dsimp only; rw [ReLog.retest_gi Ψ Ξ (fun i z U=>congr_arg _ ((X i).inv z U)) _ i t]
lemma scroll_value (s : Glade c) (U : Config G c) : ((scroll X s).glow b.threshold).value U= (↑(Real.exp (ReLog.locked Ψ b Ξ s.val U)-1):ℂ):= by
  by_cases h: Healthy b.threshold s.val U
  · exact (masked_eq _ _ _ _ h|>.trans ((congr_arg (fun z : ℝ=> (↑(Real.exp z-1):ℂ)) (masked_eq b.threshold s.val (ReLog.raw Ψ Ξ s.val) U h).symm)))
  change masked _ s.val _ _ = _; rw [masked_ne _ _ _ _ h,ReLog.locked,masked_ne _ _ _ _ h]; simp
lemma greeting (s : Glade c) (U : Config G c):
    ((scroll X s).glow b.threshold).covets U+1=scalar W (Real.exp (ReLog.locked Ψ b Ξ s.val U)):= by
  rw [CoverReads.covets,scroll_value,show ((scroll X s).glow b.threshold).fires=quiet W from rfl,evening_one,map_sub, map_one,sub_add_cancel]
lemma reclamation (he : ReLog.Tags Ψ b Ξ w) (h : ReLog.Fund Ψ b.B m ρ d w) D U :
   scalar W (realGas X b D U)=scalar W (realGas X b ∅ U) * ∏ i ∈ univ.filter (fun i: Glade c=> ¬ Disjoint (scroll X i).extent D), (((scroll X i).glow b.threshold).covets U+1):= by
  simp_rw [greeting]; let f (i:Support c):= ReLog.locked Ψ b Ξ i U
  rw [← map_prod, ← Real.exp_sum, ← map_mul]
  apply congr_arg; unfold realGas; rw [Finset.sdiff_empty]
  let γ := ReLog.herald Ψ b Ξ U
  refine ((ReLog.intake Ψ he b.B h).2.2.2 U D).2.2.1.trans ?_
  let z:= univ.filter (fun i:Support c=> ¬Disjoint i D)
  apply congr_arg; apply congr_arg Real.exp
  change ∑ i∈z,f i=∑ i∈ _,f (i:Glade c).val
  symm; apply sum_bij (fun i _=> (i:Glade c).val)
  exact fun _ h=> mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩; exact fun _ _ _ _ h=>Subtype.val_injective h
  · intro i hi; have ht :=(mem_filter.mp hi).2; have hv : i.Nonempty:= not_nonempty_empty (α:=Site c)|> fun _=> (by by_contra! h; rw [h] at ht; exact ht (Finset.disjoint_empty_left _)); exact ⟨⟨i,hv⟩,mem_filter.mpr ⟨mem_univ _,ht⟩,rfl⟩
  exact fun _ _=>rfl
-- bounds using floor ρ from Fund
lemma patch_paid (he : ReLog.Tags Ψ b Ξ w) (h : ReLog.Fund Ψ b.B m ρ d w) (hl : ρ≤1) (L : ℝ) (hy : 0≤L) :
    ∃ z:Glade c→ℝ, (∀ i,0≤z i) ∧ (∀ i U,L*‖((scroll X i).glow b.threshold).value U‖ ≤ z i) ∧ Hits (fun i=>(scroll X i).extent) z b m (L*2*ρ):= by
  let g:= ReLog.ceiling (ReLog.fumes Ψ (-w)); let n (i : Glade c):= g i.val
  obtain ⟨-,hg,hz,-⟩:= ReLog.intake Ψ he b.B h; let a:=ReLog.native (n:=c) b.B m; let Y:=fun i=> a i*g i
  have hN i:0≤g i:= (abs_nonneg _).trans (hg (1:Config G c) i)
  have ha t (x:Support c) (hh:t∈x): a x*g x≤ρ:= (single_le_sum (f:=Y) (fun _ _=> mul_nonneg (Real.exp_pos _).le (hN _)) (mem_filter.mpr ⟨mem_univ _,hh⟩)).trans (hz t)
  have hx (i:Glade c): g i.val ≤1:= by obtain ⟨t,ht⟩:=i.property; exact (le_mul_of_one_le_left (hN _) ((ReLog.native_rate b.B h.nonnegative).pos _)).trans ((ha t _ ht).trans hl)
  let f(i : Glade c):=L*2*n i
  refine ⟨f,fun i=> mul_nonneg (by positivity) (hN _),fun i U=> ?_,fun i=>?_⟩
  · rw [scroll_value,Complex.norm_real]; have hv:= Real.abs_exp_sub_one_le ((hg U i.val).trans (hx i)); unfold f n; change _ ≤ _*_ *g i.val; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hv.trans (mul_le_mul_of_nonneg_left (hg U _) (by norm_num))) hy
  apply le_trans (b:= L*2*∑ i' ∈ (univ:Finset (Support c)).filter (fun j=>i∈j), Y i') _ (mul_le_mul_of_nonneg_left (hz _) (by positivity))
  unfold strike; rw [Finset.sum_filter]
  let v:= univ.filter (fun j:Glade c=>i∈j.val)
  have hL : (∑ j:Glade c, if i∈ (scroll X j).extent then alarm (fun i=>(scroll X i).extent) f b.B m j else 0) =∑ j∈v,f j*a j.val:= by rw [Finset.sum_filter]; apply sum_congr rfl; intro j _; split_ifs <;> first|rfl|contradiction
  refine le_trans (b:=∑ j∈v,f j*a j.val) ?_ ?_
  · refine le_trans ?_ hL.le; apply sum_le_sum; intro j _; split_ifs <;> exact le_rfl
  rw [Finset.mul_sum]
  have hν : v.image Subtype.val⊆ ((univ:Finset (Support c)).filter (fun j=>i∈j)):= by intro i hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2⟩
  apply le_trans _ (sum_le_sum_of_subset_of_nonneg (f:=fun i => L*2*Y i) hν (fun i _ _=> mul_nonneg (by positivity) (mul_nonneg (Real.exp_pos _).le (hN _))))
  rw [Finset.sum_image Subtype.val_injective.injOn]; exact (sum_le_sum fun i _=>by unfold f n Y; linarith only)
end
end YM.PhysicalNext.InteractingRank.Display.Sew
