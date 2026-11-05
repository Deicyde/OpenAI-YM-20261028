import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Festal
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Procession
/-! # Path booking C cutoff. Finite Kin shape units and transfer carrying
 absolute anchors from scale zero. Tangential leases later.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck  
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling WilsonStartup Extra.Iteration Song
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V : ℝ}
section mellow
variable {A : Type*} (Y:PathData G) (q:BudgetPoint)
abbrev Rags := Low ⊕ ℕ ⊕ ℕ ⊕ ℕ
-- One linear translate t from path/coupling plus...
def melody (i:Rags):ℕ:= i.elim (fun d=>d.length Y) (Sum.elim (fun i=>(Y.cubic i).length) (Sum.elim (fun i=>(Y.quartic i).length) (fun i=>(Y.loop i).length)))
def legs (s:Seat c) (i : Rags): Songbook c:= i.elim (fun x=>.inl (s,x)) (Sum.elim (fun x=> .inr (.inl (s,x))) (Sum.elim (fun x=>.inr (.inr (.inl (s,x)))) (fun x=> .inr (.inr (.inr (s,x))))))
abbrev stepper (c : Side) : Seat c×Rags→ Songbook c:= fun i=> legs i.1 i.2
def rollers (c:Side): Seat c × Rags≃ Songbook c := Equiv.ofBijective (stepper c) (by
  constructor
  · rintro ⟨x,i⟩ ⟨y,j⟩ h; rcases i with i|i|i|i <;> rcases j with j|j|j|j <;> simp [stepper,legs] at *; all_goals exact h
  rintro (⟨s,i⟩|⟨s,i⟩|⟨s,i⟩|⟨s,i⟩)
  · exact ⟨(s,.inl i),rfl⟩
  · exact ⟨(s,.inr (.inl i)),rfl⟩
  · exact ⟨(s,.inr (.inr (.inl i))),rfl⟩
  exact ⟨(s,.inr (.inr (.inr i))),rfl⟩)
lemma tunesAnchor (s: Seat c) (i:Rags): (strings Y q (legs s i)).site=s.2:= by rcases i with i|i|i|i <;> rfl
lemma yarn (s:Seat c) (i:Rags): (strings Y q (legs s i)).support⊆neighbors (q.B + Meadow.melody Y i) s.2:= by
  let f i:= Lattice.affine s.1 s.2 i
  have hp i : separation s.2 (f i)= separation (0:Site c) i:= by unfold f Lattice.affine; nth_rw 1 [← zero_add s.2]; rw [separation_translate]; nth_rw 1 [← s.1.act_zero]; rw [separation_signed]
  rcases i with i|i|i|i
  · intro y hy; change y∈ (i.home Y q (0:Site c)).image f at hy
    obtain ⟨i',hi,rfl⟩:=mem_image.mp hy; apply (neighbors_mem ..).2; rw [hp]; change _ ≤ q.B+ i.length Y
    have h₀ (h:i'∈halo q.B ({0}:Support c)) : separation (0:Site c) i' ≤ q.B := by simpa [halo_spec] using h
    unfold Low.home at hi; cases he:i.2 with
    | inl w=>
      rw [he] at hi; exact (h₀ hi).trans (Nat.le_add_right ..)
    | inr z=>
    rw [he] at hi; unfold Low.length; rw [he]; simp only [Sum.elim]
    rcases mem_union.mp hi with h|h
    · rcases mem_union.mp h with h|h
      · exact (h₀ h).trans (Nat.le_add_right ..)
      rw [separation_comm]; exact (slot_length (i.left Y z) _ h).trans (by omega)
    rw [separation_comm]; exact (slot_length (i.right Y z) _ h).trans (by omega)
  all_goals
    intro y hy
    obtain ⟨w,hq,rfl⟩ := mem_image.mp hy
    apply (neighbors_mem ..).mpr; rw [show separation s.2 _=separation 0 w from hp w];
    apply le_trans _ (Nat.le_add_left ..); first | rw [Paths.atom_foot 0 (Y.cubic i)] at hq; exact Paths.where_slot _ _ _ hq | rw [Paths.atom_foot 0 (Y.quartic i)] at hq; exact Paths.where_slot _ _ _ hq | rw [Paths.atom_foot 0 (Y.loop i)] at hq; exact Paths.where_slot _ _ _ hq

def bough (k:ℕ): Finset Rags:= let d:=Finset.range k
    (univ ×ˢ (Finset.disjSum (univ:Finset Unit) (d×ˢ d))).disjSum (d.disjSum (d.disjSum d))
def ripened (n k:ℕ): Finset Rags:= (bough k).filter fun i=>Meadow.melody Y i≤ n
lemma burgeoning (n:ℕ) (i:Rags) (hp:Meadow.melody Y i ≤ n): ∀ᶠ k in atTop,i∈ripened Y n k:= by
  have he (i:ℕ):∀ᶠ k in atTop,i∈ Finset.range k:=(eventually_gt_atTop i).mono fun i h=>mem_range.mpr h
  refine (Eventually.mono (p:=fun k=> i∈bough k) ?_ (fun k h=> mem_filter.mpr ⟨h,hp⟩)); rcases i with ⟨i,i⟩|i|i|i
  · rcases i with i|⟨i,k⟩; · filter_upwards with x; simp [Meadow.bough]
    filter_upwards [he i,he k] with x hi hj; simp only [Meadow.bough,inl_mem_disjSum,mem_product,inr_mem_disjSum,hi,hj,mem_univ,true_and]
  all_goals exact (he i).mono fun _ h=>by simp only [Meadow.bough,inr_mem_disjSum,inl_mem_disjSum,h]

def spurs (τ : Clip) (β γ:ℝ) (s:Signed) (i:Rags) (x:Site c):= Song.sounding Y τ β γ (legs (s,x) i)
def garner (τ : Clip) (β γ : ℝ) (n k : ℕ) (x:Site c) (U: Config G c):= ∑ s : Signed, ∑ i∈ Meadow.ripened Y n k, Meadow.spurs Y τ β γ s i x U
end mellow
end YM.PhysicalNext.Repeat.Meadow
