import YM.AnalyticBridge.RESET_INCOME_PORT.Use
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Festal
/-! # Geometry of Pennies. Shape posts independent K.Witness.
 No shape consistency on native ranking; Lift masks by covers.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
section rolls
variable (hC) (V:Config G c) (x : Site C) (g D:ℕ)
local notation "p" => normal (divides hC) hC
local notation "Lq" => Macrame.splitter (Deck.divides hC)
include hC
lemma touches_here (i:Cell C): RG.touched (curr Lq i)=(touched i).image Lq:= by
  have hx (k:Walk) (x:Site C) : (visits x k).map (Lq) = visits (Lq x) k:= by
    induction k generalizing x with
    | nil => simp [visits]
    | cons i k H=> rw [visits,visits,List.map_cons,H]; rw [show Lq (x+i.vec)=_ from (p).uniform ..]; rfl
  unfold touched; change (visits (Lq i.1) (square i.2.val.1 i.2.val.2)).toFinset = _; rw [← hx]; ext z; simp
variable (hm:c.val>4)
include hm
lemma touched_by (i:Cell c) (x:Site C) (ht:Lq x∈ RG.touched i):∃ j:Cell C,curr Lq j=i ∧ x∈touched j:= by
  let y:= Deck.rise (Deck.divides hC) x i.1; let j:Cell C:= (y,i.2); have hj:curr Lq j=i:=Prod.ext (dawns ..) rfl
  rw [← hj,touches_here hC] at ht; obtain ⟨z,hz,hq⟩:= mem_image.mp ht; have h : x=z:= by
    apply tiniest (Deck.divides hC) hq.symm; apply lt_of_le_of_lt (separation_triangle x y z); have hv: separation x y≤ 2:= by
      apply (climb (Deck.divides hC) x i.1).trans_le; rw [separation_comm]; apply Work.E01.sep_touched _ _ ?_; rw [← hj,touches_here hC]; exact mem_image.mpr ⟨z,hz,hq⟩
    have ht:separation y z≤ 2:=Work.E01.sep_touched j z hz; omega
  exact ⟨j,hj,h.symm ▸ hz⟩
lemma flagged (t:ℝ) : x∈RG.flags t ((p).links V)↔ Lq x∈RG.flags t V:= by
  rw [flags_spec,flags_spec]; constructor
  · rintro ⟨j,hx,h⟩; rw [mirror] at h; exact ⟨_,touches_here hC j|>.symm ▸ mem_image_of_mem _ hx,h⟩
  rintro ⟨j,h,hx⟩; obtain ⟨i,rfl,hi⟩:= touched_by hC hm j x h; exact ⟨i,hi,mirror _ hC V i|>.symm ▸ hx⟩ -- replace
lemma vigor (t:ℝ) (J:Support C) : Healthy t J ((p).links V) ↔ Healthy t (J.image Lq) V:= by
  unfold Healthy; rw [disjoint_left, disjoint_left]; constructor
  · intro h i hi hk; obtain ⟨z,hz,rfl⟩:=mem_image.mp hi; exact h hz ((flagged hC V _ hm t).2 hk)
  intro h i hi hq; exact h (mem_image_of_mem (Lq) hi) ((flagged hC V _ hm t).1 hq)
lemma voyages (J:Support C): RG.inspected (J.image Lq)=(inspected J).image Lq:= by
  simp_rw [RG.inspected, image_union]; congr 1
  ext i; constructor
  · intro hi; obtain ⟨j,hj,hv⟩:= mem_biUnion.mp hi; split at hv
    · simp at hv
    rename_i hz; obtain ⟨x,hX,hv'⟩:= not_disjoint_iff.mp hz; obtain ⟨y,hy,rfl⟩:= mem_image.mp hX
    obtain ⟨k,rfl,h⟩:= touched_by hC hm j y hv'; rw [touches_here hC] at hv; obtain ⟨z,hz,rfl⟩:=mem_image.mp hv; apply mem_image_of_mem; refine mem_biUnion.mpr ⟨k,mem_univ _,?_⟩; rw [if_neg (show ¬ Disjoint J (touched k) from not_disjoint_iff.mpr ⟨_,hy,h⟩)]; exact hz
  intro h; obtain ⟨z,hz,rfl⟩:= mem_image.mp h; obtain ⟨j,hj,hv⟩:=mem_biUnion.mp hz; split at hv
  · simp at hv
  rename_i hx; obtain ⟨x,hm,hq⟩:= Finset.not_disjoint_iff.mp hx; refine mem_biUnion.mpr ⟨curr Lq j,mem_univ _,?_⟩; rw [touches_here hC, if_neg (show ¬Disjoint _ _ from not_disjoint_iff.mpr ⟨Lq x, mem_image_of_mem _ hm,mem_image_of_mem _ hq⟩)]; exact mem_image_of_mem _ hv
omit hm
lemma ringed (J:Support C) (k:ℕ) : halo k (J.image Lq)=(halo k J).image Lq := by
  ext i; constructor
  · intro h; obtain ⟨j,hj,hm⟩:= halo_spec.mp h; obtain ⟨x,hx,rfl⟩:= mem_image.mp hj; let f:= Deck.rise (Deck.divides hC) x i; exact mem_image.mpr ⟨f,halo_spec.mpr ⟨x,hx,(climb _ x i).trans_le hm⟩,dawns ..⟩
  intro h; obtain ⟨j,hj,rfl⟩:= mem_image.mp h; obtain ⟨x,hx,hq⟩:=halo_spec.mp hj; exact halo_spec.mpr ⟨_,mem_image_of_mem _ hx,(less (divides hC) x j).trans hq⟩
lemma inclined (i:Site C) : neighbors g (Lq i)=(neighbors g i).image Lq:= by
  -- convert from Halo
  have ht {c:Side} (i:Site c) : neighbors g i=halo g {i}:= by ext j; simp only [neighbors_mem,halo_spec]; simp
  simp_rw [ht, show ({Lq i}: Support c) = (({i}: Support C).image Lq) from (Finset.image_singleton ..).symm,ringed hC]
lemma steadied (A:Atom G D) : A.footprint (Lq x)=(A.footprint x).image Lq:= by unfold Atom.footprint; rw [image_image]; apply image_congr; intro i _; exact ((p).rooted ..).symm
include hm
lemma acts_c (A:Atom G D) (g:BudgetPoint) : A.placed g ((p).links V) x=A.placed g V (Lq x):= by
  unfold Atom.placed; rw [steadied hC]; by_cases hp : Healthy g.threshold (A.footprint x) ((p).links V)
  · rw [masked_eq _ _ _ _ hp,masked_eq _ _ _ _ ((vigor hC V hm ..).1 hp)]; unfold Atom.unmasked Slot.atSite; simp_rw [(p).expansion]; rfl
  rw [masked_ne _ _ _ _ hp, masked_ne _ _ _ _ ((vigor hC V hm ..).not.mp hp)]
end rolls
section aug
variable (hC he)
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
include hC he
abbrev turn_down (v:Lace h H M) (i: Trans F) : Trans f:= (i.1,v.high.cut i.2.1,i.2.2)
lemma projectionA (l k:ℕ) (A: ℕ→ Atom G D') (g: Trans F) (hh:f.val>4): atomFoot (decreed h) l k A (turn_down (L) g)= (atomFoot (decreed H) l k A g).image ((L).low.cut) := by
  let B:= L; let x:=g.2.1; let i:=g.2.2; let s:=g.1
  unfold atomFoot; change (enlargement _ l k (inspected ((A i).footprint (B.high.cut x)))).image (affine s 0) = _
  have hx : (A i).footprint (B.high.cut x)= ((A i).footprint x).image B.high.cut:= steadied (fineP h H hC) x D' (A i) -- fix
  rw [enlargement,enlargement, hx,show inspected (((A i).footprint x).image B.high.cut)= (inspected ((A i).footprint x)).image B.high.cut from voyages (fineP h H hC) hh _, image_image]
  let U:=(inspected ((A i).footprint x)).image (decreed H).parent
  rw [show ((inspected ((A i).footprint x)).image ((decreed h).parent ∘ B.high.cut)) = U.image B.low.cut from (by unfold U; rw [image_image]; apply image_congr; intro j _; exact B.position _)] -- image composition def
  change (halo _ (U.image (Macrame.splitter (Deck.divides hC)))).image _= _; rw [ringed hC,image_image,image_image]
  apply image_congr; intro j _; change affine s 0 _=((L).low.cut (affine s 0 j)); unfold Lattice.affine; simp_rw [add_zero]; exact usual (divides hC) s j
end aug
end YM.PhysicalNext.Repeat.Deck
