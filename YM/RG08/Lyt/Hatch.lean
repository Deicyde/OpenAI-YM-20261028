import YM.RG08.Lyt.Bearing
/-! # Native-stride traversal. Exponential preserved. No tail assumption. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Lyt
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries
open scoped BigOperators Topology Real ContDiff Classical
open Wings Summit
variable {X:Chain}{G:Gauge}{D d k t n τ s E e i j r:ℕ}{w':ℝ}{T:Labels.Frame G d}{H:SectionData T}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{hp:1/2≤w'}{hD:d+1 ≤ D}{h:Hol G}{M:Signals P Q E τ h H hp hD}{ν:G.ColorIndex}{D':ChartRatio G}{S:Prism G X.kernel g Q E}
variable {I J:Type}{u:I→Windows}{b:J→ShoreP u}{v:Wall b 1→ Wings u 1}
local notation "Ⓨ"=> wallY X
-- translate proven (poly) abstract Traverse via zero-weight trick: reweight roots by ℓ at this step for P. Want iterate Q contract also with different w. lift recurrence exactly with scaling at each bead then use Traverse k=0. normal produces.
section travel
variable {Y α:Type} [NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y]{w:Wall b 0→ ℝ}{p:J→ℝ}{A:Wall b 0→ Rooted Y α r}{B:Wall b 1→ Rooted Y α r}
def markU (A:Rooted Y α r)(w:ℝ): Rooted Y α r:= fun i=> ling w i • A i
lemma mark_kind (z: Rooted Y α r)(w C:ℝ) : Quire.Lit z w C ↔ cis 0 1 (markU z w) C := by
   unfold Quire.Lit cis Quire.Ink; simp only [tailP,pow_zero,one_mul,markU,norm_smul,Real.norm_of_nonneg (ling_pos _ _|>.le)]
lemma hatch (hb:0≤p)(hx: Tin (fun i=>Ⓨ (Wall.tip b i)) p (fun j=>A (Wall.tip b j)) (fun j=>w (Wall.tip b j)))
    (h:∀ (t: Wall b 1) (C:ℝ), Quire.Lit (A t.roof) (w t.roof) C→ Quire.Lit (B t) (w t.low) (C * gain X.S (1/2) t.i (t.i+1)))
    (he : Tin (wallY X) (strideP X b p) (fun j: Wall b 1=> A j.low-B j) (fun i=>w i.low)): Tin Ⓨ (strideP X b p) A w:= by
   let P i:= markU (A i) (w i); let Q t:= markU (B t) (w t.low)
   have hx' : Card 0 (fun i=>Ⓨ (Wall.tip b i)) p (fun i=>P (Wall.tip b i)) 1:= ⟨_,hx.serves.choose_spec.1,fun i=> (mark_kind ..).mp (hx.serves.choose_spec.2 i)⟩
   have he' : Card 0 Ⓨ (strideP X b p) (fun t:Wall b 1=> P t.low-Q t) 1:= ⟨_,he.serves.choose_spec.1,fun i=>by rw [show P i.low-Q i=markU (A i.low-B i) (w i.low) from funext fun b=> (smul_sub ..).symm]; exact (mark_kind ..).mp (he.serves.choose_spec.2 i)⟩
   obtain ⟨B,hB,H⟩:=(traverse hb (v:=fun _=>1) (fun _=>zero_le_one) hx' (fun j c he=>(mark_kind ..).mp (h j c ((mark_kind ..).mpr he))) he').money
   exact ⟨B,hB,fun i=> (mark_kind ..).mpr (H i)⟩
lemma ascendM (hp:0≤p)(h: Weighed (wallY X (b:=b) (n:=1)) (fun i=> ((X.S.block i.i).val:ℝ)))(he:Tin (wallY X) (strideP X b p) A w): Tin Ⓨ (strideP X b p) (fun i:Wall b 1=> A i.roof) (fun i=>w i.roof):=by
   have hu: Card 0 Ⓨ (strideP X b p) (fun i=>markU (A i) (w i)) 1:=⟨_, he.serves.choose_spec.1, fun i=>(mark_kind ..).mp (he.serves.choose_spec.2 i)⟩
   obtain ⟨b,h,H⟩:=(hu.up h hp).money; exact ⟨b,h,fun i=> (mark_kind ..).mpr (H i)⟩
end travel
section projection
variable {I₀:Type}{A:I₀→ReadsU T D w'}{S:I₀→ Native (Letter T)}{y δ w:I₀→ℝ}
lemma over_s (hp: Audience y) (he:∀ i≤e,∀ b r, Tin y 1 (fun j=> A j b i r) w)(hv:∀ i,Boards (A i))(hm:∀ j v,j < e∨ j=e∧ r ≤ slot v → Dig y δ (fun i=> coeff j (S i v))): Tin y δ (fun i=> edgeBook (A i) (S i) e r) w:= by
    simp_rw [accounting]; refine Tin.additions _ hp (f:=fun j i=>∑ a∈range (e+1),_) fun i _=> Tin.additions (range (e+1)) hp (f:=fun j a=> coeff j (S a i) • A a i (e-j) r) (fun j hj=> ?_)
    by_cases hz:r ≤ slot i+(e-j); swap
    · simp_rw [show ∀ a:I₀,A a i (e-j) r=0 from fun a=>not_ne_iff.mp (mt (((hv a).rank i).cap _ _) hz),smul_zero]; exact Tin.zero
    exact dig_scale (he _ (Nat.sub_le ..) _ _) (hm _ _ (by have he:=mem_range_succ_iff.mp hj; omega))
end projection
end YM.RG08.Lyt
