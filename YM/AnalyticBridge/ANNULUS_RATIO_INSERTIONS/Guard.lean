import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Region


/-!
# Keep the actual prerequisites through substitution

A broad aperture choice compatible with the LFR packet charts. Use `late`
lemmas later, here at any height fulfilling the quote. We recommend setting
the E broad AND frozen-shell apertures post-L together (larger than
both sets of post-L prices), then obtaining all receipts incl Ledger
at this K. Does not retrofit bills committed for SectorChange alone.

Keep Wide locally thru D+5, even when other factors are no longer intact.
Keep broad gates on a local ACTIVE set incl up to D + one whole B from
the owner sites. This suffices through even LFR's larger `thin` extent
on the shot-selected coordinates. Requires no promise about realizability
elsewhere. No change of covariance, or assuming Y lies on shell patches
at any more links. After defaults dropped, other hard lookups, e.g.
activity or likelihood reads, may need *additional* gates. Consumer need
never remove the ones here to get these bounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented
-- physical and reserve notation clashes between LFR & SC; use the Gaussian ones
-- explicitly via Next.SectorChange where needed
open SectorNext.Remainder.Affine Harvest
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Local chart reads (caller halo can be bigger).
Positive initial endpoint test in common coordinates. LFR orientation
change costs an additional one in converting their chord halo. -/
def localDoors (O A : Stores S) (F : Forest S.ratio) (x : ℝ) (R : ℕ) := (Finset.univ : Finset (Active A x F)).filter
    fun i => S.ratio.parent i.val.val.1 ∈ O.dome R

def border (O A : Stores S) (F : Forest S.ratio) (x : ℝ) (R : ℕ) (q : Chi) (d : ℝ)
    (a : Prices G (Active A x F)) := ∏ i ∈ localDoors O A F x R, broad q d (tape a i)

lemma opened {O A : Stores S} {F : Forest S.ratio} {x d : ℝ} {R : ℕ} (q : Chi) (a : Prices G (Active A x F))
    (he : border O A F x R q d a ≠ 0) {i : Active A x F} (h : S.ratio.parent i.val.val.1 ∈ O.dome R) (hd : 0<d) :
    ‖tape a i‖ < 2*d := by
  apply broad_span q hd
  intro hv; exact he (show border .. = 0 from Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i,h⟩) hv)



variable (A : Stores S) (F : Forest S.ratio) (x : ℝ) (V : Config G c)
variable (Y : LinkArray G (Frozen A x F)) (q : Chi) (d : ℝ) (W : Stencils S) (a : Prices G (Active A x F))

local notation "R₀" => (replica S.ratio V)
local notation "U₀" => physical A F V Y (tape a)

lemma on_active (i : Active A x F) : U₀ i.val.val = (G.lieExp (tape a i)) * R₀ i.val.val := by
  unfold physical
  rw [show F.drape _ i.val.val = returned A F V Y (tape a) i.val from F.off_tree ..]
  unfold returned thaw
  rw [freeze_regular]; rfl

lemma on_frozen (i : Frozen A x F) : U₀ i.val.val = Y i := by
  unfold physical
  rw [show F.drape _ i.val.val = returned A F V Y (tape a) i.val from F.off_tree ..]
  exact freeze_held ..

lemma on_fixed (i : Bond f) (hi : i∈F.trunks) : U₀ i = 1 := F.on_tree _ ⟨i,hi⟩

lemma common_active (i : Active A x F) : common x V W A F q d Y a i.val.val = tape a i := by
  unfold common Rows.input fresh
  rw [Pi.add_apply, dif_pos i.val.property, dif_neg (show ¬ chill A x F i.val from i.property),
    dif_pos i.val.property, dif_pos i.property, zero_add]

lemma common_frozen (i : Frozen A x F) : common x V W A F q d Y a i.val.val = autoShell q d V Y i := by
  unfold common Rows.input fresh
  simp only [Pi.add_apply,dif_pos i.val.property,dif_pos i.property,dif_neg (not_not_intro i.property),add_zero]

lemma common_tree (i : Bond f) (hi : i∈F.trunks) : common x V W A F q d Y a i=0 := by
  unfold common Rows.input fresh
  simp only [Pi.add_apply,dif_neg (not_not_intro hi),add_zero]

/-- Frozen or tree has precisely the patched-log read even before
using smallness (on tree read actual replica=1). -/
lemma patched_fixed {i : Bond f} (h : ∀ j : Active A x F,i ≠ j.val.val) :
    common x V W A F q d Y a i = patched q d (U₀ i * (R₀ i)⁻¹) := by
  by_cases he : i∈F.trunks
  · rw [common_tree A F x V Y q d W a i he,on_fixed A F x V Y a i he]
    rw [show R₀ i=1 from if_pos (F.trunk_internal he),inv_one,mul_one]
    unfold patched
    by_cases hi : (1:G.El) ∈ firstChart G
    · rw [Set.indicator_of_mem hi]; simp [LocalH.snap,G.mat_one,G.plog_one]
    rw [Set.indicator_of_notMem hi]
  let i' : F.Free := ⟨i,he⟩
  have hx : chill A x F i' := by by_contra hz; exact h ⟨i',hz⟩ rfl
  rw [show U₀ i=Y ⟨i',hx⟩ from on_frozen A F x V Y a ⟨i',hx⟩]
  exact common_frozen A F x V Y q d W a ⟨i',hx⟩

/-- In either orientation: on the held arguments no change to frozen Y, use our
actual shell extension, not a log computed on the new copy of the field
without the adjoint flip. This identity holds even way outside chart margin. -/
lemma patched_turn (s : Signed) (i : Bond f) (h : ∀ j : Active A x F,sendEdge s 0 i ≠ j.val.val) :
    orientedLog x V W A F q d Y a s i = patched q d (pull s 0 U₀ i*(replica S.ratio (pull s 0 V) i)⁻¹) := by
  rw [← turn_replica,turn_read,turn_read,orientedLog,in_eval,patched_fixed A F x V Y q d W a h]
  split
  next hu =>
    let g := R₀ (sendEdge s 0 i); let u := U₀ (sendEdge s 0 i)
    change (- G.adjoint g⁻¹) (patched q d (u*g⁻¹))=patched q d (u⁻¹*(g⁻¹)⁻¹)
    rw [show u⁻¹*(g⁻¹)⁻¹ = g⁻¹*(u*g⁻¹)⁻¹*(g⁻¹)⁻¹ by group, patched_covary,patched_inv,map_neg]
    rfl
  rfl

/-- Joint aperture for this instance. Cleans produced even on `Wide`, which buys chord
*relative* to the correctly rotated replica on the whole needed thin halo.
Frozen-shell identity on selected addresses (overpay with that halo); any
regular log is bounded by its own kept chart.
-/
lemma in_patch {O : Stores S} {D R : ℕ} {s : Signed} {t : Site c} {L : Side} {K K₀ : ℝ}
    (hs : t ∈ (turnStore s O).dome (D*radiusB x)) (ht : S.patch.L=L) (hC : K₀ ≤ K)
    (hk : d=K*fiery G x L) (hd : 0<fiery G x L) (hL : 0<d) (hh : d<firstRadius G)
    (hb : 2 ≤ radiusB x) (hp : (D+1)*radiusB x ≤ R) (he : border O A F x R q d a ≠ 0)
    (H : ∃ a' : Directions G f, Cleans (S:=S) K₀ x (pull s 0 U₀) (pull s 0 V) t a') :
    PatchInputs (S:=S) (pull s 0 U₀) (pull s 0 V) (orientedLog x V W A F q d Y a s) (2*K) x t := by
  obtain ⟨l,h⟩:= H
  intro i hi
  let e := sendEdge s 0 i
  have hl := h.chart i hi
  by_cases hu : ∃ j : Active A x F,e=j.val.val
  · obtain ⟨j,hj⟩ := hu
    constructor
    · rw [← turn_replica]
      unfold orientedLog
      rw [← congr_fun (mount _ (common x V W A F q d Y a) s) i,turn_read,turn_read]
      unfold e at hj; rw [hj, on_active A F x V Y a j]
      unfold increment; rw [common_active]
    rw [orientedLog,in_size]
    unfold e at hj; rw [hj,common_active]
    have hc : S.ratio.parent j.val.val.1∈O.dome R := by
      rw [← hj]
      obtain ⟨y,hy,ht'⟩ := halo_spec.mp ((turn_dome ..).mp hs)
      apply halo_spec.mpr; refine ⟨y,hy,?_⟩
      have hu := spin_separation (S:=S) i s t
      have he' := separation_triangle y (s.act t) (S.ratio.parent (sendEdge s 0 i).1)
      unfold thin at hi
      rw [Nat.add_mul,Nat.one_mul] at hp; change separation t (S.ratio.parent i.1) ≤ _ at hi; omega
    have hv := opened q a he hc hL
    rw [ht]
    apply hv.le.trans_eq
    rw [hk]; ring
  have h' : ∀ j : Active A x F,e≠j.val.val := fun j ht => hu ⟨j,ht⟩
  unfold increment
  rw [patched_turn A F x V Y q d W a s i h']
  let R := replica S.ratio (pull s 0 V) i
  let u := pull s 0 U₀ i
  have hx : G.lieExp (l i) * R = u := hl.1.symm
  have he' : ‖l i‖ ≤ d := by
    apply hl.2.1.trans
    rw [ht,hk]; gcongr
  change u = G.lieExp (patched q d (u*R⁻¹))*R ∧ _
  have hy : u*R⁻¹=G.lieExp (l i) := by rw [← hx]; group
  rw [hy,patched_agrees q hL hh he']
  refine ⟨hx.symm, he'.trans ?_⟩
  rw [ht]; linarith [show 0 < K*fiery G x L by rw [← hk]; exact hL]


def Aperture (P : Teller G) (L : Side) (w K x : ℝ) :=
  let d := K*fiery G x L
  0<fiery G x L ∧ 0<d ∧ d<firstRadius G ∧
  2≤radiusB x ∧ (∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → 100*(1+radiusB x)≤c.val → P.Funds S T →
      span S.patch x ≤ radiusB x / 50 ∧
      ∀ (D : ℕ) (F : Forest S.ratio) (O A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c),
      SliceSet S F U → Wide O A D x w U k V → ∀ p : Site c, inSweep O A D (radiusB x) p →
        ∃ (X : ℝ) (a : Directions G f), X≤K ∧ Cleans (S:=S) X x U V p a)

variable {O : Stores S} {P : Teller G} {L : Side} {w K : ℝ}
/-- Sufficient buys. Keep the real curved increments, even if using the comparison
later on a branch not at the allocation's globally realizable U. -/
lemma licensed {l D R : ℕ} (hx : (D+1)*radiusB x ≤ R) (hh : S.patch.L=L) (hs : 100*(1+radiusB x) ≤ c.val)
    {k : S.Choices} {T : Tube G S} (hT : P.Funds S T) (hA : Aperture P L w K x) (hd : d=K*fiery G x L)
    (hl : D ≤ l) (ht : 5≤l) (h : Isle O A l (radiusB x))
    (he : Wide O A D x w U₀ k V) (hz : border O A F x R q d a ≠ 0) :
    ∀ s, Ensures U₀ V O (Harvest.crown x O D) (clipping x A F O D) x k
      (orientedLog x V (shots S x) A F q d Y a) w (2*K) D F A s := by
  have hU : SliceSet S F U₀ := on_fixed A F x V Y a
  let M s := Harvest.crown x O D s; let E s := clipping x A F O D s
  obtain ⟨hv,hv',hG,hB,-,hk⟩ := And.intro hA.1 (And.intro hA.2.1 (And.intro hA.2.2.1 (And.intro hA.2.2.2.1 (hA.2.2.2.2 _ _ S T hh hs hT))))
  rw [← hd] at hv' hG
  intro s
  have hm : (E s).selects (M s) := emitted_selects ..
  have hi := h.turn s
  have hr : (M s).annulus (turnStore s O) (turnStore s A) D (radiusB x) := earns hl (by omega) hi
  have hf := turn_wide s (funds_branch hT) he
  refine ⟨hi.owns ht,hf,hm,hr,?_⟩
  have help t (h : inSweep (turnStore s O) (turnStore s A) D (radiusB x) t) :
      PatchInputs (S:=S) (pull s 0 U₀) (pull s 0 V) (orientedLog x V (shots S x) A F q d Y a s) (2*K) x t := by
    obtain ⟨X,b,hX,H⟩ := hk D (turnForest s F) (turnStore s O) (turnStore s A) _ (choice s k) (pull s 0 V)
      (turn_sliced s F U₀ hU) hf t h
    exact in_patch A F x V Y q d _ a h.2 hh hX hd hv hv' hG hB hx hz ⟨_,H⟩
  exact ⟨fun i hy => help _ (hr.1 i (hm.1 hy)),fun i hy => help _ (hr.2.1 i (hm.2 hy))⟩

end YM.AnalyticBridge.AnnulusRatioInsertions
