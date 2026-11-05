import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Read
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Change


/-!
# Gaussian kernel-row factors through E:H_{200}, same actual a mapping

Decompose the very exponent of dyed, including having paid the Gaussian
relative density (Frco). Include in the compulsory exponent also the
first term specialized to these rows. Set aside the Frco linear and
quadratic correction for further letters (NOT priced here, and not
charging them as if also with nonpositive sign).
-/
set_option autoImplicit false
-- Only stylistic lint disabled. All holes/axioms/declaration safety audited at entry.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.AnalyticBridge.Annulus1AD
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube MeasureTheory Tree
   Axial YM.Push.SectorMeasure Next.Fluctuations Metric Oriented Presented Exterior Bloch
open YM.Next.SectorChange YM.SectorNext.Remainder
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
open Affine
open scoped Matrix -- notation

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (T : Tube G S) (V : Config G c) (x : ℝ) (A O : Stores S) (k : S.Choices) (F : Forest S.ratio) (q : Chi)
  (d : ℝ) (Y : LinkArray G (Frozen A x F))
variable (M : Signed → Window S) (β : ℝ)

/-- drows minus affine squares at the specified list of anchors in
each channel. All at true a and U, with original tag likelihood elsewhere
applied using k. The average still to be performed. -/
def ownedAt (U : Config G f) (a : Prices G (Active A x F)) (s : Signed) : ℝ :=
  (M s).work T x (pull s 0 U) (choice s k) (pull s 0 V) - columns V x k T F A q d Y a s (M s)



def emission (m z : Prices G (Active A x F)) :=
  let g:=coupling β
  let a := m + g • z
  let U := landed x A F V Y a;
  -β* averaged (ownedAt T V x A k F q d Y M U a) - averaged (fun s => columns V x k T F A q d Y m s (M s)) / g^2



variable {σ Λ θ : ℝ} {o : Clip}





variable {x k A F d Y} {D R : ℕ} {P : Teller G}
lemma depositing {width rho W κ B H β L n}
    (hs : P.Funds S T) (hL : S.patch.L=L) (hl : 100*(1+radiusB x)≤c.val)
    (ha : PointCharge T x W κ) (h0 : Ledger P L W κ (2*width) H n D x)
    (hU : Authorized A V F x B) (hβ : β∈Set.Icc (Scales.y G L x/2) (2*Scales.y G L x))
    (ho : Packet O A R) (hw : (D+5)*radiusB x≤R) (hD : 2 ≤ D)
    (m z : Prices G (Active A x F)) :
    let d:=width*fiery G x S.patch.L
    let a:=m+coupling β • z
    let U := landed x A F V Y a
    span S.patch x ≤ radiusB x/50 →
    (∀ s, Wide (turnStore s O) (turnStore s A) D x W (pull s 0 U) (choice s k) (pull s 0 V)) →
    ((2+D)*radiusB x≤rho) →
    admitsHere A O x F q d (tape a) rho ≠ 0 →
    0<d → d<firstRadius G →
    (∃ K : ℝ, 1≤K ∧ K≤width ∧ (∀ s : Signed, ∃ u : Directions G f, ∀ i,
        inSweep (turnStore s O) (turnStore s A) D (radiusB x) i → Cleans (S:=S) K x (pull s 0 U) (pull s 0 V) i u)) →
    let M := fun s => anchorage (turnStore s O) (D*radiusB x)
    Real.exp (emission T V x A k F q d Y M β m z) ≤
      Real.exp (-κ/4 * (Scales.p G L x)^2 * O.shares - coin G L H n x * O.shares) ∧
    (∀ s, (harvest A O x F s D).written T x (choice s k) (pull s 0 V) (signedArray x A F q d V Y a s)) := by
  intro d a U hx hh hρ hv hp he hb M
  obtain ⟨K,hK,hk,hN⟩ := hb
  obtain ⟨l,τ,hT,-⟩ := hs.feeds
  have H₀ : 1≤radiusB x := by unfold span at hx; omega
  have H₁ : (D+2)*radiusB x≤R := (Nat.mul_le_mul_right _ (show D+2 ≤ D+5 by omega)).trans hw
  have H₂ : 5*radiusB x≤R := (Nat.mul_le_mul_right _ (show 5 ≤ D+5 by omega)).trans hw
  have hslice : SliceSet S F U := fun i hi => F.on_tree (Next.SectorChange.returned A F V Y (tape a)) ⟨i,hi⟩
  let v := signedArray x A F q d V Y a
  let ka s := harvest A O x F s D
  let bands s := bandRows (turnStore s O) D (radiusB x)
  have hh' s : (ka s).charts (pull s 0 U) (pull s 0 V) (v s) (2*width) x := by
    obtain ⟨u,h⟩ := hN s
    have he' (i : Site c) (hk' : inSweep (turnStore s O) (turnStore s A) D (radiusB x) i) :=
      preview q V Y a hp hk he H₀ hK (by rw [Nat.add_comm D]; exact hρ) hv s i hk' u (h _ hk')
    obtain ⟨hF,hB⟩ := harvesting (A:=A) (O:=O) (x:=x) (s:=s) (D:=D) (F:=F) hx ho
    obtain ⟨hJ,hN', -⟩ := band_bought (D:=D) (ho.turns s) H₁
    exact ⟨fun p ht => he' _ (hJ _ (hF ht)),fun i ht => he' _ (hN' _ (hB ht))⟩
  have H3 s : Ensures U V O bands ka x k v W (2*width) D F A s :=
    ⟨(ho.turns s).ownership H₂,hh s,harvesting hx ho,band_bought (ho.turns s) H₁,hh' s⟩
  obtain ⟨hi,h⟩ := used U V O bands ka k v F A hL hl hs β (2*width) H W κ D n ha h0 hβ hslice H3
  refine ⟨(Real.exp_monotone ?_).trans h,hi⟩
  have hk (s : Signed) : ownedAt T V x A k F q d Y M U a s=credits U V O bands ka T x k v s := by
    unfold ownedAt credits boost
    let U' := pull s 0 U; let V' := pull s 0 V; let O':=turnStore s O; let k':=choice s k
    have hw := band_bill T O' x k' U' V' hD
    unfold M v ka bands O' U' V' k' at *
    rw [← hw,extracting V x k T F A q d Y a s O D hT hU]; abel
  unfold emission; dsimp only
  change -β* averaged _- averaged _ / _ ≤ -β* averaged _
  unfold v M bands ka at hk
  unfold v M bands ka; change -β* averaged (ownedAt T V x A k F q d Y _ U a)- averaged _ / _ ≤ -β* averaged _
  rw [funext hk]
  refine sub_le_self _ (div_nonneg ?_ (sq_nonneg _))
  unfold averaged; apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun s _ => columns_nonneg ..

end YM.AnalyticBridge.Annulus1AD
