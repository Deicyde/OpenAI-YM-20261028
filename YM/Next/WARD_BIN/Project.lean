import YM.Next.WARD_BIN.Degree
import YM.Next.WARD_BIN.Stencils
import YM.Work.G01
import YM.Work.G02



/-!
# Project local finite cylinders to the label space

Actually weighted jets of the chosen `Hol`. Compute the whole finite Taylor
polynomial if needed, no clipping flags on the link curve. Price lower orders using
smoothness and the good-set derivatives. Smoothness here from `Affordable`
and continuity along increments; no extrapolations across discontinuous masks.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Work.G07 Bid Work.G05
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {k : ℤ} {d n l : ℕ} {S : Finset Cover}

abbrev curve (H : Hol G) (A : Snap G d) := H.links d (expand d A) 1

lemma curve_zero (H : Hol G) (d : ℕ) : curve H (d:=d) 0=1 := funext fun i => (Work.G02.linkGerm H d i).2.1

lemma expand_color (v : G.El) (A : Snap G d) : expand d (Cast v A) = colored v (expand d A) := by
  funext i; by_cases h:i<d-1 <;> simp [expand,Cast,h,colored]

lemma curve_cast (H : Hol G) (v : G.El) (A : Snap G d) : curve H (Cast v A) =
    Lattice.gauge (fun _ => v) (curve H A) := by rw [curve, expand_color, Work.G01.links_colored]

lemma plot (H : Hol G) (i : Edge Cover) (d : ℕ) : ContDiffAt ℝ ∞ (fun A : Snap G d => G.mat (curve H A i)) 0 :=
  (Work.G02.linkGerm H d i).1.contDiffAt.of_le le_top

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]

namespace Affordable

lemma smooth_poly {f : CoverConfig G → T} (h : Affordable S k f) (H : Hol G) (d : ℕ) :
    ContDiffAt ℝ ∞ (fun J : Snap G d => f (curve H J)) 0 := by
  obtain ⟨n,hn⟩:=someFits S
  let q := (0:Site n)
  let U := (1:Config G n)
  let F (p : Snap G d) := above q (curve H p)
  have hf : F 0=U := by unfold F; rw [curve_zero]; rfl
  let L (t : Snap G d) (e : Edge (Site n)) := G.plog (G.mat (F t e * (U e)⁻¹))
  have he (i : Edge (Site n)) : ContDiffAt ℝ ∞ (fun t : Snap G d => G.mat (F t i * (U i)⁻¹)) 0 := by
    change ContDiffAt ℝ ∞ (fun t : Snap G d => G.mat (F t i)*G.mat ((U i)⁻¹)) 0
    exact (plot H _ d).mul contDiffAt_const
  have hc : ContDiffAt ℝ ∞ L 0 := contDiffAt_pi.mpr fun i => by
    have hp : ContDiffAt ℝ ∞ G.plog (G.mat (F 0 i * (U i)⁻¹)) := by
      rw [hf,mul_inv_cancel]; exact G.plog_diff.of_le le_top
    exact hp.comp (f:=fun t => G.mat (F t i * (U i)⁻¹)) (0:Snap G d) (he i)
  have hp (i : Edge (Site n)) : ContinuousAt (fun y : Snap G d => F y i) 0 :=
    (G.continuous_mat.isClosedEmbedding G.mat_injective).isInducing.continuousAt_iff.2 (plot H (Lattice.lift (i.1-q),i.2) d).continuousAt
  obtain ⟨h0,-,hA⟩ := exp_local U F 0 hf hp
  have ht : ContDiff ℝ ∞ (fun v => places q f (increment U v)) := h.fitted 0 hn q [] le_rfl U
  apply (ht.contDiffAt.comp (f:=L) 0 hc).congr_of_eventuallyEq
  filter_upwards [hA] with V hV
  change f _ = places _ f _; rw [show increment U (L V)=F V from hV]; exact (fromAbove h.uses hn q (curve H V)).symm
end Affordable

-- Coefficient extraction by grade. No arbitrary splitting into unrelated stencils.
variable {f : CoverConfig G → ℂ} (H : Hol G)

def crown (H : Hol G) (f : CoverConfig G → ℂ) (d : ℕ) (l n : ℕ) :=
    tile (Tensor.coeff (E:=Snap G d) (f ∘ curve H) l 0) n

lemma crown_pure : pureDegree (crown H f d l n) n l := tile_grade ..

lemma cast_mul_scalar (t : ℝ) (u : G.El) (v : Snap G d) : Cast u (t • v)=t • Cast u v := funext fun i => map_smul (Taylor.paint u) _ (v i)

lemma cast_engineered (t : ℝ) (u : G.El) (v : Snap G d) :
    Cast u (engineered t v)=engineered t (Cast u v) := funext fun i => map_smul (Taylor.paint u) _ (v i)

lemma crown_invariant (hf : Affordable S k f) (hp : GaugeInvariant f) : crown H f d l n ∈ invariantSpace G := by
  intro A u
  unfold crown
  rw [← tile_reads, ← tile_reads]
  apply congr_arg (leading n); funext t
  have he : trunk d (colored u A)=Cast u (trunk d A) := rfl
  let g := f ∘ curve (d:=d) H
  have hx := hf.smooth_poly H d
  have hz : ContDiffAt ℝ l g 0 := hx.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [he, ← cast_engineered, ← leading_tensor _ g hz, ← leading_tensor _ _ hz]
  apply congr_arg (leading l); funext s
  dsimp only [g, Function.comp_apply]; rw [← cast_mul_scalar,curve_cast,hp]

open scoped Classical in
/-- Pad by zero outside cutoff for labels, factor order restriction occurs later. -/
def crownAt (hf : Affordable S k f) (hp : GaugeInvariant f) (d l n : ℕ) : Label G d :=
    if h : n≤d then ⟨crown H f d l n, functor h, crown_invariant H hf hp⟩ else 0
where
  functor (h : n≤d) : crown H f d l n ∈ limited G d := by
    refine (MvPolynomial.mem_restrictSupport_iff ℂ).mpr fun i hi => ?_
    have ht := crown_pure H (l:=l) (n:=n) (d:=d) (MvPolynomial.mem_support_iff.mp hi)
    change height i≤d
    rw [weight_slot] at ht
    exact le_trans (show height i=n from congr_arg Prod.fst ht).le h

variable (hf : Affordable S k f) (hp : GaugeInvariant f)

lemma crownAt_ok (l : ℕ) (h : n ≤ d) : (crownAt H hf hp d l n).val=crown H f d l n := by
  unfold crownAt; rw [dif_pos h]

lemma crowned (d l n) : crownAt H hf hp d l n∈ Grade (n,l) := by
  by_cases h:n≤d
  · apply (pure_grade (n,l) _).mpr
    rw [crownAt_ok H hf hp l h]; exact crown_pure H
  rw [crownAt,dif_neg h]; exact Submodule.zero_mem _

/-- This specific unmasked projection into radial labels. -/
def readout (d : ℕ) (H : Hol G) {f : CoverConfig G → ℂ} (hf : Affordable S k f) (hp : GaugeInvariant f) : Label G d :=
    ∑ l ∈ Finset.range (d+1), ∑ n∈ Finset.range (d+1), crownAt H hf hp d l n

lemma grade_readout (hl : l ≤ d) (hm : n ≤ d) :
    gradePart (n,l) (readout d H hf hp) = crownAt H hf hp d l n := by
  classical
  unfold readout; rw [map_sum, Finset.sum_eq_single l]
  · rw [map_sum, Finset.sum_eq_single n, gradePart_self _ _ (crowned ..)]
    · intro a _ ha; apply gradePart_zero _ _ _ ?_ (crowned ..); exact fun H => ha (congr_arg Prod.fst H).symm
    intros H; simp at H; omega
  · intro i _ hi; rw [map_sum]; apply Finset.sum_eq_zero; intro a _
    apply gradePart_zero _ _ _ ?_ (crowned ..); exact fun H => hi (congr_arg Prod.snd H).symm
  intros H; simp at H; omega

set_option maxHeartbeats 600000 in
lemma reading (d) : Projects H (readout d H hf hp) f := by
  classical
  intro v
  let g := f ∘ curve (d:=d) H
  let A (t : ℝ) := engineered t (trunk d v)
  let B := readout d H hf hp
  have he : (fun h : ℝ => f (H.links d v h)) = g ∘ A := by funext t; rw [scales H]; rfl
  have hh t : Labels.read (scaleJet v t) B.val =
      ∑ l ∈ Finset.range (d+1), ∑ n∈Finset.range (d+1), t^n • Labels.read v (crownAt H hf hp d l n).val := by
    unfold B readout; simp only [AddSubmonoidClass.coe_finsetSum,map_sum,scaled_grade (n:=_) t v _ (crowned ..)]
  dsimp only; rw [he, funext hh]
  have hZ : A 0=0 := by funext; simp [A, engineered_at]
  have hA : ContDiffAt ℝ d A 0 := (eng_cont _ _).contDiffAt
  have hf0 : ContDiffAt ℝ d g 0 := (hf.smooth_poly H d).of_le (WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiffAt ℝ d g (A 0) := hZ ▸ hf0
  refine ⟨hg.comp 0 hA,ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => monoSmooth _ j _|>.contDiffAt,fun i hi => ?_⟩
  have hJ := jets_comp hA hA (blockTaylor_contDiff d g _|>.contDiffAt) hg rfl (fun _ _ => rfl)
    (hZ ▸ blockTaylor_jets hf0) i hi
  unfold iteratedDeriv; rw [← hJ]
  let K l := Tensor.coeff g l 0
  have hB : blockTaylor d g ∘ A = fun t : ℝ => ∑ l ∈ Finset.range (d+1),Tensor.diagonal (K l) (A t) := by
    funext t; simp only [blockTaylor,K,Function.comp_apply,Finset.sum_apply]
  apply smul_right_injective ℂ (show ((i.factorial:ℝ)⁻¹) ≠ 0 by positivity)
  rw [hB]; change leading i (fun t => ∑ l ∈ Finset.range (d+1),Tensor.diagonal (K l) (A t)) = leading i _
  have hA' (l) : ContDiffAt ℝ i (fun t => Tensor.diagonal (K l) (A t)) 0 :=
    (Tensor.diag_smooth (K l) (i:WithTop ℕ∞)).comp_contDiffAt 0 (hA.of_le (by exact_mod_cast hi))
  rw [lead_sum (f:=_) _ (fun l _ => hA' l), lead_sum]
  · apply Finset.sum_congr rfl; intro l hl
    rw [lead_sum (n:=i) _ (fun p t => (t^p:ℝ) • _) (by intros; exact (monoSmooth ..).contDiffAt)]
    simp_rw [lead_monomial, Finset.sum_ite_eq, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), if_true, crownAt_ok H hf hp _ hi]
    exact tile_reads (K l) _ _
  intro j _; exact ContDiffAt.sum fun l _ => (monoSmooth ..).contDiffAt

end YM.WardBin
