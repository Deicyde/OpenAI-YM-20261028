import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Mediator
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Pattern
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Powers
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Weighted
import YM.Next.FOUNDATIONS.LinkBounds

set_option warningAsError false

/-!
# Log-link map. Actual tested lattice support, screen to the support,
carried real positions evaluated via true lift at both endpoints
(nonwrapping AND side large, compare `Foundations.size_one` -- doesn't
follow from nonwrapping alone at the degenerate one-site boundary!).
No claim screens commute with RG or caps, used at the single vacancy
test only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Mom
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open Powers Mediator Next.Foundations Pattern
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {d : ℕ} {n : Side}

abbrev Slate (G : Gauge) (n : Side) (d : ℕ) := (Site n → G.Color) × Snap G d

abbrev needed (X : Support n) (x : Edge (Site n)) := x.1∈X ∧ x.1+Lattice.step x.2∈ X

def stamp (o : Site n) (x : Site n) := Pattern.xyz (lift (x-o))

def Sites (o : Site n) (X : Support n) (k : ℕ) : Submodule ℝ (Slate G n d) where
  carrier := {v | (∃ p : E4→G.Color, p∈space E4 G.Color k ∧ ∀ i∈X,v.1 i=p (stamp o i)) ∧
    ∀ i : Fin (d-1), k < i.val+2 → v.2 i=0 }
  zero_mem' := by refine ⟨⟨0,(space E4 G.Color k).zero_mem,fun _ _ => rfl⟩,fun _ _ => rfl⟩
  add_mem' := by
    rintro a b ⟨⟨p,hp,hP⟩,ha⟩ ⟨⟨q,hq,hQ⟩,hb⟩
    exact ⟨⟨p+q,(space E4 G.Color k).add_mem hp hq,fun i hi => congr_arg₂ (· + ·) (hP i hi) (hQ i hi)⟩,
      fun i hi => by change a.2 i+b.2 i=_; rw [ha _ hi,hb _ hi,add_zero]⟩
  smul_mem' := by
    rintro c a ⟨⟨p,hp,hP⟩,ha⟩; exact ⟨⟨c • p,(space E4 G.Color k).smul_mem _ hp,fun i hi => congr_arg (c • ·) (hP i hi)⟩,
      fun i hi => by change c • (a.2 i) = _; rw [ha _ hi,smul_zero]⟩

def Maps (o : Site n) (X : Support n) (i : ℕ) : Submodule ℝ (Directions G n) where
  carrier := {v | ∃ f : Axis → E4 → G.Color,(∀ j,f j∈space E4 G.Color (i-1)) ∧
    ∀ x, v x=if needed X x then f x.2 (stamp o x.1) else 0 }
  zero_mem' := ⟨0,fun _ => (space E4 G.Color (i-1)).zero_mem,fun x => by simp⟩
  add_mem' := by
    rintro a b ⟨p,hp,h⟩ ⟨q,hq,H⟩; refine ⟨p+q,fun j => (space E4 G.Color _).add_mem (hp _) (hq _),fun i => ?_⟩
    change a _+b _= _; rw [h,H]; split; rfl; simp
  smul_mem' := by
    rintro c a ⟨p,hp,h⟩; refine ⟨c • p,fun j => (space E4 G.Color _).smul_mem _ (hp _),fun i => ?_⟩
    change c • a _=_; rw [h]; split; rfl; simp

/-- Log links after local gauge. Values outside deliberately not tested. -/
def runway (o : Site n) (x : Edge (Site n)) : Slate G n d →L[ℝ] Panel G d := by
  let A : Slate G n d →ₗ[ℝ] Panel G d := {
    toFun v := (v.1 x.1,v.1 (x.1+step x.2)-v.1 x.1,tempo (stamp o x.1) x.2 v.2)
    map_add' a b := by
      refine Prod.ext rfl (Prod.ext ?_ (map_add (tempo _ _) a.2 b.2))
      change a.1 _ + b.1 _ - (a.1 _+b.1 _) = _; change _=(a.1 _- a.1 _)+(b.1 _- b.1 _); abel
    map_smul' c a := Prod.ext rfl (Prod.ext (smul_sub c _ _).symm (map_smul (tempo _ _) _ a.2)) }
  exact A.toContinuousLinearMap

def optic (X : Support n) (o : Site n) (v : Slate G n d) : Directions G n := fun i =>
    if needed X i then stereo G d (runway o i v) else 0

lemma osmotic (X : Support n) (o : Site n) : ContDiffAt ℝ ω (optic X o (G:=G) (d:=d)) 0 ∧ optic X o (0:Slate G n d)=0 := by
  constructor
  · apply contDiffAt_pi.mpr; intro i; unfold optic; by_cases h:needed X i
    · simp only [if_pos h]
      exact ((map_zero (runway (G:=G) (d:=d) o i)).symm ▸ (scripts G d).1).comp 0 (f:=runway o i) (ContinuousLinearMap.contDiff ..).contDiffAt
    simp only [if_neg h]; exact contDiffAt_const
  funext i; unfold optic; split
  · rw [map_zero,(scripts G d).2]; rfl
  rfl

lemma papertrail {o : Site n} {x : Edge (Site n)} (H : Hol G) :
    ∀ᶠ v : Slate G n d in 𝓝 0,
      G.lieExp (stereo G d (runway o x v)) = gauge (fun i => G.lieExp (v.1 i)) (H.testLinks d o (expand d v.2) 1) x := by
  have h := G02.linkGerm H d (lift (x.1-o),x.2)
  have hz : H.testLinks d o (expand d (0:Snap G d)) 1 x=1 := h.2.1
  have hs : ContinuousAt (fun v : Snap G d => H.testLinks d o (expand d v) 1 x) 0 :=
    (G.continuous_mat.isClosedEmbedding G.mat_injective).isInducing.continuousAt_iff.mpr h.1.continuousAt
  let S (v : Slate G n d) := gauge (fun i => G.lieExp (v.1 i)) (H.testLinks d o (expand d v.2) 1) x
  have hh : Tendsto S (𝓝 0) (𝓝 1) := by
    rw [← show S 0=1 by simp [S,Lattice.gauge,hz,- Drops.expand_zero]]
    have hf i : Continuous (fun x : Slate G n d => G.lieExp (x.1 i)) := by fun_prop
    exact (show ContinuousAt S 0 from ((hf _).continuousAt.mul (hs.comp_of_eq (continuous_snd.continuousAt (x:= (0:Slate G n d))) rfl)).mul (hf _).continuousAt.inv).tendsto
  filter_upwards [hh.eventually G.plog_right] with v hv
  change _=S v; rw [←hv]
  apply congrArg G.lieExp
  unfold S Lattice.gauge
  rw [G.mat_mul,G.mat_mul,G.mat_inv]
  let f := tempo (stamp o x.1) x.2 (d:=d) (G:=G)
  rw [show G.mat (H.testLinks d o (expand d v.2) 1 x)=run G d (f v.2) from stem H ..]
  apply congrArg G.plog
  change _ * run G d (f v.2)* star (G.mat (G.lieExp (v.1 x.1+(v.1 _-v.1 _))))=_
  rw [add_sub_cancel ..]
  rfl

lemma appears {o : Site n} {X : Support n} {p : Config G n → ℂ} (h : LocalOn X p) (hw : GaugeInvariant p) (H : Hol G) :
    (p ∘ increment 1) ∘ (optic X o)=ᶠ[𝓝 (0:Slate G n d)] (fun v => p (H.testLinks d o (expand d v.2) 1)) := by
  filter_upwards [Filter.eventually_all.mpr (papertrail (d:=d) (o:=o) H (x:=·))] with v hv
  apply Eq.trans (h _ _ (fun i hi hI => ?_)) (hw (fun i => G.lieExp (v.1 i)) _)
  change G.lieExp (optic X o v i)*1=_
  rw [mul_one,optic,if_pos (show needed X i from ⟨hi,hI⟩)]; exact hv i

section Scale

def deck (i : Fin (d-1)) : Snap G d →L[ℝ] Snap G d :=
    let Y : Snap G d →ₗ[ℝ] Snap G d := {
      toFun v := Pi.single i (v i)
      map_add' f g := by rw [Pi.add_apply,Pi.single_add]
      map_smul' c f := by funext j; by_cases H:j=i; subst j; simp
                          simp [Pi.single_eq_of_ne H] }
    Y.toContinuousLinearMap
lemma deck_at (v : Snap G d) (i : Fin (d-1)) : deck i v=Pi.single i (v i) := rfl
lemma decks (v : Snap G d) : (∑ i,deck i v)=v := by
  funext i
  simp [deck_at,Finset.sum_apply]
lemma deck_price (v : Snap G d) (h : ℝ) : Weighted.scaled (fun i : Fin (d-1) => i.val+2) (deck (G:=G)) h v=trunk d (scaleJet (expand d v) h) := by
  unfold Weighted.scaled; funext i
  simp only [Finset.sum_apply,Pi.smul_apply]; rw [sum_eq_single i]
  · simp [trunk,expand,scaleJet,deck_at]
  · intro j _ hj; rw [deck_at,Pi.single_eq_of_ne (Ne.symm hj),smul_zero]
  simp
end Scale

set_option maxHeartbeats 520000 in
lemma formal_null {o : Site n} {X : Support n} {p : Config G n → ℂ} (d : ℕ) (H : Hol G) (h : LocalOn X p) (hw : GaugeInvariant p)
    {j : ℕ} (he : ∀ J : Jet G,∀ l,l ≤ j → iteratedDeriv l (fun t => p (H.testLinks d o J t)) 0=0)
    (hp : ContDiffAt ℝ j (p ∘ increment 1) 0) : valence (fun i => (Sites o X i (G:=G) (d:=d):Set _)) j ((p ∘ increment 1) ∘ (optic X o (d:=d))) := by
  let A (v : Snap G d) := p (H.testLinks d o (expand d v) 1)
  let B := (p ∘ increment 1) ∘ (optic X o (d:=d))
  let L : Slate G n d →L[ℝ] Snap G d := ContinuousLinearMap.snd ℝ _ _
  let K : Snap G d →L[ℝ] Slate G n d := ContinuousLinearMap.inr ℝ _ _
  have hz v : L (K v)=v := rfl
  have ht : B=ᶠ[𝓝 0] (A ∘ L) := appears h hw H
  obtain ⟨hC,h₀⟩ := osmotic (G:=G) (d:=d) X o
  have hB : ContDiffAt ℝ j B 0 := (h₀.symm ▸ hp).comp (f:=optic X o) 0 (hC.of_le le_top)
  have hA : ContDiffAt ℝ j A 0 := by
    have hx : Tendsto K (𝓝 0) (𝓝 0) := by simpa using K.continuous.tendsto (0:Snap G d)
    refine ((show ContDiffAt ℝ j B (K (0:Snap G d)) from (map_zero K).symm ▸ hB).comp (f:=K) 0 K.contDiff.contDiffAt).congr_of_eventuallyEq
      ((ht.comp_tendsto hx).symm)
  have hs : Weighted.evolved (fun i : Fin (d-1) => i.val+2) (deck (G:=G)) j A := by
    intro v i hi
    simp_rw [deck_price, A, ← test_scaled]
    exact he _ i hi
  intro m a u ha
  have hv1 : ∀ i,1 ≤ a i := fun i => (ha.1 i).1
  have hM : m ≤ j := le_trans (by simpa using sum_le_sum (s:=Finset.univ) (f:=fun _ => 1) (fun i _ => hv1 i)) ha.2
  letI : NormedAddCommGroup (Slate G n d) := inferInstanceAs (NormedAddCommGroup ((Site n → G.Color) × Snap G d))
  letI : NormedSpace ℝ (Slate G n d) := inferInstanceAs (NormedSpace ℝ ((Site n → G.Color) × Snap G d))
  have hx := (ht.iteratedFDeriv ℝ m).eq_of_nhds
  change iteratedFDeriv ℝ m B 0 u=0; rw [hx,jets_linear L (hA.of_le (Nat.cast_le.mpr hM)), ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply Weighted.cancel (fun i : Fin (d-1) => i.val+2) (deck (G:=G)) _ (fun i => by omega) decks hs hA _ a hv1 ha.2
  intro i x hx
  rw [deck_at]
  change (Pi.single x ((u i).2 x) : Snap G d)=0
  rw [((ha.1 i).2.2 x hx),Pi.single_zero]
end YM.MultiNext.SignedSource.Mom
