import YM.RG08.Germ.Template
import YM.RG08.Pace.Initial
import YM.Next.STATIONARY.FrameEst.Stencils
import YM.Work.F04.Choices

/-! # Kernel germ in the TRUE ROOT coordinates of the Wilson step

The ROOT frame is fixed, no extra centered variables integrated. Kernels
read at full cutoffs P,K independent of tag. Finite path support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
variable {α I : Type} {c f L m : Side} {P : Patch} {G : Gauge} {k : KernelChoices}
variable (S : StepData c f)

abbrev Fink (G : Gauge) (L : Side) := Co L (Loc G 1)
abbrev Park (G : Gauge) (L : Side) := Fink G L ⊕ Loc G 1
abbrev Alley (G : Gauge) (g : Ratio c f) := PAC (Park G g.count) c

def fineL (G : Gauge) (g : Ratio c f) : Alley G g →L[ℝ] Link G f :=
    ContinuousLinearMap.pi fun a=> let i := splitCo g (Loc G 1) a; ContinuousLinearMap.proj (i.1,Sum.inl i.2)
def coarseL (G : Gauge) (g : Ratio c f) : Alley G g →L[ℝ] Link G c :=
    ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (i.1,Sum.inr i.2)

def songs (G : Gauge) (S : StepData c f) : Alley G S.ratio →L[ℝ] Bang G c f :=
    ((coarseL G S.ratio).prod 0).prod (((fineL G S.ratio).prod 0).prod 0)
private def pianos (P : Patch) : Piano G P → Option (Cover × Park G P.L)
    | .inl (true,x,i) => some (carry (0:Site P.L) x.val,Sum.inl (arrives (0:Site P.L) x.val, i))
    | .inr (.inr (false,i)) => some (0,Sum.inr i)
    | _ => none
lemma piano_path (x : Alley G S.ratio) (i : Site c) : pianist S i (songs G S x)=seats (pianos S.patch) i x := by
  funext p
  rcases p with ⟨⟨⟩|⟨⟩,j,b⟩ | (⟨⟨⟩|⟨⟩,v⟩|⟨⟨⟩|⟨⟩,k⟩)
  · rfl
  · change fineL G S.ratio x (wrap f _+_,b)=x (i+wrap c _,.inl _)
    unfold fineL; rw [ContinuousLinearMap.pi_apply]; dsimp only [split_co,ContinuousLinearMap.proj_apply]
    have hy : (splitCo S.ratio (Loc G 1)) (wrap f j.val+S.ratio.embed i,b)=(i+wrap c (carry (0:Site S.ratio.count) j.val),Work.F08.arrives (0:Site S.ratio.count) j.val,b) := by
      rw [split_co,add_comm (wrap f _)]; simp only [moves_residue,moves_parent,Ratio.embed_parent,Ratio.residue_embed]
    rw [hy]; rfl
  · rfl
  · rfl
  · change x (i,Sum.inr k)=x (i+wrap c 0,Sum.inr k); simp
  rfl

private lemma root_bang (t : S.Choices) (h : S.patch.Branches S.kernel G) (x : Alley G S.ratio) :
    let y:=songs G S x
    Stationary.ribbon S t (atire (buffOn S t G true) (headOn S t true y) y.2.1)=S.prediction (input G f (fineL G S.ratio x)) t := by
  intro y; rw [headOn]; split; swap; · simp_all
  change Stationary.ribbon S t (atire 1 (dress (fedora S t) (Stationary.extend 0)) y.2.1)=_
  rw [extend_zero, dressed_one (fedora_style h t),atire,dress_one,mul_one]
  change Lattice.gauge _ _=_
  -- switch 0
  change Lattice.gauge (Stationary.extend (fineL G S.ratio x,(0:BaseSites G c))).2 (S.prediction (input G f _) t)=_
  have hx : (Stationary.extend (fineL G S.ratio x,(0:BaseSites G c))).2=1 := by change (Stationary.extend (0:Vault G c f)).2=_; rw [extend_zero]; rfl
  rw [hx,gauge_one]; rfl

private def canonMusic (P : Patch) (b : ℝ) (x : BassInput G P) := ∑ i,presentsBox true b x i
lemma music_h (P : Patch) (u : ℝ) (h : P.Branches k G) : AnalyticAt ℝ (canonMusic (G:=G) P u) 0 := (show ContDiffAt ℝ ω _ _ from ContDiffAt.sum (s:=univ) (fun i _=> presents_this h _ u i)).analyticAt

def noiseLaw (t : S.Choices) (x : Alley G S.ratio) : ℝ :=
    tickets S (input G c (coarseL G S.ratio x)) (S.prediction (input G f (fineL G S.ratio x)) t)
lemma noise_angles (t : S.Choices) (h : S.patch.Branches S.kernel G) : noiseLaw (G:=G) S t =ᶠ[𝓝 0]
    atmosphere (pianos S.patch) (canonMusic S.patch S.kernel.penalty) c := by
  let L:=songs G S
  have he : Tendsto L (𝓝 0) (𝓝 0) := by simpa only [map_zero] using L.continuous.tendsto 0
  filter_upwards [he.eventually (boom_line S t h true)] with x hx
  unfold L at hx
  rw [show Stationary.ribbon _ _ _=_ from root_bang S t h x] at hx
  simp_rw [piano_path] at hx; exact hx

section note
variable {w : ℝ} {r : ℕ}

def blot (u : G.ColorIndex) (P : Patch) (κ : ℝ) (r : ℕ) : Shale (Park G P.L) r := by
  classical
  exact breath (0, .inr (coord 0,u)) (pianos P) (canonMusic P κ) r
lemma blot_pays (P : Patch) (u : G.ColorIndex) (κ : ℝ) (h : 0≤w) :
    ∃ C : ℝ, 0 ≤ C ∧ Glow (blot u P κ r) w C := by classical exact breath_quote (ι:=Piano G P) _ _ _ _ h
lemma blot_sym (P : Patch) (u : G.ColorIndex) (κ : ℝ) : Tunable (blot u P κ r) := by classical exact breath_tune (ι:=Piano G P) ..
theorem blot_true (t : S.Choices) (u : G.ColorIndex) (h : S.patch.Branches S.kernel G) (r : ℕ) :
    AnalyticAt ℝ (noiseLaw S t (G:=G)) 0 ∧ Tensor.coeff (noiseLaw S t) r 0= recital (blot u S.patch S.kernel.penalty r) c := by
  classical
  have he := breath_proofs _ (music_h _ S.kernel.penalty h) (pianos S.patch) (0,.inr (coord 0,u)) c r
  exact ⟨he.1.congr (noise_angles S t h).symm, (Tensor.GermCoeff r (noise_angles S t h)).trans he.2.symm⟩
end note
-- physical density local tag collapse exact, probability Haar noise unchanged
lemma collapse_tags (t : S.Choices) (h : S.patch.Branches S.kernel G) : ∀ᶠ U : Config G f in 𝓝 1, ∀ V : Config G c,∀ β:ℝ,
    S.density β U V=S.noise β (S.prediction U t) V := by
  classical
  filter_upwards [eventually_all.mpr (fun r=> Work.F04.prediction_germ h r t)] with U hU V β
  unfold StepData.density; simp_rw [show ∀ r,S.prediction U r=S.prediction U t from hU]; rw [← Finset.sum_mul, S.chosen h U,one_mul]
end YM.RG08
