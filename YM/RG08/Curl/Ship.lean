import YM.RG08.Scale.Mate
/-! # Expose canonical curvature completion on ordinary unmasked stencils

Not a hit estimate. Includes first TWO null moments on curvature for any positive
relative or difference loop, path lengths wire exact. Use after rates proven
on link kernels; none of these contractions needed on templates to close
repeated estimate. Arbitrary finite arity. -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Virtue
open Filter MeasureTheory Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free Conductor UVExt.Paths Push.AbsoluteSums
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {m : Side} {A B C σ η : ℝ} {r s d n : ℕ}
abbrev Atlas (G : Gauge) := ∀ m, Link G m → ℝ
variable {F : Atlas G}

-- specify at Skin for changing supports deterministically.
structure Mar (X : Skin G d) (B w : ℝ) : Prop where
   pass i j : Width w B (X i j)
   draws i j : (fun a=> X i a j) ∈ paints G (d+1)
lemma Mar.mono {X:Skin G d} (h : Mar X B σ) (he:B ≤ A)(hp:η≤σ) : Mar X A η := ⟨fun i j=> (h.pass i j).mono hp he,h.draws⟩
lemma Mar.plus {X Y:Skin G d}(hx:Mar X A σ)(hy:Mar Y B σ):Mar (X+Y) (A+B) σ := ⟨fun i j=> Charge.add (hx.pass i j) (hy.pass i j) (fun _=> (Real.exp_pos _).le),fun i j=> (paints G (d+1)).add_mem (hx.draws i j) (hy.draws i j)⟩
lemma Mar.pathways [NeZero d] {X:Skin G d}(h : Mar X B σ) : AtomWall (Stationary.issue X) σ (B*inkCost G d σ) := by
  exact ⟨budget_copy (carrierPath d) (realpath_price h.pass), fun i=> (show _ from h.draws (carrierPath d i).1 _)⟩

variable (G)
private abbrev Periods := Side
private def flights (i : ℕ) : Side:=⟨i+1,Nat.succ_pos _⟩
private lemma fills : Tendsto (fun i=>(flights i).val) atTop atTop := tendsto_add_atTop_nat _

-- suppress Ward in f only costs at k+1

def Foil (F : Atlas G) (k:ℕ) (w C : ℝ) := ∃ L : Picture G k,(∀ i j,Firm w C (L i j)) ∧ ∀ m,Recorded L (F m) 0
lemma reaps [NeZero d]{G: Gauge}{V:Link G m→ℝ}(h : Pointwise V)(hp:Rays (d+1) V){X:Skin G d} {L:Picture G d}(hx : Recorded L V 0)(he:Shades X L σ A)(hσ:0<σ): Rays (d+2) (V - turnSeries (Stationary.issue X)):= by
    have hA := artery_funded he; let Y:=Stationary.issue X; have hH : Pointwise (turnSeries Y (m:=m)):= stain_ink _ hσ hA.1 hA.2
    have hW : Rays (d+1) (V - turnSeries Y):= hp.sub (turns_low _ hσ hA.1)
    refine (rays_jet (h.sub hH).analytic _).2 fun j hj=> ?_
    by_cases hm:j=d+1
    · subst j; rw [iteratedFDeriv_sub_apply h.analytic.contDiffAt hH.analytic.contDiffAt]; exact sub_eq_zero.mpr (aperture_eq (colors_align V h.analytic h.lights L X he hσ hx)).symm
    exact (rays_jet (h.sub hH).analytic _).mp hW j (by omega)
lemma currency (d:ℕ) [NeZero d] (hd : 2 ≤ d) (h:0<σ): ∃ η K:ℝ, 0<η ∧ η ≤ σ ∧ 0 ≤ K ∧ ∀ (F:Atlas G) (A:ℝ),
    0≤A → (∀ m, Pointwise (F m) ∧ Rays (d+1) (F m)) → Foil G F d σ A → ∃ X:Skin G d, Mar X (A*K) η ∧ ∀ m, Rays (d+2) (F m-turnSeries (Stationary.issue X)) := by
   obtain ⟨w,V,hw,H,hq,hV⟩:= strokes G d hd σ h; refine ⟨_,_,hw,H,hq,?_⟩
   rintro F A hA hp ⟨L,ht,hL⟩
   have hf:= withdrew (F:=fun i=> F (flights i)) fills (tendsto_const_nhds (x:=(0:ℝ))) ht (fun i=> by simpa only [mul_zero] using (hL _)) (fun i=>(hp _).1.analytic) (fun i=>(hp _).1.stained) (fun i=> (hp _).1.guard) (fun i j hj _=> (rays_jet (hp _).1.analytic _).mp (hp _).2 j hj)
   obtain ⟨X,hX⟩:= hV _ _ hA hf
   exact ⟨X, ⟨hX.price,hX.pigment⟩, fun m=> reaps (hp _).1 (hp _).2 (hL _) hX hw⟩
def Flute (X:Skin G 1) := ∀ a i,Rays 2 (readable (X a i) ∘ axes)
variable {G}
lemma near (hg:G.Simple) (ν:G.ColorIndex) (h:0<σ): ∃ η K:ℝ, 0<η ∧ η ≤ σ ∧ 0 ≤ K ∧ ∀ (F:Atlas G)(Q:Pot G 2)(A:ℝ),
    Glow Q σ A → Tunable Q → (∀ m, Pointwise (F m) ∧ Rays 2 (F m) ∧ Tensor.coeff (F m) 2 0=recital Q m) → probeK ν Q=0 → ∃ X:Skin G 1, Mar X (A*K) η ∧ Flute G X ∧ ∀ m, Rays 3 (F m-turnSeries (Stationary.issue X)) := by
   obtain ⟨w,V,hW,H,hV,hf⟩:= veins G σ h; refine ⟨_,_,hW,H,hV,?_⟩
   intro F Q A hv he hQ hp
   have he' (m:Side):= (hQ m).2.2
   let L:= gallery Q
   have ht := flags_two hg he _ fills (V:=fun i=> F (flights i)) (fun i=>(hQ _).1) (fun i=> he' _) hv h
   have hh : leapTip L (step (0:Axis)) 1 ![ν,ν]=0 := by
      unfold probeK alphaPay at hp; unfold L; rw [← ht.true_tip (ht.crop_edict (fun _ _ => trivial)) (step (0:Axis)) 1 ![ν,ν],show (leapTip ..).re=0 from (mul_eq_zero.mp hp).resolve_left (by norm_num),Complex.ofReal_zero]
   obtain ⟨X,hX,hF⟩:=hf A 2 L hv.nonneg ht.toFeatures (ht.vanish hg 1 0 (by decide) ν hh)
   exact ⟨_, ⟨hX.price,hX.pigment⟩,hF,fun m=> reaps (hQ m).1 (hQ m).2.1 (gallery_marks he (hQ m).2.2) hX hW⟩
end YM.RG08.Virtue
