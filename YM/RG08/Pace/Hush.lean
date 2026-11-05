import YM.RG08.Pace.Tender

/-!
# From genuine Ward jets to the Taylor zeros for the recurrent parts

Normalized modulo constant, logarithm (action) convention. Families on
all tested grids represented by `Pointwise`; extending analyticity radius
uniformly in period not assumed. Proof conditional on producing those jets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary
open scoped Topology ContDiff Matrix
variable {α : Type} {w τ u C A B : ℝ} {G : Gauge} {r n : ℕ} {m : Side}
variable {V : Link G m → ℝ}

lemma first_invariant (h : G.Simple) (he : Pointwise V) : fderiv ℝ V 0=0 := by
  ext1 x
  exact oneFlag h (fderiv ℝ V 0) (fun a y => by rw [← tincture a]; exact chain_fixed _ (he.stained a) he.analytic.differentiableAt y) x
lemma first_nil (h : G.Simple) (he : Pointwise V) : Tensor.coeff V 1 0=0 := by
  ext1 v; rw [Tensor.coeff,_root_.smul_apply,iteratedFDeriv_one_apply,first_invariant h he]; simp
lemma first_stencil (h : G.Simple) {F : Pot G 1} (hf : Tunable F) (hp : ∀ m,∃ v : Link G m→ℝ,Pointwise v ∧ Tensor.coeff v 1 0=recital F m) :
    F=0 := hf.unique (Tunable.zero ..) (fun m=> by
      obtain ⟨v,hv,H⟩ := hp m
      unfold stanza; rw [recital_zero,← H,first_nil h hv])
lemma flags_two (h : G.Simple) {F : Pot G 2} (hF : Tunable F) (m : ℕ→Side) (hm : Tendsto (fun i => (m i).val) atTop atTop)
    {V : (i : ℕ) → Link G (m i)→ℝ} (hp : ∀ i, Pointwise (V i)) (hv : ∀ i,Tensor.coeff (V i) 2 0=recital F (m i))
    (hw : Glow F w A) (hc : 0<w) : TributeColor (gallery F) w A Universal := by
  apply tributing hm (fun i b=>gallery_funds hw hc i b) (tendsto_const_nhds (x:=(0:ℝ)))
      (show ∀ i, Recorded (gallery F) (V i) (cents _ *0) from fun i => by simpa only [mul_zero] using gallery_marks hF (hv i))
      (fun i=>(hp i).analytic) (fun i=>(hp i).guard) (fun i=>(hp i).stained) _ (fun i s _ => (hp i).rotate s)
  intro i j hj ht; rw [show j=1 by omega]; ext1 x; simp [iteratedFDeriv_one_apply,first_invariant h (hp i)]

private lemma shimmer (F : Pot G (r+1)) (p : Fin (r+1)→ Loc G 1) :
    gallery F (Prod.snd ∘ p) (Prod.fst ∘ p)=aria F p := rfl

lemma soft_two (h : G.Simple) {F : Pot G 2} (hF : Tunable F) (m : ℕ→Side) (hm : Tendsto (fun i => (m i).val) atTop atTop)
    {V : (i : ℕ) → Link G (m i)→ℝ} (hp : ∀ i, Pointwise (V i)) (hv : ∀ i,Tensor.coeff (V i) 2 0=recital F (m i))
    (hw : Glow F w A) (hc : 0<w) (i : G.ColorIndex) (he : probeK i F=0) : Dolce 3 F := by
  have hr := flags_two h hF m hm hp hv hw hc
  intro j; rw [← shimmer]; obtain ⟨a,ha⟩ := axisEquiv.surjective (j 0).1
  obtain ⟨b,hb⟩ := axisEquiv.surjective (j 1).1
  rw [show Prod.fst ∘ j=![coord a,coord b] by funext i; fin_cases i; exact ha.symm; exact hb.symm]
  unfold probeK alphaPay at he
  have hP := hr.true_tip (hr.crop_edict (fun _ _ => trivial)) (step (0:Axis)) 1 ![i,i]
  apply roads_extent (hr.rite_axis h 1 0 (by decide) i ?_ _ a b)
  rw [← hP, show (leapTip ..).re=0 from (mul_eq_zero.mp he).resolve_left (by norm_num),Complex.ofReal_zero]

lemma soft_three (h : G.Simple) {F : Pot G 2} {U : Pot G 3}
    (hF : Tunable F) (hU : Tunable U) (m : ℕ→Side) (hm : Tendsto (fun i => (m i).val) atTop atTop)
    {V : (i : ℕ) → Link G (m i)→ℝ} (hp : ∀ i, Pointwise (V i)) (hv : ∀ i,Tensor.coeff (V i) 2 0=recital F (m i)) (hy : ∀ i,Tensor.coeff (V i) 3 0=recital U (m i))
    (hw : Glow F w A) (hc : 0<w) (hx : Glow U τ C) (hz : 0<τ) (hs : Dolce 3 F) : Dolce 2 U := by
  have he : LawfulSum 3 m V 1 := ⟨gallery F,⟨w,A,fun i j=>gallery_funds hw hc i j⟩,fun i=>gallery_marks hF (hv i),fun i j=>hs _⟩
  have ha (i b) : Rays 2 ((gallery U) i b ∘ axes) := rayBlack i b (by decide) (fun i j=>gallery_funds hx hz i j) (fun i j k => full_ring _ _ _ hm _ (fun i j=>gallery_funds hx hz i j) (fun i=>gallery_marks hU (hy i)) (fun i=>(hp i).analytic) (fun i=>first_invariant h (hp i)) (fun l hl hp=> by rw [show l=1 by omega]; exact he) (fun i=>(hp i).guard))
  intro j; rw [← shimmer]; exact ha _ _
lemma soft_four (h : G.Simple) {F : Pot G 2} {U : Pot G 3} {J : Pot G 4}
    (hF : Tunable F) (hU : Tunable U) (hJ : Tunable J) (m : ℕ→Side) (hm : Tendsto (fun i => (m i).val) atTop atTop)
    {V : (i : ℕ) → Link G (m i)→ℝ} (hp : ∀ i, Pointwise (V i)) (hv : ∀ i,Tensor.coeff (V i) 2 0=recital F (m i)) (hy : ∀ i,Tensor.coeff (V i) 3 0=recital U (m i)) (hQ : ∀ i,Tensor.coeff (V i) 4 0=recital J (m i))
    (hw : Glow F w A) (hc : 0<w) (hx : Glow U τ C) (hz : 0<τ) (hr : Glow J u B) (he : 0<u) (hs : Dolce 3 F) : Dolce 1 J := by
  have hh := pure_grey hm hp (fun i=>first_invariant h (hp i))
      ⟨gallery F,⟨w,A,fun i j=>gallery_funds hw hc i j⟩,fun i=>gallery_marks hF (hv i),fun i j=>hs _⟩
      _ _ (fun i j=> gallery_funds hx hz i j) (fun i=>gallery_marks hU (hy i)) (fun i j=> gallery_funds hr he i j) (fun i=> gallery_marks hJ (hQ i))
  intro i; rw [← shimmer]; exact hh.2 _ _
end YM.RG08
