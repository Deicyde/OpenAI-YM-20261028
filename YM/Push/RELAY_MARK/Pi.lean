import YM.Push.RELAY_MARK.Spelling
import YM.Shift.Exchange
import YM.Work.B16
import YM.Work.G05.Taylor

/-!
# Taylor leading accounting for transported gradients

Charge G-invariance later (work on raw polynomials including
color legs here). Actual radial Hol tests through every order `d`;
`peg` and all `G##` statements used here are proven at B70. The
linear symbol analysis is for keeping independence at this projection,
not renaming columns after an ordered limit. .
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Analysis Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {H : Hol G} {j d : ℕ}

structure Forms (H : Hol G) (d : ℕ) (F : Pre G) (p : Pol G) : Prop where
  bound : p∈limited G d
  nice (J : Jet G) : ContDiffAt ℝ (d:WithTop ℕ∞) (fun t=>F (H.links d J t)) 0
  through (J : Jet G) k (h : k ≤ d) :
    iteratedDeriv k (fun t=> F (H.links d J t)) 0 = iteratedDeriv k (fun t=>read (scaleJet J t) p) 0

namespace Forms
variable {p q : Pol G} {f g : Pre G}
lemma sole (hf : Forms H d f p) (hg : Forms H d f q) : p=q := by
  have he (k : ℕ) (h : k ≤ d) : tier k p = tier k q := eval_ext _ _ (fun A => by
    have hx := (hf.through A k h).symm.trans (hg.through A k h)
    rw [deriv_read,deriv_read] at hx; exact smul_right_injective ℂ (show (k.factorial:ℝ)≠0 by positivity) hx)
  rw [← limited_cap d p hf.bound, ← limited_cap d q hg.bound,capRead,capRead]
  exact Finset.sum_congr rfl fun i hi => he i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

lemma seats (v : Label G d) (f : Pre G) : Forms H d f v.val ↔ Projects H v f := by
  refine ⟨fun h J => ⟨h.nice J,?_,h.through J⟩,fun h => ⟨v.property.1,fun J=>(h J).1,fun J=>(h J).2.2⟩⟩
  exact (read_smooth J _ _).contDiffAt

lemma zero (H : Hol G) (d : ℕ) : Forms H d 0 0 :=
    ⟨Submodule.zero_mem _, fun _ => contDiffAt_const,fun _ k _ => by simp⟩
lemma one (H : Hol G) (d : ℕ) : Forms H d 1 1 :=
    ⟨(unit G d).property.1,fun _ => contDiffAt_const,fun _ k _ => by simp⟩

lemma nice_at (hf : Forms H d f p) (J : Jet G) (k : ℕ) (h : k≤d) :
    ContDiffAt ℝ (k:WithTop ℕ∞) (fun t=>f (H.links d J t)) 0 := (hf.nice J).of_le (Nat.cast_le.mpr h)

lemma add (hf : Forms H d f p) (hg : Forms H d g q) : Forms H d (f+g) (p+q) := by
  refine ⟨Submodule.add_mem _ hf.bound hg.bound,fun A => (hf.nice A).add (hg.nice A),fun A k h => ?_⟩
  simp only [Pi.add_apply,map_add]; rw [iteratedDeriv_fun_add (hf.nice_at _ _ h) (hg.nice_at _ _ h),
    iteratedDeriv_fun_add (read_smooth A p _).contDiffAt (read_smooth A q _).contDiffAt,hf.through _ _ h,hg.through _ _ h]

lemma scale (hf : Forms H d f p) (c : ℂ) : Forms H d (c • f) (c • p) := by
  refine ⟨Submodule.smul_mem _ _ hf.bound,fun A => (hf.nice A).const_smul c,fun A k h => ?_⟩
  simp only [Pi.smul_apply,map_smul]; rw [iteratedDeriv_fun_const_smul_field,iteratedDeriv_fun_const_smul_field,hf.through _ _ h]

lemma neg (hf : Forms H d f p) : Forms H d (-f) (-p) := by simpa using hf.scale (-1)
lemma sub (hf : Forms H d f p) (hg : Forms H d g q) : Forms H d (f-g) (p-q) := by simpa [sub_eq_add_neg] using hf.add hg.neg

lemma product (hf : Forms H d f p) (hg : Forms H d g q) : Forms H d (f*g) (capRead d (p*q)) := by
  refine ⟨cap_limited d _,fun A => (hf.nice A).mul (hg.nice A), fun J k hk => ?_⟩
  rw [deriv_read J, tier_capRead _ _ k hk, ← deriv_read J]; simp only [map_mul, Pi.mul_apply]
  rw [iteratedDeriv_fun_mul (hf.nice_at J k hk) (hg.nice_at J k hk),
    iteratedDeriv_fun_mul (read_smooth J p _).contDiffAt (read_smooth J q _).contDiffAt];
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hf.through J i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hk),hg.through J _ ((Nat.sub_le k i).trans hk)]

lemma sum {X : Type*} (s : Finset X) (f : X→Pre G) (p : X→Pol G)
    (h : ∀ i∈s, Forms H d (f i) (p i)) : Forms H d (∑ i∈s,f i) (∑ i∈s,p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact zero ..
  | insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (h _ (Finset.mem_insert_self ..)).add (ih (fun i ht => h i (Finset.mem_insert_of_mem ht)))
end Forms

section Slot

def slotted (G : Gauge) (s : Slot) (i : G.ColorIndex) : Pre G := fun U => ((s.eval U i : ℝ):ℂ)

private lemma diag_slots (m : ℕ) {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (F : Jet G → X)
    (v : (X →ₗ[ℝ] ℝ) → Pol G) (hV : ∀ q, v q ∈ floorSlots 1) (hW : ∀ q J, read J (v q) = (q (F J):ℂ)) (C : Tensor.T X ℂ m) :
    ∃ p ∈ floorSlots (G:=G) m,∀ J : Jet G,Tensor.diagonal C (F J)=read J p := by
  classical
  induction m with
  | zero =>
    refine ⟨MvPolynomial.C (Tensor.diagonal C 0),?_, fun J=>?_⟩
    · exact slot_sector (0,0) (MvPolynomial.isWeightedHomogeneous_C bidegree _)
    simp only [Labels.read,MvPolynomial.aeval_C,Algebra.algebraMap_self,RingHom.id_apply]
    exact congr_arg C (Subsingleton.elim ..)
  | succ m ih =>
    let B := Module.finBasis ℝ X
    choose p hp he using fun i => ih (C.curryLeft (B i))
    let g i := v (B.coord i)
    refine ⟨∑ i,p i*g i, Submodule.sum_mem _ fun i _=> slots_mul (hp _) (hV _),fun J=>?_⟩
    let x := F J
    have hf : Tensor.diagonal C x = Tensor.diagonal (C.curryLeft x) x := by
      apply congr_arg C; ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have ht : C.curryLeft x= ∑ i, B.repr x i • C.curryLeft (B i) := by
      nth_rw 1 [← B.sum_repr x]; rw [map_sum]; simp only [map_smul]
    rw [hf,ht,Tensor.diagonal, sum_apply, map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_apply,Complex.real_smul,map_mul, show read J (g i)=_ from hW ..,← he i J]; exact mul_comm _ _

private lemma f_smooth (J : Jet G) (K L : ℕ) :
    ContDiffAt ℝ (L:WithTop ℕ∞) (fun t => trunk K (scaleJet J t)) 0 := by
  have H {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (y : Y) (k : ℕ) :
      ContDiffAt ℝ (L:WithTop ℕ∞) (fun t : ℝ => t^k • y) 0 := (contDiffAt_id.pow _).smul contDiffAt_const
  exact contDiffAt_pi.mpr fun i => H _ (i.val+2)

private theorem compose_trim (H : Hol G) (d L : ℕ) (he : d ≤ L) (f : Pre G) (W : Snap G d → ℂ)
    (ht : ContDiffAt ℝ (L:WithTop ℕ∞) W 0) (y : Pol G)
    (hu : ∀ J : Jet G, Work.G05.blockTaylor L W (trunk d J) = read J y)
    (hv : ∀ (J : Jet G) (t : ℝ), f (H.links d J t)=W (trunk d (scaleJet J t))) :
    Forms H d f (capRead d y) := by
  refine ⟨cap_limited ..,fun J=>?_,fun J k hk=>?_⟩
  · simp_rw [hv]
    have hh : trunk d (scaleJet J 0)=0 := by funext i; simp [trunk,scaleJet]
    exact ((show ContDiffAt ℝ (L:WithTop ℕ∞) W (trunk d (scaleJet J 0)) from hh.symm ▸ ht).comp 0
      (f_smooth J d L)).of_le (Nat.cast_le.mpr he)
  let q (t : ℝ) := trunk d (scaleJet J t)
  have hh : q 0=0 := by funext b; simp [q,trunk,scaleJet]
  have Hf := f_smooth J d L
  simp_rw [hv J]; rw [deriv_read J,tier_capRead d y k hk,← deriv_read J,← funext (fun t : ℝ => hu (scaleJet J t))]
  change iteratedDeriv k (W ∘ q) 0 = iteratedDeriv k (Work.G05.blockTaylor L W ∘ q) 0
  unfold iteratedDeriv
  have hl : ∀ m ≤ L, iteratedFDeriv ℝ m W (q 0) = iteratedFDeriv ℝ m (Work.G05.blockTaylor L W) (q 0) := by
    rw [hh]; exact fun m h => (Work.G05.blockTaylor_jets ht m h).symm
  exact congr_arg (fun A : Tensor.T ℝ ℂ k => A (fun _ => 1)) (Work.G05.jets_comp (f:=q) Hf Hf
    (hh.symm ▸ ht) (Work.G05.blockTaylor_contDiff L W _).contDiffAt rfl (fun _ _ => rfl) hl k (hk.trans he))

/- Builds the readout of any raw slot, retaining its one-factor part
at d. Work with Taylor order d+1 even for d=0; trim engineering at end. -/
lemma slot_readout (H : Hol G) (s : Slot) (d : ℕ) (i : G.ColorIndex) (h : Peg H d) :
    ∃ p, Forms H d (slotted G s i) p ∧ p-spell d (safeLinear H d s i)∈floorSlots 2 := by
  classical
  let q := safeLinear H d s i
  let W := ((Complex.ofRealCLM).comp (EuclideanSpace.proj i)) ∘ takes H d s
  let L : ℕ := d+1
  have ht : ContDiffAt ℝ (L:WithTop ℕ∞) W 0 := by
    refine ContDiffAt.comp _ ?_ ((h.shot s).contDiffAt.of_le le_top)
    exact ((Complex.ofRealCLM).comp (EuclideanSpace.proj i)).contDiff.contDiffAt
  have he := lt_add_one d
  let hs := (Finset.range (L+1)).filter (fun i : ℕ => 2 ≤ i)
  have hi : Finset.range (L+1)=insert 0 (insert 1 hs) := by ext x; simp [hs]; omega
  choose P hp hP using fun k : ℕ => diag_slots k (trunk d (G:=G)) (spell d) (fun q => spell_slot q) (fun q => spell_reads q) (Tensor.coeff W k 0)
  let y := spell d q + ∑ i∈hs,P i
  have h0 : W 0=0 := by simp [W,takes_zero]
  have hd (J : Jet G) : Tensor.diagonal (Tensor.coeff W 1 0) (trunk d J) = read J (spell d q) := by
    rw [spell_reads, Tensor.diagonal,Tensor.coeff]
    let F := Complex.ofRealCLM.comp (EuclideanSpace.proj i)
    simp only [W,Nat.factorial_one,Nat.cast_one,inv_one,one_smul, iteratedFDeriv_one_apply]
    rw [fderiv_comp _ F.differentiableAt (h.shot s).differentiableAt,F.fderiv]; rfl
  have hu (J : Jet G) : Work.G05.blockTaylor L W (trunk d J) = read J y := by
    rw [Work.G05.blockTaylor, hi,Finset.sum_apply, Finset.sum_insert,Finset.sum_insert,
      Tensor.diagonal,Tensor.coeff_apply_zero,h0,zero_add,hd]
    · unfold y; rw [map_add,map_sum]; exact congr_arg _ (Finset.sum_congr rfl fun i _=> hP i J)
    all_goals simp [hs]
  let p := capRead d y
  refine ⟨p,compose_trim H d L he.le _ W ht y hu ?_,?_⟩
  · intro J t
    rw [Drops.scales H J t]; rfl
  · change capRead d y - spell d q∈floorSlots 2
    rw [← limited_cap d _ (spell_limited q),← cap_sub]
    unfold y; rw [add_sub_cancel_left]
    exact cap_preserves d (Submodule.sum_mem (floorSlots 2) fun i hi =>
      rise_anti (by
        apply Prod.Lex.le_iff'.mpr
        have hx : 2 ≤ i := (Finset.mem_filter.mp hi).2
        exact ⟨hx,fun _=>le_rfl⟩) (hp _))
end Slot

section Force

def flashed (b : Point) (i : G.ColorIndex) : Pre G := fun U => ((force U b.w b.e i:ℝ):ℂ)

lemma fsum (b : Point) (i : G.ColorIndex) :
    flashed b i = ∑ p : PlaqAxes, hereTerm (fun s => slotted G s i) b.w b.e.2 p := by
  funext U
  unfold flashed
  let a := b.e.2
  let F : G.Color →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj i)
  change F (force U b.w b.e)=_
  rw [Finset.sum_apply,show b.e=(stop 0 b.w,a) by rw [b.lands], force_stems,map_sum]
  refine Finset.sum_congr rfl fun p _=>?_
  change F (hereTerm _ b.w a p)=(hereTerm (V:=Pre G) (fun s => slotted G s i) _ a p) _
  unfold hereTerm; split
  next h=> rw [map_sub]; rfl
  next h=> split <;> simp only [map_sub,map_neg,map_zero] <;> rfl

private lemma preferred (H : Hol G) (w : Point) (i : G.ColorIndex) (d : ℕ) :
    hereTerm (fun s => safeLinear H d s i) w.w w.e.2 = fun p =>
    ((EuclideanSpace.proj i) ∘L hereTerm (Blurb H d) w.w w.e.2 p).toLinearMap := by
  funext p; unfold hereTerm
  split
  next h => exact LinearMap.ext fun A=> by simp [safeLinear]
  next h =>
    split
    next h => exact LinearMap.ext fun A=> by simp [safeLinear]
    next h => exact LinearMap.ext fun A=> by simp

lemma psum (H : Hol G) (d : ℕ) (w : Point) (i : G.ColorIndex) :
    spell d (positiveLinear H d w i)=∑ p : PlaqAxes, hereTerm (fun s=> spell d (safeLinear H d s i)) w.w w.e.2 p := by
  have he : positiveLinear H d w i=∑ p : PlaqAxes, hereTerm (fun s => safeLinear H d s i) w.w w.e.2 p := by
    rw [preferred]; apply LinearMap.ext; intro A
    simp [positiveLinear,linearForce]
  change spellMap G d _ = _; rw [he,map_sum]; refine Finset.sum_congr rfl fun p _=>?_
  unfold hereTerm; split
  next h => rw [map_sub]; rfl
  next h => split <;> simp only [map_zero,map_neg,map_sub]; rfl

lemma force_reads (H : Hol G) (h : Peg H d) (w : Point) (i : G.ColorIndex) :
    ∃ p, Forms H d (flashed w i) p ∧ p-spell d (positiveLinear H d w i)∈floorSlots 2 := by
  choose p hp he using fun s : Slot => slot_readout H s d i h
  rw [fsum,psum]
  refine ⟨∑ q : PlaqAxes, hereTerm p w.w w.e.2 q, Forms.sum _ _ _ (fun b hb=>?_),?_⟩
  · unfold hereTerm; split
    next h => exact (hp _).sub (hp _)
    next h =>
      split
      next h => exact ((hp _).sub (hp _)).neg
      next h => exact Forms.zero ..
  rw [← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun q _=>?_
  unfold hereTerm; split
  next h=> rw [sub_sub_sub_comm]; exact Submodule.sub_mem (floorSlots 2) (he _) (he _)
  next h=>
    split
    next h=>
      rw [← neg_sub',sub_sub_sub_comm]; exact Submodule.neg_mem _ (Submodule.sub_mem _ (he _) (he _))
    next h=> simp
end Force
end YM.Push.Mark
