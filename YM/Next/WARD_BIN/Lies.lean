import YM.Next.WARD_BIN.Stencils


/-!
# Ordered left-link derivative tools, for `Regular` at health boundaries

To justify subtraction and literal offsets/rotations/star on the same budgets.
Represent as derivative of a curve of ordered increments: later when negatives
are reversed have to permute the mixed partials for this same curve. Never use
symmetry of the ordered Lie derivatives themselves. `ContDiffAt` in germ chart
suffices; don't infer that every nearby configuration is healthy!
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Lies
open Lattice Wilson RG Function Filter Topology Set Work.G07
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side}
variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {U : Config G n} {f g : Config G n → E} {l m : ℕ}

abbrev Slab (G : Gauge) (n : Side) (k : ℕ) := Fin k → Directions G n

def chug (k : ℕ) : Config G n → Slab G n k → Config G n :=
  match k with
  | 0 => fun U _ => U
  | k+1 => fun U A => chug k (increment U (A 0)) (Fin.tail A)
lemma chug_zero (U : Config G n) (k : ℕ) : chug k U 0=U := by
  induction k with
  | zero => rfl
  | succ k ih => change chug k (increment U 0) 0 = _; rw [at_zero_increment, ih]

def Germ (l : ℕ) (f : Config G n → E) (U : Config G n) : Prop :=
  ContDiffAt ℝ l (fun y => f (increment U y)) 0

lemma Germ.prod {j : ℕ} (h : Germ l f U) (hp : j ≤ l) : Germ j f U :=
  ContDiffAt.of_le h (Nat.cast_le.mpr hp)

/-- Use coefficientwise matrix smoothness; not leaving the chart. -/
lemma Germ.curves (h : Germ l f U) {x : F} {Z : F → Config G n} (hx : Z x=U)
    (hz : ∀ i,ContDiffAt ℝ l (fun y => G.mat (Z y i)) x) : ContDiffAt ℝ l (fun y => f (Z y)) x := by
  let A (y : F) (i : Edge (Site n)) := G.plog (G.mat (Z y i * (U i)⁻¹))
  have ht : ∀ i,ContinuousAt (fun y => Z y i) x := fun i =>
    (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.isInducing.continuousAt_iff.mpr (hz i).continuousAt
  obtain ⟨(hs : A x=0),hb,hh⟩ := exp_local U Z x hx ht
  have ha : ContDiffAt ℝ l A x := by
    apply contDiffAt_pi.mpr; intro i
    let u (y : F) := G.mat (Z y i * (U i)⁻¹)
    have hm : ContDiffAt ℝ l u x := by unfold u; simp_rw [G.mat_mul]; exact (hz i).mul contDiffAt_const
    exact (show ContDiffAt ℝ l G.plog (u x) from (show u x=1 by simp [u,hx]).symm ▸
      G.plog_diff.of_le le_top).comp x hm
  apply ((show ContDiffAt ℝ l (fun y => f (increment U y)) (A x) from hs.symm ▸ h).comp x ha).congr_of_eventuallyEq
  exact hh.mono fun i hi => congrArg f hi.symm

lemma grins {U : F → Config G n} {x : F} (hs : ∀ i,ContDiffAt ℝ l (fun y => G.mat (U y i)) x)
    {A : F → Directions G n} (hA : ContDiffAt ℝ l A x) (i) :
    ContDiffAt ℝ l (fun y => G.mat ((increment (U y) (A y)) i)) x := by
  unfold increment; simp_rw [G.mat_mul]
  exact (((G.exp_jet.of_le le_top).contDiffAt).comp x (contDiffAt_pi.mp hA i)).mul (hs i)

lemma chug_diff (h : Germ l f U) (k : ℕ) : ContDiffAt ℝ l (f ∘ chug k U) 0 := by
  have hv : ∀ j : ℕ, ∀ {A : Slab G n k → Config G n} {X : Slab G n k → Slab G n j},
      (∀ i,ContDiffAt ℝ l (fun y => G.mat (A y i)) (0 : Slab G n k)) →
        (ContDiffAt ℝ l X (0 : Slab G n k)) → ∀ i, ContDiffAt ℝ l (fun y => G.mat (chug j (A y) (X y) i)) 0 := by
    intro j
    induction j with
    | zero => exact fun h _ => h
    | succ k ih =>
      intro A X ha hx i; apply ih (grins ha (contDiffAt_pi.mp hx 0)) _ i
      exact contDiffAt_pi.mpr fun j => contDiffAt_pi.mp hx j.succ
  exact h.curves (chug_zero _ _) (hv k (fun _ => contDiffAt_const) contDiffAt_id)

lemma liner {d : F→E} [NormedAddCommGroup X] [NormedSpace ℝ X] {a : X} (V : X →L[ℝ] F)
    (hh : ContDiffAt ℝ l d (V a)) : iteratedFDeriv ℝ l (d ∘ V) a =
      (iteratedFDeriv ℝ l d (V a)).compContinuousLinearMap fun _ => V := by
  let t := interior {x | ContDiffAt ℝ l d x}
  have ht : ContDiffOn ℝ l d t := fun _ hx => ContDiffAt.contDiffWithinAt (interior_subset hx)
  have hi : V a ∈ t := mem_interior_iff_mem_nhds.mpr (hh.eventually (by simp))
  have hu := isOpen_interior (s:={x | ContDiffAt ℝ l d x})
  have hb := hu.uniqueDiffOn (𝕜:=ℝ)
  have hx := (hu.preimage V.continuous).uniqueDiffOn (𝕜:=ℝ)
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hb hh hi,
    ← iteratedFDerivWithin_eq_iteratedFDeriv hx (hh.comp _ V.contDiff.contDiffAt) (show a∈ V⁻¹' t from hi)]
  exact V.iteratedFDerivWithin_comp_right ht hb hx hi le_rfl

def mixed (f : Config G n → E) (k : ℕ) (U : Config G n) : Tensor.T (Directions G n) E k :=
  (iteratedFDeriv ℝ k (f ∘ chug k U) 0).compContinuousLinearMap
    (fun i => ContinuousLinearMap.single ℝ (fun _ => Directions G n) i)

lemma mixed_eval (U : Config G n) (f : Config G n → E) (A : Slab G n l) :
    mixed f l U A= iteratedFDeriv ℝ l (f ∘ chug l U) 0 (fun i => Pi.single i (A i)) := rfl

/- One-parameter derivative of the mixed tensor tail. Even l=0 use
Cons at next order on the *same chug*. -/
lemma successor {A : Slab G n (l+1)} (hh : ContDiffAt ℝ (↑(l+1:ℕ)) (f ∘ chug (l+1) U) 0)
    (ih : ∀ U : Config G n, ContDiffAt ℝ l (f ∘ chug l U) 0 →
      leftDerivs f (List.ofFn (Fin.tail A)) U=mixed f l U (Fin.tail A)) :
    HasDerivAt (fun t : ℝ => leftDerivs f (List.ofFn (Fin.tail A)) (increment U (t • A 0)))
      (mixed f (l+1) U A) 0 := by
  classical
  let a := A 0
  let B := Fin.tail A
  let V : Slab G n l →L[ℝ] Slab G n (l+1) := ContinuousLinearMap.pi
    (Fin.cons (0 : Slab G n l →L[ℝ] Directions G n) (fun j : Fin l => ContinuousLinearMap.proj j))
  have hv (Z : Slab G n l) : V Z=Fin.cons 0 Z := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp [V]
    simp [V]
  let u := (Pi.single (0:Fin (l+1)) a : Slab G n (l+1))
  let T (t : ℝ) := t • u
  have ht (t : ℝ) : T t=Fin.cons (t • a) 0 := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [T,u]
  have hz : T 0=0 := zero_smul ..
  have hu (t : ℝ) (W : Slab G n l) : T t + V W=Fin.cons (t • a) W := by
    rw [ht,hv]; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  let g := f ∘ chug (l+1) U
  let v : Fin l → Slab G n l := fun i => Pi.single i (B i)
  have hg (t) : f ∘ chug l (increment U (t • a)) = (fun z => g (T t + z)) ∘ V := by
    funext i; dsimp only [Function.comp_apply]; rw [hu]
    dsimp only [g,Function.comp_apply]; simp only [chug,Fin.cons_zero, Fin.tail_cons]
  let v' := fun i => V (v i)
  have he : (fun i => (Pi.single i (A i): Slab G n (l+1))) = Fin.cons u v' := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]; rfl
    simp only [v',hv,Fin.cons_succ]; funext i; refine Fin.cases ?_ (fun l => ?_) i
    · simp
    simp [Pi.single_apply,v,B,Fin.tail]
  have hf : HasDerivAt T u 0 := by
    simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const u
  rw [mixed_eval,he, YM.Analysis.cons_jet hh]
  let G' := fun z => iteratedFDeriv ℝ l g z v'
  have hH : DifferentiableAt ℝ G' 0 :=
    (ContinuousMultilinearMap.apply ℝ _ E v').differentiableAt.comp 0 (hh.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr l.lt_succ_self))
  have HH : HasDerivAt (G' ∘ T) (fderiv ℝ G' 0 u) 0 := by
    have hw := (show DifferentiableAt ℝ G' (T 0) from hz.symm ▸ hH).hasFDerivAt.comp_hasDerivAt 0 hf
    rwa [hz] at hw
  refine HH.congr_of_eventuallyEq ?_
  have hb : ∀ᶠ t in 𝓝 (0:ℝ), ContDiffAt ℝ l g (T t) :=
    (hf.continuousAt.tendsto).eventually ((show ContDiffAt ℝ l g (T 0) from hz.symm ▸ hh.of_le (Nat.cast_le.mpr l.le_succ)).eventually (by simp))
  filter_upwards [hb] with t hG
  let d := fun w => g (T t + w)
  have hw : ContDiffAt ℝ l d (V 0) := by
    rw [map_zero]
    exact (show ContDiffAt ℝ l g ((fun w => T t + w) 0) from by simpa using hG).comp _ (show ContDiffAt ℝ l (fun w => T t + w) 0 from contDiffAt_const.add contDiffAt_id)
  have hE := hg t
  change leftDerivs _ _ (increment U (t • a)) = G' (T t)
  rw [ih _ (by rw [hg t]; exact hw.comp _ V.contDiff.contDiffAt), mixed_eval,hg,liner V hw]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,map_zero,d,
    iteratedFDeriv_comp_add_left, add_zero]; rfl

lemma expand_part (A : Slab G n l) (h : ContDiffAt ℝ l (f ∘ chug l U) 0) :
    leftDerivs f (List.ofFn A) U=mixed f l U A := by
  induction l generalizing U with
  | zero => rw [mixed_eval,iteratedFDeriv_zero_apply,List.ofFn_zero]; rfl
  | succ l ih =>
    rw [List.ofFn_succ,leftDerivs]; exact (successor h (fun _ hu => ih _ hu)).deriv

lemma Germ.takes (hh : Germ m f U) (A : Slab G n l) (h : l≤m) : leftDerivs f (List.ofFn A) U=mixed f l U A :=
  expand_part A (chug_diff (hh.prod h) l)

lemma Germ.has (hf : Germ m f U) (l : List (Directions G n)) (A : Directions G n) (hx : l.length < m) :
    HasDerivAt (fun t : ℝ => leftDerivs f l (increment U (t • A))) (leftDerivs f (A::l) U) 0 := by
  have hz : A::l=List.ofFn (Fin.cons A l.get) := by rw [List.ofFn_cons,List.ofFn_get]
  have hp := successor (chug_diff (hf.prod hx) (l.length+1)) (A:=Fin.cons A l.get) (fun U => expand_part _)
  simp only [← hf.takes _ hx,Fin.tail_cons,Fin.cons_zero,List.ofFn_cons,List.ofFn_get] at hp
  exact hp
lemma Germ.sub (h : Germ l f U) (he : Germ l g U) : Germ l (f - g) U := ContDiffAt.sub h he
lemma Germ.takes_sub (h : Germ m f U) (he : Germ m g U) (x : List (Directions G n)) (hp : x.length ≤ m) :
    leftDerivs (f-g) x U=leftDerivs f x U-leftDerivs g x U := by
  have hf (Z : Slab G n x.length) : leftDerivs (f-g) (List.ofFn Z) U=leftDerivs f (List.ofFn Z) U-leftDerivs g (List.ofFn Z) U := by
    rw [(h.sub he).takes _ hp,h.takes _ hp,he.takes _ hp]; simp only [mixed_eval]
    rw [show (f-g) ∘ chug x.length U=f ∘ chug x.length U - g ∘ chug x.length U from rfl,
      iteratedFDeriv_sub_apply (chug_diff (h.prod hp) _) (chug_diff (he.prod hp) _)]; rfl
  simpa [List.ofFn_get] using! hf x.get

/- Ready for rotation bookkeeping. Reorder parameters on this **whole**
ordered path when changing gauges/frames. -/
abbrev Panels (l : ℕ) := Fin l → ℝ
def journey (U : Config G n) (l : ℕ) (A : Slab G n l) (t : Panels l) := chug l U (fun i => t i • A i)
def photon (l : ℕ) (A : Slab G n l) : Panels l →L[ℝ] Slab G n l :=
  ContinuousLinearMap.pi fun i => (ContinuousLinearMap.proj i).smulRight (A i)
abbrev cart (i : Fin l) : Panels l := Pi.single i 1
lemma parallel (A : Slab G n l) (i : Fin l) : photon l A (cart i) = Pi.single i (A i) := by
  funext j; change (cart i j) • A j= _; by_cases H : j=i
  · simp [H]
  simp [cart,H]
lemma journey_photon (U : Config G n) (A : Slab G n l) : journey U l A= chug l U ∘ photon l A := rfl
lemma Germ.journeys (A : Slab G n l) (hh : Germ l f U) : ContDiffAt ℝ l (f ∘ journey U l A) 0 :=
  (show ContDiffAt ℝ l (f ∘ chug l U) (photon l A 0) from by rw [map_zero]; exact chug_diff hh _).comp _
    (photon l A).contDiff.contDiffAt
lemma Germ.ordered (A : Slab G n l) (hh : Germ l f U) :
    leftDerivs f (List.ofFn A) U=iteratedFDeriv ℝ l (f ∘ journey U l A) 0 cart := by
  rw [hh.takes A le_rfl, mixed_eval]
  rw [journey_photon,← Function.comp_assoc, liner (photon l A) (by rw [map_zero]; exact chug_diff hh _)]
  simp_rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero, parallel]
lemma left_sub {P : Support n} {b : BudgetPoint} {U : Config G n} [MeasurableSpace E]
    (hf : b.Regular P f) (hg : b.Regular P g) {l} (he : List.length l≤b.order) (hp : Healthy b.threshold P U) :
    leftDerivs (f-g) l U=leftDerivs f l U - leftDerivs g l U :=
  (show Germ b.order f U from hf.smooth U hp).takes_sub (hg.smooth U hp) l he

lemma regsub {P : Support n} {b : BudgetPoint} {f g : Config G n → ℂ} (hf : b.Regular P f) (hg : b.Regular P g) :
    b.Regular P (f-g) := by
  have hh (U : Config G n) (ht : Healthy b.threshold P U) : Germ b.order (f-g) U :=
    (show Germ b.order f U from hf.smooth U ht).sub (hg.smooth U ht)
  exact ⟨fun U V he => congr_arg₂ (·-·) (hf.sites U V he) (hg.sites U V he),hf.borel.sub hg.borel,
    fun k U => congr_arg₂ (·-·) (hf.symmetry k U) (hg.symmetry k U), hh, fun U he A l hl => (hh U he).has l A hl⟩
lemma pays_sub {P : Support n} {b : BudgetPoint} {f g : Config G n → ℂ} (hf : b.Regular P f) (hg : b.Regular P g)
    {c c' o} (he : b.supBounds o P f c) (hh : b.supBounds o P g c') : b.supBounds o P (f-g) (c+c') :=
  ⟨add_nonneg he.1 hh.1,fun U hp l hl hm => (congr_arg (‖·‖) (left_sub hf hg hl hp)).trans_le ((norm_sub_le ..).trans
    (add_le_add (he.2 U hp l hl hm) (hh.2 U hp l hl hm)))⟩
end YM.WardBin.Lies
