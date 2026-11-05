import YM.Planned.ATOM_REGULAR_ESTIMATE.EdgeTaylor

/-! Substitute actual log directions from polynomial gauges and radial
Snap calls. Even **nonlinear** jets of this substitution are filtered on a
nonwrapping support: at least one degree is always removed. (Infinitesimal
surjectivity back onto polynomial-direction fields shown later.) -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Flat
open Function Tensor Lattice Wilson RG Source Labels Source.Drops Gauge Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {d k m : ℕ}

/-- Log gauges of polynomial site dependence (constant gauge not needed). -/
abbrev MaskLog (G : Gauge) (d : ℕ) := (i : Fin d) → T E4 G.Color (i.val+1)
/-- Chosen *finite* perturbation data for testing polynomial directions -/
abbrev Perturb (G : Gauge) (d : ℕ) := Snap G d × MaskLog G d

abbrev Tuple (G : Gauge) (d : ℕ) := G.Color × G.Color × Rad G d

def enter (w : MaskLog G d) (x : E4) := ∑ i, diagonal (w i) x
@[simp] lemma enter_zero (x : E4) : enter (0 : MaskLog G d) x = 0 := by simp [enter,Tensor.diagonal]

structure Phase (k : ℕ) (w : Perturb G d) : Prop where
  low : Lower k w.1
  mask (i : Fin d) : k < i.val + 1 → w.2 i = 0

namespace Phase
variable {w v : Perturb G d}
protected lemma mono (h : Phase k w) (hk : k ≤ m) : Phase m w :=
  ⟨fun i hi => h.low i (lt_of_le_of_lt hk hi),fun i hi => h.mask i (lt_of_le_of_lt hk hi)⟩

lemma room (h : Phase k w) : Degree k (enter w.2) := by
  rw [show enter w.2 = ∑ i,diagonal (w.2 i) from funext fun i => by rw [enter,Finset.sum_apply]]
  apply Degree.sum _; intro i hi
  by_cases hx : i.val+1 ≤ k
  · exact Degree.diag hx _
  rw [h.mask i (Nat.lt_of_not_ge hx)]; exact Degree.const 0 _
protected lemma add (hv : Phase k v) (hw : Phase k w) : Phase k (v+w) := by
  constructor
  · intro i hi; change v.1 i+w.1 i=0; rw [hv.low i hi,hw.low i hi,zero_add]
  intro i hi; change v.2 i+w.2 i = 0; rw [hv.mask i hi,hw.mask i hi,zero_add]

end Phase

def changeIn (x : E4) (i : Axis) : Perturb G d →L[ℝ] Tuple G d := LinearMap.toContinuousLinearMap {
  toFun w := (enter w.2 x,enter w.2 (x+basis i)-enter w.2 x, record x i w.1)
  map_add' a b := by
    simp [enter,Tensor.diagonal,Finset.sum_add_distrib]; abel
  map_smul' a w := by simp [enter,Tensor.diagonal,Finset.smul_sum,smul_sub] }

def plant (k : Tuple G d) : G.Color := G.plog (G.mat ((G.lieExp k.1) * endVal k.2.2 * (G.lieExp (k.1+k.2.1))⁻¹))

lemma plant_analytic (d : ℕ) : ContDiffAt ℝ ω (plant : Tuple G d → G.Color) 0 := by
  let L (k : Tuple G d) := G.mat ((G.lieExp k.1) * endVal k.2.2 * (G.lieExp (k.1+k.2.1))⁻¹)
  have he : L 0=1 := by simp [L,(end_diff G d).2]
  have hg : ContDiffAt ℝ ω (fun k => G.mat (endVal (Prod.snd (Prod.snd k)))) (0 : Tuple G d) :=
    (end_diff G d).1.contDiffAt.comp (f:=fun k : Tuple G d => k.2.2) (0:Tuple G d) (contDiff_snd.comp contDiff_snd).contDiffAt
  apply (show ContDiffAt ℝ ω G.plog (L 0) by rw [he]; exact G.plog_diff).comp _ (f:=L)
  unfold L; simp_rw [G.mat_mul,G.mat_inv]
  exact ((G.exp_jet.contDiffAt.comp (f:=Prod.fst) _ contDiffAt_fst).mul hg).mul ((starL' ℝ (A:=G.Mat)).contDiff.contDiffAt.comp _
    ((G.exp_jet.comp (contDiff_fst.add (contDiff_fst.comp contDiff_snd))).contDiffAt))

lemma plant_pure (z : G.Color) : plant (d:=d) (z,0,0)=0 := by simp [plant,(end_diff ..).2]
lemma plant_deletes {w : Fin m → G.Color} :
    iteratedFDeriv ℝ m (plant (d:=d)) 0 (fun i => (w i,0,0))=0 := by
  let I : G.Color →L[ℝ] Tuple G d := ContinuousLinearMap.inl ..
  have he := jets_linear I (k:=m) ((plant_analytic d).of_le le_top)
  have hv : plant ∘ (⇑I)=(fun z : G.Color => 0) := funext fun z => plant_pure (d:=d) z
  rw [hv] at he
  change ((iteratedFDeriv ℝ m (plant (d:=d)) 0).compContinuousLinearMap fun _ => I) w = _
  rw [← he]; simp

/-- Use the SAME cover origin convention (initial positive vertices).
No projection on universal stencil values when only the edges in `X` matter. -/
def FitsGrade (o : Site n) (X : Support n) (k : ℕ) (v : Directions G n) :=
  ∀ i : Axis, ∃ p : E4 → G.Color, Degree k p ∧
    ∀ x : Site n, x∈X → x+step i∈X → v (x,i) = p (position (lift (x-o)))

def visible (H : Hol G) (o : Site n) (w : Perturb G d) : Config G n :=
  Lattice.gauge (fun x => G.lieExp (enter w.2 (position (lift (x-o)))))
    (H.testLinks d o (expand d w.1) 1)

def surface (H : Hol G) (o : Site n) (w : Perturb G d) : Directions G n :=
  fun x => G.plog (G.mat (visible H o w x))

lemma visible_mat (H : Hol G) (o : Site n) (i : Edge (Site n)) :
    ContDiffAt ℝ ω (fun k => G.mat (visible H o k i)) (0:Perturb G d) ∧
    visible H o (0:Perturb G d) i=1 := by
  let u j (w : Perturb G d) := G.lieExp (enter w.2 (position (lift (j-o))))
  have h0 (j : Site n) : u j 0=1 := by simp [u]
  let l := (lift (i.1-o),i.2)
  let f (w : Perturb G d) := H.links d (expand d w.1) 1 l
  have he (w) : visible H o w i=u i.1 w * f w * (u (i.1+step i.2) w)⁻¹ := rfl
  have hh (j : Site n) : ContDiffAt ℝ ω (G.mat ∘ u j) 0 := ((G.exp_jet.contDiffAt.comp
    ((0:Perturb G d)) (f:=fun k => Prod.fst (changeIn (position (lift (j-o))) i.2 k))
    (contDiff_fst.comp (changeIn (G:=G) (d:=d) (position (lift (j-o))) i.2).contDiff).contDiffAt))
  have hy := Work.G02.linkGerm H d l
  have hf : ContDiffAt ℝ ω (G.mat ∘ f) 0 := hy.1.contDiffAt.comp (f:=Prod.fst) (0:Perturb G d) contDiffAt_fst
  simp_rw [he]
  constructor
  · simp_rw [G.mat_mul,G.mat_inv]; exact ((hh _).mul hf).mul (((starL' ℝ (A:=G.Mat)).contDiff.contDiffAt).comp _ (hh _))
  rw [h0,h0,show f 0=1 from hy.2.1]; simp

lemma surface_diff (H : Hol G) (o : Site n) : ContDiffAt ℝ ω (surface H o) (0 : Perturb G d) := by
  refine contDiffAt_pi.mpr fun i => ?_
  let f k := G.mat (visible (d:=d) H o k i)
  exact (show ContDiffAt ℝ ω G.plog (f 0) by unfold f; rw [(visible_mat H o i).2,G.mat_one]; exact G.plog_diff).comp 0 (f:=f) (visible_mat H o i).1

@[simp] lemma surface_zero (H : Hol G) (o : Site n) : surface H o (0 : Perturb G d)=0 := by
  funext i; rw [surface,(visible_mat H o i).2,G.mat_one]; exact G.plog_one

lemma place_surface (H : Hol G) (o : Site n) {S : Support n} {x : Site n} (h : Nonwrapping S o)
    (hn : 2 ≤ n.val) (hx : x∈S) (i : Axis) (J : Perturb G d) :
    surface H o J (x,i) = plant (changeIn (position (lift (x-o))) i J) := by
  change G.plog (G.mat (G.lieExp _ * H.links d (expand d J.1) 1 (lift (x-o),i) * (G.lieExp (enter J.2 _))⁻¹)) = _
  rw [lift_end hn h x hx, position_next, ← end_link H]; unfold plant; simp [changeIn]

lemma degree_surface (H : Hol G) (o : Site n) (X : Support n) (h : Nonwrapping X o)
    (hn : 2 ≤ n.val) (p : Fin m → Perturb G d) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i)
    (hp : ∀ i, Phase (a i) (p i)) :
    FitsGrade o X ((∑ i, a i)-1) (iteratedFDeriv ℝ m (surface H o) 0 p) := by
  let j := ∑ i, a i
  let T := iteratedFDeriv ℝ m (plant (d:=d) (G:=G)) 0
  intro u
  refine ⟨(fun x => T (fun i => changeIn x u (p i))),?_,fun x hx _ => ?_⟩
  · let A (r : Fin m) (x : E4) := enter (p r).2 x
    let Z (x : E4) (r : Fin m) : Tuple G d := (A r x,0)
    let Y (x : E4) (r : Fin m) : Tuple G d := (0, A r (x+basis u)-A r x,record x u (p r).1)
    have hy r : Degree (a r - 1) (fun x => Y x r) := by
      let L : G.Color →L[ℝ] Tuple G d := (ContinuousLinearMap.inr ..).comp (ContinuousLinearMap.inl ..)
      let M : Rad G d →L[ℝ] Tuple G d := (ContinuousLinearMap.inr ..).comp (ContinuousLinearMap.inr ..)
      let f (x) := A r (x+basis u)-A r x
      let g (x) := record x u (p r).1
      rw [show (fun x => Y x r) = (L ∘ f) + (M ∘ g) from funext fun x => by simp [f,g,L,M,Y]]
      exact Degree.add (Degree.linear ((hp r).room.difference _) _) (Degree.linear (degree_record (hp r).low u) _)
    have hz i : Degree (a i) (fun x => Z x i) := (hp i).room.linear (ContinuousLinearMap.inl ℝ G.Color (G.Color × Rad G d))
    let b (s : Finset (Fin m)) (i : Fin m) := fun x => s.piecewise (Y x) (Z x) i
    have he x : T (fun i => changeIn x u (p i)) = ∑ s : Finset (Fin m), T (fun i => b s i x) := by
      have hh (i) : changeIn x u (p i)=(Y x + Z x) i := by simp [Y,Z,A,changeIn]
      rw [funext hh]; exact T.map_add_univ ..
    rw [show (fun x => T (fun i => changeIn x u (p i))) = ∑ s, (fun x => T (fun i => b s i x)) by funext x; rw [Finset.sum_apply,he]]
    apply Degree.sum _; intro S _
    by_cases ht : S.Nonempty
    · let w (i) := if i∈S then a i -1 else a i
      obtain ⟨i,hi⟩ := ht
      have he : ∑ i, w i < ∑ i, a i := Finset.sum_lt_sum
        (fun i _ => show w i ≤ a i by by_cases h : i∈S <;> simp [w,h]) ⟨i,Finset.mem_univ _,by rw [show w i=a i-1 from if_pos hi]; exact Nat.sub_lt (ha i) one_pos⟩
      refine Degree.mono (Degree.tensor T (b S) w fun i => ?_) (by omega)
      by_cases hi : i∈S <;> simp only [b,w,Finset.piecewise,hi,↓reduceIte]
      · exact hy i
      exact hz i
    rw [Finset.not_nonempty_iff_eq_empty.mp ht, show (fun x => T fun i => b ∅ i x)=fun _ => 0 from funext fun x => by
      simp only [b,Finset.piecewise_empty]
      exact plant_deletes]
    exact Degree.const 0 _
  let L : Directions G n →L[ℝ] G.Color := ContinuousLinearMap.proj (x,u)
  let y := position (lift (x-o))
  have ht : L ∘ surface (d:=d) H o = plant ∘ (changeIn y u) := funext fun J => place_surface H o h hn hx u J
  have he := L.iteratedFDeriv_comp_left (i:=m) (surface_diff (d:=d) H o) le_top
  change iteratedFDeriv ℝ m (L ∘ (surface H o)) (0:Perturb G d) = _ at he
  rw [ht] at he
  exact congr_arg (fun f : Tensor.T (Perturb G d) G.Color m => f p) (he.symm.trans (jets_linear (changeIn (G:=G) (d:=d) y u) (k:=m) ((plant_analytic d).of_le le_top)))
end YM.Planned.AtomRegular.Flat
