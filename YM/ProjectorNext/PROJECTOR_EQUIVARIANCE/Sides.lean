import YM.Next.FOUNDATIONS.SU2
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links

/-!
# Derivatives of reversed links

To pay `remBound` after reorientation have to understand the higher *ordered*
left derivatives. Negatively read links will use RIGHT derivatives. Give
an exact calculus at smooth germs (works at equality in B.Regular). In
particular left and right derivatives commute on a smooth germ even for this
matrix group. This does **not** say that left derivatives commute.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Lattice Wilson RG Analysis Next.Foundations
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}

/-- Convert from right to left at this base array. -/
def leftDir (U : Config G n) : Directions G n →ₗ[ℝ] Directions G n where
  toFun A e := G.adjoint (U e) (A e)
  map_add' A B := by funext e; change G.adjoint _ (_ + _) = _; rw [map_add]; rfl
  map_smul' c A := by funext e; change G.adjoint _ (c • _) = _; rw [map_smul]; rfl

/-- false = E uses these (left-increment frame); true = right increments. -/
def glide (r : Bool) (U : Config G n) (A : Directions G n) :=
  if r then fun e => U e * G.lieExp (A e) else increment U A

lemma right_eq_left (U : Config G n) (A : Directions G n) : glide true U A = increment U (leftDir U A) := by
  funext e
  change U e * G.lieExp (A e) = G.lieExp (G.adjoint _ _) * U e
  rw [exp_adjoint]; group

lemma glide_both (U : Config G n) (A B : Directions G n) :
    glide true (glide false U A) B = glide false (glide true U B) A := by
  funext e; exact mul_assoc ..

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : Config G n → Y} {U : Config G n} {k : ℕ}

/-- Only the *germ* in the good coordinates. -/
def HasOrderAt (f : Config G n → Y) (U : Config G n) (k : ℕ) := ContDiffAt ℝ k (f ∘ increment U) 0

namespace HasOrderAt

private def fuseDirs (q : Directions G n × Directions G n) : Directions G n :=
  fun e => G.plog (G.mat (G.lieExp (q.2 e)*G.lieExp (q.1 e)))

private lemma originDirs : fuseDirs (0 : Directions G n × Directions G n) = 0 := by
  funext e; simp [fuseDirs]

private lemma regularDirs : ContDiffAt ℝ ω (fuseDirs (G:=G) (n:=n)) 0 := by
  refine contDiffAt_pi.mpr fun e => ?_
  have hg : ContDiff ℝ ω (fun v : Directions G n × Directions G n =>
      G.mat (G.lieExp (v.2 e) * G.lieExp (v.1 e))) :=
    (G.exp_jet.comp ((contDiff_apply ℝ G.Color e).comp contDiff_snd)).mul
      (G.exp_jet.comp ((contDiff_apply ℝ G.Color e).comp contDiff_fst))
  refine ContDiffAt.comp (f:=fun v => _) (g:=G.plog) _ ?_ hg.contDiffAt
  simp only [Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,G.mat_lieExp_zero,one_mul,G.mat_one]
  exact G.plog_diff

lemma stacked (h : HasOrderAt f U k) :
    ContDiffAt ℝ k (fun q : Directions G n × Directions G n => f (increment (increment U q.1) q.2)) 0 := by
  have he : (fun q : Directions G n × Directions G n => increment (increment U q.1) q.2) =ᶠ[𝓝 0]
      increment U ∘ fuseDirs := by
    suffices hh : ∀ i, ∀ᶠ v : Directions G n × Directions G n in 𝓝 0,
        increment (increment U v.1) v.2 i = increment U (fuseDirs v) i by
      filter_upwards [eventually_all.mpr hh] with x hx; exact funext hx
    intro i
    let g (q : Directions G n × Directions G n) := G.lieExp (q.2 i)*G.lieExp (q.1 i)
    have hh : Tendsto g (𝓝 0) (𝓝 1) := by
      rw [← show g 0=1 by simp [g]]; exact (show Continuous g by unfold g; fun_prop).tendsto _
    filter_upwards [hh.eventually G.plog_right] with q hq
    unfold increment fuseDirs
    rw [← mul_assoc, show G.lieExp _ = g q from hq]
  exact (((originDirs.symm ▸ (show ContDiffAt ℝ k (f ∘ increment U) 0 from h)) : ContDiffAt ℝ k
    (f ∘ increment U) (fuseDirs 0)).comp 0 (regularDirs.of_le le_top)).congr_of_eventuallyEq (he.fun_comp f)

lemma nearby (h : HasOrderAt f U k) (s : Bool) (A : Directions G n) :
    ∀ᶠ t : ℝ in 𝓝 0, HasOrderAt f (glide s U (t • A)) k := by
  have hh (B : Directions G n) : ∀ᶠ t : ℝ in 𝓝 0, HasOrderAt f (increment U (t • B)) k := by
    let q (t : ℝ) := (t • B,(0:Directions G n))
    have ht : Tendsto q (𝓝 0) (𝓝 0) := by
      rw [← show q 0=0 by simp [q,Prod.zero_eq_mk]]; exact (show Continuous q by unfold q; fun_prop).tendsto _
    filter_upwards [ht.eventually (h.stacked.eventually (by simp))] with i hi
    exact hi.comp 0 (f:=fun x => (i • B,x)) (contDiffAt_const.prodMk contDiffAt_id)
  cases s
  · exact hh _
  simp_rw [right_eq_left,map_smul]; exact hh _

lemma crossed (h : HasOrderAt f U k) :
    ContDiffAt ℝ k (fun q : Directions G n × Directions G n => f (glide true (increment U q.1) q.2)) 0 := by
  let L := (leftDir U).toContinuousLinearMap
  let r (q : Directions G n × Directions G n) := (L q.2,q.1)
  have ht : r 0=0 := by simp [r,Prod.zero_eq_mk]
  have hh (A B : Directions G n) : glide true (increment U A) B = increment (increment U (L B)) A := by
    change glide true (glide false _ _) _ = _; rw [glide_both,right_eq_left]; rfl
  simp_rw [hh]
  have hC : ContDiff ℝ k r := by unfold r; fun_prop
  exact ((ht.symm ▸ h.stacked) : ContDiffAt ℝ k _ (r 0)).comp _ hC.contDiffAt
end HasOrderAt

abbrev Instruction (G : Gauge) (n : Side) := Bool × Directions G n

def opD (i : Instruction G n) (f : Config G n → Y) (U : Config G n) :=
  deriv (fun t : ℝ => f (glide i.1 U (t • i.2))) 0

def word (l : List (Instruction G n)) (f : Config G n → Y) := l.foldr opD f



lemma smooth_op (i : Instruction G n) (h : HasOrderAt f U (k+1)) : HasOrderAt (opD i f) U k := by
  let M (a : Directions G n) (s : ℝ) := f (glide i.1 (increment U a) (s • i.2))
  change ContDiffAt ℝ k (fun a : Directions G n => fderiv ℝ (M a) 0 1) 0
  have he : ContDiffAt ℝ (↑(k+1 : ℕ)) (uncurry M) 0 := by
    let L (p : Directions G n × ℝ) := (p.1,p.2 • i.2)
    have hl : L 0 = 0 := by simp [L, Prod.zero_eq_mk]
    have H : ContDiffAt ℝ (↑(k+1 : ℕ)) (fun q : Directions G n × Directions G n =>
        f (glide i.1 (increment U q.1) q.2)) 0 := by
      cases i.1
      · exact h.stacked
      · exact h.crossed
    exact ((hl.symm ▸ H) : ContDiffAt ℝ _ _ (L 0)).comp 0 (f:=L) (by unfold L; fun_prop)
  exact (he.fderiv (f:=M) (g:=fun _ => 0) (m:=↑k) contDiffAt_const (by push_cast; rfl)).clm_apply
    (g:=fun _ => (1:ℝ)) contDiffAt_const

lemma smooth_word (l : List (Instruction G n)) (h : HasOrderAt f U (l.length + k)) :
    HasOrderAt (word l f) U k := by
  induction l generalizing k with
  | nil => simpa [word] using h
  | cons i l ih => exact smooth_op i (ih (by simpa only [List.length_cons,add_assoc,add_comm k] using h))

lemma op_to_left (A : Directions G n) : opD (true,A) f U = opD (false,leftDir U A) f U := by
  unfold opD; simp_rw [right_eq_left,map_smul]; rfl

private lemma diff_x {g : ℝ × ℝ → Y} {x y : ℝ} (h : DifferentiableAt ℝ g (x,y)) :
    deriv (fun t : ℝ => g (t,y)) x = D (1,0) g (x,y) :=
  (h.hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id' x).prodMk (hasDerivAt_const x y))).deriv

private lemma diff_y {g : ℝ × ℝ → Y} {x y : ℝ} (h : DifferentiableAt ℝ g (x,y)) :
    deriv (fun t : ℝ => g (x,t)) y = D (0,1) g (x,y) :=
  (h.hasFDerivAt.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id' y))).deriv

/-- Ordinary mixed derivatives for a locally smooth two-sided variation. -/
lemma op_exchange (A B : Directions G n) (h : HasOrderAt f U 2) :
    opD (false,A) (opD (true,B) f) U = opD (true,B) (opD (false,A) f) U := by
  let M (p : ℝ × ℝ) := f (glide true (glide false U (p.1 • A)) (p.2 • B))
  have he : ContDiffAt ℝ 2 M (0,0) := by
    let L (p : ℝ × ℝ) := (p.1 • A,p.2 • B)
    have hp : L (0,0) = 0 := by simp [L,Prod.zero_eq_mk]
    have hx : ContDiffAt ℝ 2 (fun q : Directions G n × Directions G n =>
        f (glide true (increment U q.1) q.2)) (L (0,0)) := by rw [hp]; simpa using h.crossed
    exact hx.comp _ (f:=L) (by unfold L; fun_prop)
  have H := he.eventually (by simp)
  have hh (i : ℝ × ℝ) : DifferentiableAt ℝ (D i M) (0,0) :=
    (dSmooth (m:=1) he i (by norm_num)).differentiableAt one_ne_zero
  have hx : deriv (fun t : ℝ => deriv (fun u : ℝ => M (t,u)) 0) 0 = D (1,0) (D (0,1) M) (0,0) := by
    rw [← diff_x (hh (0,1))]
    refine Filter.EventuallyEq.deriv_eq ?_
    have hl : Tendsto (fun t : ℝ => (t,(0:ℝ))) (𝓝 0) (𝓝 (0,0)) := (by fun_prop : Continuous _).tendsto 0
    filter_upwards [hl.eventually H] with t ht; exact diff_y (ht.differentiableAt (by norm_num))
  have hy : deriv (fun u : ℝ => deriv (fun t : ℝ => M (t,u)) 0) 0 = D (0,1) (D (1,0) M) (0,0) := by
    rw [← diff_y (hh (1,0))]
    refine Filter.EventuallyEq.deriv_eq ?_
    have hl : Tendsto (fun t : ℝ => ((0:ℝ),t)) (𝓝 0) (𝓝 (0,0)) := (by fun_prop : Continuous _).tendsto 0
    filter_upwards [hl.eventually H] with t ht; exact diff_x (ht.differentiableAt (by norm_num))
  unfold opD; simp_rw [← glide_both]; exact hx.trans ((commuteD he (1,0) (0,1)).trans hy.symm)

end YM.ProjectorNext.Equivariance
