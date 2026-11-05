import YM.ProjectorNext.PROJECTOR_CALIBRATION.Revenue


/-! # Fixed triangular model

Construct from the limiting linear jets of the gauge-covariant stencil, by
polynomial algebra and truncation in the same label frame. No campaigning,
Compares or any subsequence hypothesis needed for triangularity. -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice RG Wilson Source Source.Drops Function Filter Tensor Work Labels Next.Foundations Push.CutoffProjectors
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ}

/- Real tensor evaluated on truncated data, yield actual polynomial. Adapt
G05 / FOUNDATIONS.Readout proof (over ℓ here arbitrary, not the
Fréchet Taylor order). -/
set_option maxHeartbeats 600000 in
set_option synthInstance.maxHeartbeats 60000 in
private lemma as_poly (l : ℕ) (B : Tensor.T (Snap G d) ℂ l) :
    ∃ u : Pol G, ∀ J : Jet G, Labels.read J u = Tensor.diagonal B (trunk d J) := by
  classical
  let I := (i : Level d) × Fin (Labels.dim G i.val)
  let v (i : I) : Key G := ⟨i.1.val,i.2⟩
  let r (J : Jet G) (i : I) := ((axes G i.1.val).repr (J i.1.val)) i.2
  let P (i : I) : Snap G d := firing i.1 (axes G i.1.val i.2)
  have he (J : Jet G) : trunk d J = ∑ i : I, r J i • P i := by
    funext k; symm
    rw [Fintype.sum_sigma,Finset.sum_apply,Finset.sum_eq_single k]
    · simp only [Finset.sum_apply,Pi.smul_apply,P,firing,LinearMap.single_apply,Pi.single_eq_same]
      exact (axes G k.val).sum_repr (J k.val)
    · intro i _ hi; simp [Finset.sum_apply,P,firing,Pi.single_eq_of_ne hi.symm]
    simp
  induction l with
  | zero =>
    refine ⟨MvPolynomial.C (Tensor.diagonal B 0),fun J => ?_⟩
    simp only [Labels.read,MvPolynomial.aeval_C,Algebra.algebraMap_self,RingHom.id_apply]; exact congr_arg B (Subsingleton.elim ..)
  | succ l ih =>
    choose p hp using fun i : I => ih (B.curryLeft (P i))
    refine ⟨∑ i, MvPolynomial.X (v i)*p i, fun J => ?_⟩
    let A := trunk d J
    have hb : Tensor.diagonal B A = Tensor.diagonal (B.curryLeft A) A := by
      apply congr_arg B; ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
    change Labels.read J _ = Tensor.diagonal B A; rw [hb]
    rw [show B.curryLeft A=∑ i : I, r J i • B.curryLeft (P i) from by rw [show A = _ from he J,map_sum]; simp]
    rw [Tensor.diagonal,sum_apply,_root_.map_sum]; exact Finset.sum_congr rfl fun i _ => by
      rw [map_mul, hp, smul_apply,Complex.real_smul,Labels.read,MvPolynomial.aeval_X]; rfl

namespace Machine
variable (M : Machine H d) (F : Labels.Frame G d)

def shadeLaw (i : F.Index) (A : Snap G d) := Cross.mix (shade F i) M.U A (M.liftAll A)

lemma by_tensor (i : F.Index) : ∃ B : Tensor.T (Snap G d) ℂ (F.grades i).2, M.shadeLaw F i = Tensor.diagonal B := by
  let X := Snap G d
  let l := (F.grades i).2
  let Q (j k : Fin l) : X →L[ℝ] X := if k=j then LinearMap.toContinuousLinearMap M.liftAll else
      if k < j then ContinuousLinearMap.id _ _ else LinearMap.toContinuousLinearMap M.U
  let B := ∑ j, (shade F i).compContinuousLinearMap (Q j)
  refine ⟨B,funext fun A => ?_⟩
  unfold shadeLaw; rw [Cross.mixSum]; unfold B Tensor.diagonal; rw [sum_apply]
  refine Finset.sum_congr rfl fun j _ => congr_arg _ ?_
  ext1 k; by_cases hk : k=j
  · subst k; simp [Cross.cell,Q]
  simp only [Cross.cell,update_of_ne hk,Cross.field,Q,if_neg hk]
  split <;> rfl

private lemma poly_law (i : F.Index) : ∃ u : Pol G, ∀ J, Labels.read J u = M.shadeLaw F i (trunk d J) := by
  obtain ⟨B,hB⟩ := M.by_tensor F i
  obtain ⟨u,hu⟩ := as_poly _ B; exact ⟨u,fun J => (hu J).trans (congr_fun hB (trunk d J)).symm⟩

def amethyst (i : F.Index) := capRead d (M.poly_law F i).choose

lemma shade_closed (i : F.Index) (A : Snap G d) (u : G.El) :
    M.shadeLaw F i (Cast u A)=M.shadeLaw F i A := by
  unfold shadeLaw; rw [M.intertwines]
  trans (1:ℝ) • Cross.mix (shade F i) M.U A (M.liftAll A)
  · exact Cross.scaled_mix (shade F i) M.U (castAction u (d:=d)) 1 (fun x => by
      rw [one_smul]; exact painting (F.grades i).2 (F.pure i) u x) (fun a => M.toSplit.comm ..) _ _
  exact one_smul ..

lemma legit (i : F.Index) : M.amethyst F i ∈ localFields G d := by
  let P := (M.poly_law F i).choose
  refine ⟨cap_limited .., fun J u => ?_⟩
  have he (t : ℝ) : trunk d (scaleJet (colored u J) t) = Cast u (trunk d (scaleJet J t)) := by
    funext j; unfold trunk scaleJet Cast colored; rw [map_smul]
  have h (t : ℝ) : Labels.read (scaleJet (colored u J) t) P = Labels.read (scaleJet J t) P := calc
    _ = _ := (M.poly_law F i).choose_spec _
    _ = M.shadeLaw F i (trunk d (scaleJet J t)) := by rw [he,M.shade_closed]
    _ = _ := ((M.poly_law F i).choose_spec _).symm
  have hu (n : ℕ) : Labels.read (colored u J) (tier n P) = Labels.read J (tier n P) := by
    apply smul_right_injective ℂ (show (↑(n.factorial):ℝ)≠0 by positivity)
    change (↑(n.factorial):ℝ) • _ = (↑(n.factorial):ℝ) • _
    rw [← deriv_read, ← deriv_read,funext h]
  change Labels.read (colored u J) (capRead d P) = Labels.read J (capRead d P)
  unfold capRead; simp [hu]

def stone (i : F.Index) : Label G d := ⟨_,M.legit F i⟩

lemma observed (i : F.Index) (k : Lens G d) : probe F k (F.coords (M.stone F i)) = M.calendar F i k 0 0 := by
  let P := (M.poly_law F i).choose
  have h (t : ℝ) := (M.poly_law F i).choose_spec (scaleJet k.1 t)
  rw [probe_eq,F.coords.symm_apply_apply,M.as_recorded]
  trans iteratedDeriv k.2.val (fun t => Labels.read (scaleJet k.1 t) P) 0
  · rw [deriv_read,deriv_read]; exact congrArg _ (congrArg (Labels.read k.1) (tier_capRead d P k.2.val (Nat.le_of_lt_succ k.2.isLt)))
  simp_rw [P,h]; rfl

/-- T is the cutoff-independent holonomy model for these valves. Canonical
also when machines use different path choices; refers to no future fit
values. (Not asserting equality of these models *between* choices.) -/
def trophy : Model F := ( (∑ i : F.Index, (LinearMap.toSpanSingleton ℂ _ (F.coords (M.stone F i))).comp (LinearMap.proj i)).comp
    (equationSpace F).subtype).toContinuousLinearMap

lemma spends (x : equationSpace F) (i : Lens G d) :
    probe F i (M.trophy F x)=∑ k : F.Index, x.val k*M.calendar F k i 0 0 := by
  change probe F i ((_ : F.Coeff →ₗ[ℂ] F.Coeff) (x:F.Coeff)) = _
  rw [LinearMap.sum_apply, _root_.map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  change probe F i (x.val k • F.coords (M.stone F k)) = _
  rw [map_smul,M.observed]; rfl
end Machine
end YM.ProjectorNext.Calibration
