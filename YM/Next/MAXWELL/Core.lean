import YM.Next.MAXWELL.Studio

/-! # A finite test for every weight: reflected point-pair -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis Table.Pairing Wick Factorization Fock
open scoped ContDiff Topology BigOperators ComplexOrder
variable {G : Gauge}

def score (a : Axis) (x : E4) (p q : WickPol G) :=
  cabinet a (points fun _ : Fin 1 => x) (points fun _ : Fin 1 => x) (fun _ => p) (fun _ => q)

section cert
variable (a : Axis) (x : E4)
private lemma fix (T : MultilinearMap ℂ (fun _ : Fin 1 => WickPol G) ℂ) (p) :
    T.toLinearMap (fun _ => 0) 0 p=T (fun _ => p) := by
  rw [MultilinearMap.toLinearMap_apply]
  congr 1; ext1 i; fin_cases i; simp

private def sideL (q : WickPol G) : WickPol G →ₗ[ℂ] ℂ := (towerL a
  (points fun _ : Fin 1 => x) (points fun _ : Fin 1 => x) (fun _ => q)).toLinearMap (fun _ => 0) 0

private lemma fixL (p q : WickPol G) : sideL a x q p = star (score a x p q) := fix _ _

private def sideR (p : WickPol G) : WickPol G →ₗ[ℂ] ℂ := (towerR a
  (points fun _ : Fin 1 => x) (points fun _ : Fin 1 => x) (fun _ => p)).toLinearMap (fun _ => 0) 0

private lemma fixR (p q : WickPol G) : sideR a x p q = score a x p q := fix _ _

lemma score_add (p q r : WickPol G) : score a x (p+q) r = score a x p r + score a x q r := by
  apply star_injective; rw [star_add]; simp_rw [← fixL]; exact map_add _ _ _

lemma score_scale (p q : WickPol G) (c : ℂ) : score a x (c • p) q=star c * score a x p q := by
  apply star_injective; rw [star_mul]; simp_rw [← fixL,map_smul,smul_eq_mul,star_star,mul_comm c]

lemma score_extend (p q r : WickPol G) : score a x p (q+r) = score a x p q + score a x p r := by
  simp_rw [← fixR]; exact map_add _ _ _

lemma score_rescale (p q : WickPol G) (c : ℂ) : score a x p (c • q)=c * score a x p q := by
  simp_rw [← fixR]; exact map_smul _ _ _

/-- Explicit isometry formula in one finite polynomial chart (including scalar sector). -/
lemma core (hx : 0 < x a) (s : Finset (Slot G)) (L : Matrix s s ℝ)
    (h : mat a (fun i : s => ((x,coordF i.val):Limb G)) = star L * L) (p q : Fock.Space s) :
    let I : Fock.Space s →ₐ[ℂ] WickPol G := MvPolynomial.rename (fun i : s => (i.val : Slot G))
    let T : Fock.Space s →ₐ[ℂ] Fock.Space s := MvPolynomial.aeval (fun i : s => synth fun j : s => ((L j i:ℝ):ℂ))
    score a x (I p) (I q) = form (T p) (T q) := by
  intro I T
  classical
  let z : ↥s → Fin 1 := fun i => 0
  let e (i : ↥s) := coordF (i.val)
  let X (r : List (↥s)) : Fock.Space s := (r.map MvPolynomial.X).prod
  have he (r : List (↥s)) (i : Fin 1) : I (X r) = bag z e r i := by
    induction r with
    | nil => exact map_one I
    | cons d r ih =>
      change I (MvPolynomial.X d * X r)=_
      rw [map_mul,ih,bag_cons,if_pos (Subsingleton.elim i (z d))]
      rw [show e d = _ from rfl]; congr 1
      exact (MvPolynomial.rename_X _ _).trans (letter_coord _).symm
  let Q (i : ↥s) := ((x,e i):Limb G)
  let F (i j : ↥s) := linkEntry (Q i) (Q j)
  let D := fun i : ↥s => fun j => ((L j i:ℝ):ℂ)
  have ht (r : List (↥s)) : packet F D r=T (X r) := by
    induction r with
    | nil => rw [packet]; exact (map_one T).symm
    | cons d r ih =>
      rw [packet_rule, ih, pulls]; simp only [show ∀ i, F d i = 0 from fun i => link_zero ..,
        zero_smul,Finset.sum_const_zero,add_zero]
      change _ = T (MvPolynomial.X d * X r); rw [map_mul]; congr 1
      exact (MvPolynomial.aeval_X (fun i : s => synth (D i)) d).symm
  have hv (r t) : score a x (I (X r)) (I (X t)) = form (T (X r)) (T (X t)) := by
    unfold score
    rw [funext (fun i => he r i), funext (fun i => he t i)]
    have H : single (points fun _ : Fin 1 => x) a := ⟨injective_of_subsingleton _,fun i => hx⟩
    rw [cabinet_bag _ _ _ _ _ _ a (Table.Pairing.spans H H),← ht,← ht]
    exact halves (bottomEntry a ∘ Q) Q _ F D (fun i j => link_ray a _ _) (fun i j => rfl)
      (fun i j => entry_match a Q _ h i j (fun i => hx)) _ _
  have hm (u : ↥s →₀ ℕ) : ∃ r : List s, ∀ c : ℂ, MvPolynomial.monomial u c=c • X r := by
    obtain ⟨L,hL,_,_⟩ := mon_list u
    refine ⟨L,fun c => ?_⟩
    unfold X; rw [← hL]; simp only [MvPolynomial.coe_basisMonomials,MvPolynomial.smul_monomial,smul_eq_mul,mul_one]
  induction p using MvPolynomial.induction_on' with
  | add p r hp hr => rw [map_add,map_add, score_add,form_extend,hp,hr]
  | monomial u c =>
    obtain ⟨r,hr⟩ := hm u
    rw [hr c,map_smul,map_smul,score_scale,form_rescale]; congr 1
    induction q using MvPolynomial.induction_on' with
    | add q w hq hw => rw [map_add,map_add, score_extend,form_add,hq,hw]
    | monomial v d =>
      obtain ⟨t,hd⟩ := hm v; rw [hd d, map_smul,map_smul,score_rescale,form_scale,hv r t]

lemma detects (hx : 0 < x a) (p : WickPol G) (hp : p≠0) : 0 < score a x p p := by
  classical
  let s := p.vars
  let I : Fock.Space s →ₐ[ℂ] WickPol G := MvPolynomial.rename (fun i : s => i.val)
  obtain ⟨P,hP⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range p (fun i : s => i.val) Subtype.val_injective
    (fun x hx => ⟨⟨x,hx⟩,rfl⟩)
  change I P=p at hP
  have hu : P≠0 := fun H => hp (by conv_lhs => rw [← hP,H,map_zero])
  let Q (i : s) := ((x,coordF i.val):Limb G)
  obtain ⟨L,hL⟩ := columns a Q (fun i => hx)
  have hb : IsUnit L := by
    have hw := (coordGram a x hx s).isUnit; change IsUnit (mat a Q) at hw
    rw [hL,Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, IsUnit.mul_iff] at hw
    exact (Matrix.isUnit_iff_isUnit_det L).mpr hw.2
  let T : Fock.Space s →ₐ[ℂ] Fock.Space s := MvPolynomial.aeval (fun i : s => synth fun j : s => ((L j i:ℝ):ℂ))
  rw [← hP]; rw [show score a x (I P) (I P) = form (T P) (T P) from core a x hx s L hL P P]
  exact form_strict _ (fun ht => hu (synth_inj L hb (show T P = T 0 from ht.trans (map_zero T).symm)))
end cert
end YM.Maxwell.Free
