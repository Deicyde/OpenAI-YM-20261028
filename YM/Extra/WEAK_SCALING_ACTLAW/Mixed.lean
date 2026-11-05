import YM.Extra.WEAK_SCALING_ACTLAW.Line
import YM.Extra.WEAK_SCALING_ACTLAW.Pairs

/-! # Weight-five odd labels via the mixed radial curvature pairs -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling.Color
open Function Set Filter Labels Maxwell Tensor Table Climb
open scoped Matrix.Norms.Frobenius Topology InnerProductSpace ContDiff
variable {G : Gauge} {L : Register G}

/-- Linear term of the Taylor curl (one derivative, factorial convention). -/
def higher (A : Taylor G 1) (i j c : Axis) := Tensor.diagonal (takeCurl A i j) (basis c)
lemma antisymmetric (A : Taylor G 1) (i j c : Axis) : higher A i j c = -higher A j i c :=
    congrArg (fun e => Tensor.diagonal e (basis c)) ((closedCurl A).antisymmetric i j)
lemma brand (u : G.El) (A : Taylor G 1) (i j c : Axis) : higher (Taylor.paint u A) i j c = G.adjoint u (higher A i j c) := by
  simp only [higher,takeCurl,Tensor.diagonal,smul_apply,sub_apply,ContinuousMultilinearMap.curryLeft_apply,map_smul,map_sub,Taylor.paint]; rfl

private def dirs (i c : Axis) := Fin.cons (α:=fun _ => E4) (basis i) (fun _ : Fin 1 => basis c)
lemma high_eq (A : Taylor G 1) (i j c : Axis) : higher A i j c = ((1+1:ℕ):ℝ) • (A.val j (dirs i c)-A.val i (dirs j c)) := by
  simp only [higher,takeCurl,Tensor.diagonal,smul_apply,sub_apply,dirs,ContinuousMultilinearMap.curryLeft_apply]

private lemma moved (A : Taylor G 1) (s : Signed) (j i c : Axis) : (Taylor.turn s.ortho⁻¹ A).val j (dirs i c) =
    (Work.A01.eps s j * Work.A01.eps s i * Work.A01.eps s c) • A.val (s.perm j) (dirs (s.perm i) (s.perm c)) := by
  simp only [Taylor.turn, inv_inv, LinearMap.coe_mk, AddHom.coe_mk,sum_apply,smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [Finset.sum_eq_single_of_mem (s.perm j) (Finset.mem_univ _)]
  · let t := Fin.cons (α:=fun _ => ℝ) (Work.A01.eps s i) (fun _ : Fin 1 => Work.A01.eps s c)
    have he k : s.ortho.move (dirs i c k) = t k • dirs (s.perm i) (s.perm c) k :=
      Fin.cases (by simp [t,dirs, Work.A01.move_basis]) (fun j => by simp [t,dirs,Work.A01.move_basis]) k
    change s.ortho⁻¹.val j (s.perm j) • A.val _ (fun k => s.ortho.move _) = _
    rw [funext he, ContinuousMultilinearMap.map_smul_univ,Fin.prod_univ_two]
    change Work.A01.eps s j • (Work.A01.eps s i*Work.A01.eps s c) • _ = _
    module
  intro b _ hb
  rw [show s.ortho⁻¹.val j b = s.matrix b j from rfl]; simp [Signed.matrix_at,Ne.symm hb]

lemma rearranged (A : Taylor G 1) (s : Signed) (i j c : Axis) : higher (Taylor.turn s.ortho⁻¹ A) i j c =
    (Work.A01.eps s i * Work.A01.eps s j * Work.A01.eps s c) • higher A (s.perm i) (s.perm j) (s.perm c) := by
  simp only [high_eq,moved]; module

def datom (i j c : Axis) : G.Color →ₗ[ℝ] Taylor G 1 := by
  let F (x : G.Color) a := (2/3:ℝ) • added ((atom i j x).val a) (compAxis c)
  have hv (x : G.Color) a z : Tensor.diagonal (F x a) z = (2/3:ℝ) • (z c • (atom i j x).value a z) := by unfold F; exact congrArg ((2/3:ℝ) • ·) (added_diag ((atom i j x).val a) (compAxis c) z)
  have he (x : G.Color) : F x ∈ radial G 1 := by
    refine ⟨fun a v s => congrArg ((2/3:ℝ) • ·) (added_sym ((atom i j x).val a) (compAxis c) v s),fun z => ?_⟩
    simp_rw [hv,smul_comm _ (2/3:ℝ),smul_comm (z _) (z c)]
    rw [← Finset.smul_sum, ← Finset.smul_sum, Taylor.radial_value, smul_zero,smul_zero]
  refine ⟨⟨fun x => ⟨_,he x⟩,fun x y => ?_⟩, fun r x => ?_⟩ <;>
    apply Taylor.value_ext <;> funext a z
  · change Tensor.diagonal (F _ _) z = Tensor.diagonal (F _ _) z + Tensor.diagonal (F _ _) z
    rw [hv,hv,hv,map_add]; simp [Taylor.value,Tensor.diagonal,smul_add]
  change Tensor.diagonal (F (r • x) a) z = (r:ℝ) • Tensor.diagonal (F x a) z
  rw [hv,hv,map_smul]; simp only [Taylor.value,Tensor.diagonal,SetLike.val_smul,Pi.smul_apply,smul_apply]; module

lemma datom_value (i j c : Axis) (x : G.Color) (a z) :
    Taylor.value (datom i j c x) a z = (3:ℝ)⁻¹ • z c • ((if a=j then z i • x else 0) - (if a=i then z j • x else 0)) := by
  change (2/3:ℝ) • Tensor.diagonal (added ((atom i j x).val a) (compAxis c)) z = _
  rw [added_diag]; change (2/3:ℝ) • z c • Taylor.value (atom i j x) a z = _; rw [atom_value]; module

lemma paint_datom (u : G.El) (i j c) (x : G.Color) : datom i j c (G.adjoint u x) = Taylor.paint u (datom i j c x) := by
  apply Taylor.value_ext; funext a z; rw [Taylor.paint_value,datom_value,datom_value]; split_ifs <;> simp

abbrev dprobe (i : Fin 6) (c : Axis) (A : Taylor G 1) := higher A (Cube.left i) (Cube.right i) c

lemma dsum (A : Taylor G 1) : A = ∑ i, ∑ c, datom (Cube.left i) (Cube.right i) c (dprobe i c A) := by
  apply Taylor.value_ext; funext a z
  have hz : (∑ a, z a • basis a) = z := by ext i; simp
  have hv (b) : Tensor.diagonal (takeCurl A b a) z = ∑ c, z c • higher A b a c := by
    let F := continuousMultilinearCurryFin1 ℝ E4 G.Color (takeCurl A b a)
    have he (x : E4) : Tensor.diagonal (takeCurl A b a) x = F x := by unfold F; rw [continuousMultilinearCurryFin1_apply, Tensor.diagonal]; congr 1
    simp only [higher,he, ← map_smul, ← map_sum,hz]
  conv_lhs => rw [← potential_recover A,contracted_diag]; simp only [hv]
  simp only [Taylor.value,AddSubmonoidClass.coe_finsetSum,Tensor.diagonal, Finset.sum_apply,sum_apply, dprobe]
  change ((1+2:ℕ):ℝ)⁻¹ • (∑ b, z b • (∑ c, z c • _)) = ∑ i, ∑ c, Taylor.value _ a z
  conv_lhs => arg 2; simp only [Finset.smul_sum]; rw [Finset.sum_comm]
  rw [Finset.smul_sum]; conv_rhs => rw [Finset.sum_comm]; simp only [datom_value]
  have h0 (p c) : higher A p p c = 0 := by
    apply smul_right_injective G.Color (two_ne_zero (α:=ℝ)); change (2:ℝ) • _=(2:ℝ) • 0
    rw [two_smul]; nth_rw 1 [antisymmetric A p p c]; simp
  refine Finset.sum_congr rfl fun c _ => ?_
  have hi : ∀ c : Axis, c=0 ∨ c=1 ∨ c=2 ∨ c=3 := by decide
  have hl : ∀ i : Fin 6, Cube.left i = if i=0 ∨ i=1 ∨ i=2 then 0 else if i=3 ∨ i=4 then 1 else 2 := by decide
  have hr : ∀ i : Fin 6, Cube.right i = if i=0 then 1 else if i=1 ∨ i=3 then 2 else 3 := by decide
  rcases hi a with h|h|h|h <;>
    simp only [Fin.sum_univ_four,Fin.sum_univ_six,h,hl,hr] <;> norm_num [Fin.ext_iff,h0] <;>
      try simp only [antisymmetric A 3 0 c,antisymmetric A 3 1 c,antisymmetric A 3 2 c,antisymmetric A 1 0 c,
        antisymmetric A 2 0 c,antisymmetric A 2 1 c]
  all_goals module

def higherL (a b i : Axis) (c : G.ColorIndex) : Taylor G 1 →ₗ[ℝ] ℝ := {
  toFun A := higher A a b i c
  map_add' _ _ := by simp only [high_eq,Submodule.coe_add,Pi.add_apply,PiLp.smul_apply,PiLp.sub_apply,PiLp.add_apply,add_apply]; dsimp; ring
  map_smul' r A := by simp only [high_eq,SetLike.val_smul,Pi.smul_apply,smul_apply, PiLp.smul_apply,PiLp.sub_apply]; dsimp; ring }

def dpol (a b i : Axis) (c : G.ColorIndex) : Pol G := ∑ k : Fin (dim G 1),
  MvPolynomial.C (↑(higherL a b i c ((axes G 1) k)):ℂ) * MvPolynomial.X (⟨1,k⟩ : Key G)

def mixedPol (G : Gauge) (a b i j k : Axis) := ∑ c : G.ColorIndex, pol a b c * dpol i j k c
lemma dpol_bound (a b i : Axis) (c : G.ColorIndex) : MvPolynomial.IsWeightedHomogeneous generation (dpol a b i c) 3 :=
  MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun t _ => (MvPolynomial.isWeightedHomogeneous_X ℂ generation (⟨1,t⟩ : Key G)).C_mul _)
lemma mixed_bound (a b i j k) : mixedPol G a b i j k ∈ limited G 5 := by
  refine (MvPolynomial.mem_restrictSupport_iff ℂ).mpr fun d hd => (show height d ≤ 5 from le_of_eq ?_)
  exact MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun c _ => (pol_bound a b c).mul (dpol_bound i j k c)) (MvPolynomial.mem_support_iff.mp hd)
lemma dpol_eval (A : Jet G) (a b i : Axis) (c) : Labels.read A (dpol a b i c) = (higher (A 1) a b i c : ℂ) := by
  have he := congrArg (higherL a b i c) ((axes G 1).sum_repr (A 1))
  change _= (↑(higherL a b i c (A 1)):ℂ)
  rw [← he]; simp only [dpol,Labels.read,map_sum,map_smul,map_mul,MvPolynomial.aeval_C,MvPolynomial.aeval_X, Labels.coord,Complex.ofReal_sum,smul_eq_mul,Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
lemma mixed_eval (A : Jet G) (a b i j k : Axis) : Labels.read A (mixedPol G a b i j k) = (inner ℝ (strength (A 0) a b) (higher (A 1) i j k):ℂ) := by
  rw [real_inner_comm,EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct,mixedPol,pol_eval,dpol_eval]

def mixedLabel (G : Gauge) (a b i j k : Axis) : Label G 5 := ⟨mixedPol G a b i j k, mixed_bound .., fun x u => by
  simp only [mixed_eval,colored,painted,brand,real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    ← map_sub,G.norm_adjoint]⟩

abbrev ofPair (G : Gauge) (i j : Fin 6) := mixedLabel G (Cube.left i) (Cube.right i) (Cube.left j) (Cube.right j)

lemma dmoved (g : Signed) (a b i j k : Axis) :
    tensor g.ortho (mixedLabel G a b i j k) =
      (↑(Work.A01.eps g a * Work.A01.eps g b * Work.A01.eps g i * Work.A01.eps g j * Work.A01.eps g k) : ℂ) •
        mixedLabel G (g.perm a) (g.perm b) (g.perm i) (g.perm j) (g.perm k) := by
  apply Subtype.ext; apply Labels.eval_ext; intro A
  change Labels.read A (changed _ (mixedPol ..)) = Labels.read A ((_ :ℂ) • mixedPol ..)
  rw [eval_changed,map_smul,mixed_eval,mixed_eval]; unfold changedJet
  rw [turned,rearranged,real_inner_smul_left,real_inner_smul_right]; push_cast; rw [smul_eq_mul]; ring

private def reversed : Signed := ⟨Equiv.refl _,fun _ => true⟩
private lemma minus (a : Axis) : Work.A01.eps reversed a = -1 := by simp [Work.A01.eps,reversed,Signed.matrix_at]
lemma dinputs (h : G.Simple) (p : Label G 5) : ∃ (e : Label G 5) (b : Fin 6 → Fin 6 → Axis → ℂ),
    p=e + ∑ i, ∑ j, ∑ k, b i j k • ofPair G i j k ∧ Labels.tensor reversed.ortho e = e := by
  obtain ⟨z,Q,R,he,hR⟩ := throughFive h p
  let B (i j : Fin 6) (k : Axis) := ((R.comp (atom (Cube.left i) (Cube.right i))).compl₂ (datom (Cube.left j) (Cube.right j) k))
  have hB i j k (g : G.El) (x y : G.Color) : B i j k (G.adjoint g x) (G.adjoint g y) = B i j k x y := by
    dsimp [B]; rw [paint_atom,paint_datom,hR]
  choose c hc using fun i j k => bilinear_invariant h (B i j k) (hB i j k)
  let e := ∑ i, ∑ j, ∑ k, c i j k • ofPair G i j k
  have hw (A : Jet G) : Labels.read A (p-e).val = z+Q (A 0) (A 0) := by
    rw [Submodule.coe_sub,map_sub,he]; apply sub_eq_of_eq_add
    congr 1
    calc
      R (A 0) (A 1) = ∑ i, ∑ j, ∑ k, R (atom' i (probe' i (A 0))) (datom (Cube.left j) (Cube.right j) k (dprobe j k (A 1))) := by
        conv_lhs => rw [atoms (A 0),dsum (A 1),map_sum R,LinearMap.sum_apply]; simp only [map_sum]
      _ = ∑ i, ∑ j, ∑ k, (inner ℝ (probe' i (A 0)) (dprobe j k (A 1))) • c i j k := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hc i j k _ _
      _ = _ := by simp [e,ofPair,mixedLabel,mixed_eval,probe',dprobe,Complex.real_smul,mul_comm]
  have ht (A : Taylor G 0) : Taylor.turn reversed.ortho⁻¹ A = A := by
    have ht i j := turned reversed A i j; simp only [minus, neg_mul_neg,one_mul,one_smul] at ht
    rw [atoms (Taylor.turn _ A)]; simp only [probe',ht]; exact (atoms A).symm
  refine ⟨p-e,c,(sub_add_cancel ..).symm, Subtype.ext (Labels.eval_ext _ _ fun A => ?_)⟩
  rw [show (tensor _ _).val = changed _ _ from rfl,eval_changed,hw,hw]; dsimp [changedJet]; rw [ht]

def highPin (L : Register G) : Label G 5 →ₗ[ℂ] (Bel L).Field 5 := (Bel L).project 5 ∘ₗ ((standard L.grid).coord 5).coords.toLinearMap
def mixedPin (L : Register G) (a b i j k : Axis) : (Bel L).Field 5 := highPin L (mixedLabel G a b i j k)
abbrev mixedAt (L : Register G) (i j : Fin 6) (k : Axis) := mixedPin L (Cube.left i) (Cube.right i) (Cube.left j) (Cube.right j) k
lemma mixedReal (h : (Bel L).RealSpin) (a b i j k : Axis) : (Bel L).conj h 5 (mixedPin L a b i j k) = mixedPin L a b i j k := by
  unfold mixedPin highPin; rw [LinearMap.comp_apply,Table.conj_project]; apply congrArg
  have he : realBar (mixedLabel G a b i j k) = mixedLabel G a b i j k := Subtype.ext (Labels.eval_ext _ _ (fun A => by
    change Labels.read A (conjPol _) = _; simp only [conj_value,mixedLabel,mixed_eval, Complex.star_def,Complex.conj_ofReal]))
  apply ((standard L.grid).coord 5).coords.symm.injective
  rw [← (standard L.grid).geom_conj,LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,he]

lemma highPin_action (h : (Bel L).RealSpin) (s : Signed) (x : Label G 5) :
    (Bel L).mirror h 5 s (highPin L x) = highPin L (tensor s.ortho x) := by
  simp only [highPin,LinearMap.comp_apply,LinearEquiv.coe_coe,Table.mirror_project,Register.mirrorGroup,Frame.act_coords]

lemma mixedPin_action (h : (Bel L).RealSpin) (s : Signed) (a b i j k : Axis) :
    (Bel L).mirror h 5 s (mixedPin L a b i j k) = (Work.A01.eps s a * Work.A01.eps s b * Work.A01.eps s i * Work.A01.eps s j * Work.A01.eps s k) •
        mixedPin L (s.perm a) (s.perm b) (s.perm i) (s.perm j) (s.perm k) := by
  rw [mixedPin,highPin_action h, dmoved,map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ) (_ * Work.A01.eps s k) (mixedPin ..)]; rfl

lemma odd_center (hg : G.Simple) (H : (Bel L).RealSpin) (x : Axis → (Bel L).Field 5) (hx : x ∈ polar H) :
    ∃ b : Fin 6 → Fin 6 → Axis → ℝ, x 0 = ∑ i, ∑ j, ∑ k, b i j k • mixedAt L i j k := by
  obtain ⟨hr,ho⟩ := hx
  obtain ⟨p,hp⟩ := (((Bel L).onto _).comp ((standard L.grid).coord _).coords.surjective) (x 0)
  change highPin L p=x 0 at hp
  obtain ⟨e,b,rfl,he⟩ := dinputs hg p
  let z := ∑ i, ∑ j, ∑ k, b i j k • mixedAt L i j k
  have ht : highPin L e + z = x 0 := by simp only [map_add,map_sum,map_smul] at hp; exact hp
  have hZ : x 0=z := by
    have hh i j k : (Bel L).mirror H 5 reversed (mixedAt L i j k) = - mixedAt L i j k := by rw [mixedPin_action]; simp only [minus,one_mul,neg_mul,neg_neg, neg_smul, one_smul]; rfl
    have he' := congrArg ((Bel L).mirror H 5 reversed) ht; rw [ho,minus] at he'
    simp only [map_add,z,map_sum,map_smul,hh,smul_neg,Finset.sum_neg_distrib,highPin_action H,he] at he'
    change highPin L e + -z = (↑(-1:ℝ):ℂ) • x 0 at he'
    simp only [Complex.ofReal_neg,Complex.ofReal_one,neg_smul,one_smul] at he'
    apply smul_right_injective _ (two_ne_zero (α:=ℂ)); change (2:ℂ) • _ = (2:ℂ) • _
    rw [two_smul,two_smul,add_neg_eq_iff_eq_add] at *
    rw [he'] at ht
    nth_rw 2 [← ht]; abel
  refine ⟨fun i j k => (b i j k).re,smul_right_injective _ (two_ne_zero (α:=ℂ)) ?_⟩
  change (2:ℂ) • x 0 = (2:ℂ) • _
  nth_rw 1 [two_smul, ← hr 0, hZ]; rw [hZ]
  simp only [z,map_sum,map_smulₛₗ, mixedAt, mixedReal, ← Finset.sum_add_distrib,Finset.smul_sum, ← add_smul, add_comm ((starRingEnd ℂ) _) (b _ _ _), Complex.add_conj,RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => congrArg (fun c : ℂ => c • _) (Complex.ofReal_mul ..)

lemma highPin_null (p : Label G 5) (h : p ∈ equationIdeal G 5) : highPin L p=0 := by
  let F := (L.grid.level 5).coords
  rw [show highPin L p=(Bel L).project _ (F p) from rfl]; exact Submodule.Quotient.mk_eq_zero _ |>.mpr
    ((projectionExact L.grid).mp (by
      rw [show snap L.grid 5 (F p)=0 from Subtype.ext (show (snap L.grid 5 (F p)).val=0 by
        change observable G 5 (F.symm (F p))=0; rw [F.symm_apply_apply]; exact h)]
      exact Submodule.zero_mem _))

lemma mixedPin_left (a b i j k : Axis) : mixedPin L a b i j k = -mixedPin L b a i j k := by
  unfold mixedPin; rw [← map_neg]; apply congrArg; apply Subtype.ext; apply Labels.eval_ext; intro A
  change Labels.read A (mixedPol ..)=Labels.read A (-mixedPol ..)
  rw [map_neg,mixed_eval,mixed_eval,skew (A 0) a b,inner_neg_left,Complex.ofReal_neg]

lemma mixedPin_right (a b i j k : Axis) : mixedPin L a b i j k = -mixedPin L a b j i k := by
  unfold mixedPin; rw [← map_neg]; apply congrArg; apply Subtype.ext; apply Labels.eval_ext; intro A
  change Labels.read A (mixedPol ..)=Labels.read A (-mixedPol ..)
  rw [map_neg,mixed_eval,mixed_eval,antisymmetric (A 1) i j k,inner_neg_right,Complex.ofReal_neg]

private lemma strengthShell (A : TaylorTower G) (i j k : Axis) : higher (gaugeJet (A 1)) i j k = Maxwell.grad k (Tensor.diagonal ((A 1).val i j)) 0 := by
  let F := continuousMultilinearCurryFin1 ℝ E4 G.Color ((A 1).val i j)
  have he : Tensor.diagonal ((A 1).val i j) = ⇑F := by
    funext x; unfold F; rw [Tensor.diagonal,continuousMultilinearCurryFin1_apply]; congr 1
  rw [higher, match_leg, he, Maxwell.grad,Analysis.D,F.fderiv]

lemma mixedPin_delta (a b i : Axis) : ∑ k : Axis, mixedPin L a b k i k = 0 := by
  unfold mixedPin; rw [← map_sum]; apply highPin_null
  refine ideal_meaning.mpr fun X => ?_
  simp only [AddSubmonoidClass.coe_finsetSum, mixedLabel,map_sum,mixed_eval,strengthShell,← Complex.ofReal_sum, ← inner_sum,(X 1).property.2,inner_zero_right,Complex.ofReal_zero]

lemma mixedPin_closed (a b i j k : Axis) : mixedPin L a b i j k + mixedPin L a b j k i + mixedPin L a b k i j = 0 := by
  unfold mixedPin; simp_rw [← map_add]; apply highPin_null
  refine ideal_meaning.mpr fun X => ?_
  have he : ClosedJet (X 1).val := (X 1).property.1
  simp only [Submodule.coe_add,mixedLabel,map_add,mixed_eval,strengthShell, ← Complex.ofReal_add,← inner_add_right, he.closed, inner_zero_right,Complex.ofReal_zero]
end YM.Extra.WeakScaling.Color
