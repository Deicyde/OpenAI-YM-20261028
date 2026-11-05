import YM.Push.STRESS_FLUX.Counts

/-!
# Dilation contraction in real polar weight five
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace
open StressFlux Labels Gauge Maxwell Tensor Analysis Function Set
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff
variable {G : Gauge}

/-- Half the gradient of the curvature total `∑ Fij Fij`. -/
def momentum2 (G : Gauge) (b : Axis) := ∑ i : Axis, ∑ j : Axis, pairDeriv G i j b i j
/-- Half the derivative in direction b of the curvature mountain `∑ Fbi Fbi`. -/
def momentum1 (G : Gauge) (b : Axis) := ∑ i : Axis, pairDeriv G b i b b i
private lemma sumPerm (s : Signed) (F : Axis→Axis→Label G 5) : (∑ i : Axis, ∑ j : Axis, F (s.perm i) (s.perm j))=
    ∑ i : Axis, ∑ j : Axis, F i j:= by
  have h (b): (∑ j, F b (s.perm j)) = ∑ j, F b j := Equiv.sum_comp s.perm _
  simp_rw [h]; exact Equiv.sum_comp s.perm (fun b=>∑ j, F b j)
lemma momentum2_turn (t : Signed) (a : Axis) : tensor t.ortho (momentum2 G a)= sign t a • momentum2 G (t.perm a) := by
  have he i j b : (sign t i*sign t j)*(sign t b*(sign t i*sign t j)) = sign t b := by unfold sign; split_ifs <;> norm_num
  have ht := sumPerm t (fun i j=> pairDeriv G i j (t.perm a) i j)
  simp only [momentum2,map_sum,pairDeriv_turn,he,← Finset.smul_sum,ht]
lemma momentum2_mem : momentum2 G ∈ RawOne G := by
  refine ⟨fun a => ?_,momentum2_turn⟩
  change realBar _ = _; simp [momentum2,pairDeriv_real]
lemma momentum1_mem : momentum1 G ∈ RawOne G := by
  refine ⟨fun a => ?_, fun t a => ?_⟩
  · change realBar _ = _; simp [momentum1,pairDeriv_real]
  change tensor _ _ = _
  have he b j : (sign t b*sign t j)*(sign t b*(sign t b*sign t j)) = sign t b := by unfold sign; split_ifs <;> norm_num
  unfold momentum1; simp only [map_sum,pairDeriv_turn,he,← Finset.smul_sum]
  exact congr_arg (fun z : Label G 5=> sign t a • z) (Equiv.sum_comp t.perm (fun i=>pairDeriv G (t.perm a) i (t.perm a) (t.perm a) i))

-- Certify basis via actual shell jets
lemma curl_degree_one (A : Taylor G 1) (a b i : Axis) (x : E4) : grad i (Tensor.diagonal (takeCurl A a b)) x = curl1 i a b A := by
  let L := ContinuousMultilinearMap.ofSubsingleton ℝ E4 G.Color (0:Fin 1)
  obtain ⟨f,hf⟩ := L.surjective (takeCurl A a b)
  change _=Tensor.diagonal (takeCurl A a b) _
  rw [← hf]; change fderiv ℝ (fun z => f z) x _ = _; rw [f.fderiv]; rfl

lemma shell_affine (A : Taylor G 0) : ∃ X : Maxwell.Shell G 0, gaugeJet X=A := by
  let C:=potential A
  have he : C.val ∈ onShell G.Color 0 := by
    refine ⟨C.property,fun b z=> Finset.sum_eq_zero fun a _=>?_⟩
    rw [show Tensor.diagonal (C.val a b)=fun _=>Tensor.diagonal (C.val a b) 0 from funext fun x=> congr_arg (C.val a b) (Subsingleton.elim ..)]; simp [grad,D]
  refine ⟨⟨C.val,he⟩,?_⟩
  change potential.symm (potential A)=_
  rw [LinearEquiv.symm_apply_apply]

lemma shell_quadratic (A : Taylor G 1) (h : ∀ b : Axis, ∑ i : Axis, curl1 i i b A = 0) :
    ∃ X : Maxwell.Shell G 1, gaugeJet X=A := by
  let C:=potential A
  have he : C.val ∈ onShell G.Color 1 := by
    refine ⟨C.property, fun b x=> ?_⟩
    change ∑ i : Axis, grad i (Tensor.diagonal (takeCurl A i b)) _ = _
    simp only [curl_degree_one]; exact h b
  refine ⟨⟨C.val,he⟩,?_⟩
  change potential.symm (potential A)=_
  rw [LinearEquiv.symm_apply_apply]

def basisV : (Fin 3 → ℝ) →ₗ[ℝ] RawOne G where
  toFun w := w 0 • (⟨momentum1 G,momentum1_mem⟩ : RawOne G) + w 1 • (⟨momentum2 G,momentum2_mem⟩ : RawOne G) + w 2 • (⟨eom G,eom_rows G⟩ : RawOne G)
  map_add' v w := by simp only [Pi.add_apply,add_smul]; abel
  map_smul' t v := by simp only [Pi.smul_apply,smul_eq_mul, smul_add,mul_smul, RingHom.id_apply]
lemma basisV_apply (w : Fin 3 → ℝ) (a : Axis) : ((basisV (G:=G) w).val a) = w 0 • momentum1 G a + w 1 • momentum2 G a + w 2 • eom G a := rfl

set_option maxHeartbeats 600000 in
private lemma test_m (e : G.Color) (he : ‖e‖=1) : ∃ X : TaylorTower G, let J:=fun i=> gaugeJet (X i);
    read J (momentum1 G 0).val=0 ∧ read J (momentum2 G 0).val=(4/3:ℂ) := by
  obtain ⟨x,hx⟩:= shell_affine (leg0 1 2 e)
  obtain ⟨y,hy⟩:= shell_quadratic (leg1 0 1 2 e) (by
     intro b; fin_cases b <;> norm_num [Fin.sum_univ_four,curl1_leg,basis_eq,Fin.ext_iff])
  refine ⟨fun i=> match i with | 0 => x | 1=>y | i+2=>0,?_⟩
  dsimp only
  have he' : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq,he]; ring
  suffices hh : ∀ J : Jet G, J 0 = leg0 1 2 e→J 1=leg1 0 1 2 e →
       read J (momentum1 G 0).val=0 ∧ read J (momentum2 G 0).val=(4/3:ℂ) from hh _ hx hy
  intro J hJ hK; simp only [momentum1, momentum2, AddSubmonoidClass.coe_finsetSum,map_sum]; change (∑ i, read J (pairDeriv ..).val)=_ ∧ (∑ i, ∑ j, read J (pairDeriv ..).val)=_
  simp only [pairDeriv_value,hJ,hK]
  norm_num [Fin.sum_univ_four,curl0_leg,curl1_leg,basis_eq,Fin.ext_iff,real_inner_smul_right,real_inner_smul_left,he]

private lemma test_n (e : G.Color) (he : ‖e‖=1) : ∃ X : TaylorTower G,
    read (fun i=> gaugeJet (X i)) (momentum1 G 0).val=1 := by
  obtain ⟨x,hx⟩:= shell_affine (leg0 0 1 e)
  obtain ⟨y,hy⟩:= shell_quadratic (leg1 0 0 1 e-leg1 2 2 1 e) (by
     intro b; fin_cases b <;> norm_num [Fin.sum_univ_four,curl1_leg,basis_eq,Fin.ext_iff])
  refine ⟨fun i=> match i with | 0 => x | 1=>y | i+2=>0,?_⟩
  suffices hh : ∀ J : Jet G, J 0=leg0 0 1 e→J 1=leg1 0 0 1 e-leg1 2 2 1 e →
       read J (momentum1 G 0).val=1 from hh _ hx hy
  intro J hJ hK; simp only [momentum1, AddSubmonoidClass.coe_finsetSum,map_sum]; change (∑ i, read J (pairDeriv ..).val)=1
  simp only [pairDeriv_value,hJ,hK]
  norm_num [Fin.sum_univ_four,curl0_leg,curl1_leg,basis_eq,Fin.ext_iff,real_inner_smul_right,real_inner_smul_left,he]

lemma through_eq (w : Fin 3 → ℝ) (h : G.Simple) :
    (∀ b : Axis, (basisV w).val b ∈ equationIdeal G 5) ↔ w 0=0 ∧ w 1=0 := by
  constructor
  · intro H
    obtain ⟨v,hv⟩ := has_color h
    have he (X : TaylorTower G) (b : Axis) : let J:=fun i=>gaugeJet (X i);
       w 0 • read J (momentum1 G b).val+w 1 • read J (momentum2 G b).val=0 := by
      have ha:= ideal_meaning.mp (H b) X; simp only [basisV_apply,Submodule.coe_add,Submodule.coe_smul_of_tower,map_add,read_smul,ideal_meaning.mp (eom_null (G:=G) b) X,smul_zero,add_zero] at ha; exact ha
    obtain ⟨X,hX,hY⟩:= test_m v hv
    obtain ⟨Y,hF⟩:= test_n v hv
    have h1 : w 1=0 := by
      have ht:=he X 0; simp only [hX,hY,smul_zero,zero_add] at ht; norm_num [Complex.real_smul] at ht; exact ht
    refine ⟨?_,h1⟩; have ht:=he Y 0; simp [hF,h1, Complex.real_smul] at ht; exact ht
  rintro ⟨hw,hW⟩ b; rw [basisV_apply,hW,hw,zero_smul,zero_smul,add_zero,zero_add]
  rw [ideal_meaning]; intro X; rw [Submodule.coe_smul_of_tower,read_smul,ideal_meaning.mp (eom_null _) X,smul_zero]

lemma coordinates1 (h : G.Simple) : Bijective (basisV (G:=G)) := by
  have hu : Injective (basisV (G:=G)) := by
    refine (LinearMap.ker_eq_bot (R:=ℝ) (R₂:=ℝ) (M:=Fin 3 → ℝ) (M₂:=↥(RawOne G)) (f:=(basisV (G:=G)))).mp ?_
    refine LinearMap.ker_eq_bot'.mpr ?_; intro w hw
    obtain ⟨h1,h2⟩:= (through_eq w h).mp (fun b=>by rw [hw]; exact (equationIdeal G 5).zero_mem)
    have hz : w 2 • eom G=0 := funext fun i=>by
      have he:=basisV_apply (G:=G) w i; rw [hw,h1,h2] at he; simpa using! he.symm
    have hc := (smul_eq_zero.mp hz).resolve_right (eom_nonzero h); ext1 i; fin_cases i <;> simp [*]
  have he:= finrank_one h
  haveI : FiniteDimensional ℝ (Label G 5) := Module.Finite.trans ℂ _
  refine ⟨hu,LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (K:=ℝ) (V:=↥(RawOne G)) ?_)⟩
  have ht:=LinearMap.finrank_range_of_inj hu; rw [Module.finrank_fin_fun] at ht
  exact le_antisymm (Submodule.finrank_le _) (ht.symm ▸ he)

end YM.Trace
