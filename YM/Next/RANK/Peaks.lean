import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import YM.Next.RANK.Along



/-!
# Compare the weighted read with its first linear stencil IN θ variables

At the finitely many required real Snap tests, all vertex h-derivatives of the
old readout before evaluating P cost only polynomial; revealing the nonlinear
transport gives ≥ one extra power of attenuation from Snap weights for every
order. Uses at B projection keep this through even k periods before paying. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Source Labels Source.Drops Lattice Wilson RG Asymptotics Filter Set Function
open scoped Classical Topology Matrix.Norms.Frobenius BigOperators ContDiff

section
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma guiding (L : E →L[ℝ] V) (p : ℝ → E) (m : ℕ) (t : ℝ) (h : ContDiffAt ℝ m p t) :
    iteratedDeriv m (L ∘ p) t=L (iteratedDeriv m p t) := by rw [iteratedDeriv_eq_iteratedFDeriv,iteratedDeriv_eq_iteratedFDeriv,L.iteratedFDeriv_comp_left h le_rfl]; rfl

private lemma hears (L : E →L[ℝ] V) {n : ℕ} (hn : 1 < n) (x : E) : slopeCap n L x=0 := by
  obtain ⟨v,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
  unfold slopeCap; rw [← norm_iteratedFDeriv_fderiv,show fderiv ℝ L=(fun _ => L) from funext fun x=> L.fderiv,iteratedFDeriv_const_of_ne (show v≠0 by omega)]; simp

private lemma shore (S : ℝ → E) (i : ℕ) (hz : S 0=0) (h : ContDiffAt ℝ i S 0) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ F : E→ V, ∀ (M t : ℝ), 0 ≤ M → F 0=0 → 0 < t → t ≤ 1 →
      (∀ k,k≤max 1 i → slopeCap k F 0 ≤ M) → ContDiffAt ℝ (max 1 i:ℕ) F 0 →
        let A:= fderiv ℝ F 0
        let p:= A∘S
        let W:= t⁻¹ • (F∘(t • S))
        ‖iteratedDeriv i p 0‖≤ M*C ∧ ContDiffAt ℝ i W 0 ∧ ‖iteratedDeriv i (W-p) 0‖ ≤ M*C*t := by
  let R (p : OrderedFinpartition i):=∏ j, ‖iteratedDeriv (p.partSize j) S 0‖
  let L:= ‖iteratedDeriv i S 0‖
  let C:= L+∑ j,R j
  have hl (p : OrderedFinpartition i) : 0 ≤ R p := by dsimp only [R]; positivity
  have hu : 0≤L := norm_nonneg _
  have hv' : 0 ≤ ∑ j,R j := Finset.sum_nonneg fun _ _ => hl _
  refine ⟨C,add_nonneg hu hv',fun F M t hm hF ht h₁ hw hp => ?_⟩
  intro A p W
  let Y:=F-⇑A
  have ho : slopeCap 0 Y 0=0 := by unfold Y; rw [slope0, Pi.sub_apply,hF,map_zero]; simp
  have hY : ∀ k,k ≤ i → ContDiffAt ℝ k Y 0 := fun k hi=> (hp.sub A.contDiff.contDiffAt).of_le (by exact_mod_cast hi.trans (le_max_right 1 _))
  have hA : slopeCap 1 Y 0=0 := by
    unfold slopeCap; rw [norm_iteratedFDeriv_one]; change ‖fderiv ℝ (F-⇑A) _‖=_
    rw [fderiv_sub (hp.differentiableAt (by exact_mod_cast (show max 1 i ≠0 by omega))) A.differentiableAt, A.fderiv]; simp [A]
  have he (j : ℕ) (hi : 1 < j) (hh : j ≤ i) : slopeCap j Y 0≤ M := by
    unfold slopeCap Y; rw [iteratedFDeriv_sub_apply (hp.of_le (by exact_mod_cast hh.trans (le_max_right 1 _))) A.contDiff.contDiffAt]
    apply (norm_sub_le ..).trans; rw [show ‖iteratedFDeriv ℝ j A 0‖=0 from hears A hi _, add_zero]; exact hw _ (by omega)
  have hV : (t • S) 0=0 := by simp [hz]
  have hp' : ContDiffAt ℝ i (t•S) 0 := (contDiffAt_const (c:=t)).smul h
  have hf : W-p=t⁻¹ • (Y∘(t • S)) := by funext s; simp only [W,p,Y, Pi.sub_apply, comp_apply,Pi.smul_apply,smul_sub,A.map_smul,smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
  have ho' : ContDiffAt ℝ i (Y ∘ (t • S)) 0 := (hV ▸ hY i le_rfl : ContDiffAt ℝ i Y _).comp _ hp'
  refine ⟨?_,?_,?_⟩
  · unfold p; rw [guiding A S i 0 h]; apply (A.le_opNorm _).trans; refine mul_le_mul ?_ (le_add_of_nonneg_right hv') (norm_nonneg _) hm
    unfold A; rw [← norm_iteratedFDeriv_one F]; exact hw _ (le_max_left ..)
  · have hc : ContDiffAt ℝ i F ((t • S) 0) := hV ▸ hp.of_le (by exact_mod_cast le_max_right 1 i)
    exact (contDiffAt_const (c:=t⁻¹)).smul (ContDiffAt.comp _ hc hp')
  rw [hf, iteratedDeriv_const_smul ho',norm_smul,Real.norm_of_nonneg (inv_pos.mpr ht).le, ← div_eq_inv_mul, div_le_iff₀ ht,
    iteratedDeriv_vcomp_eq_sum_orderedFinpartition (show ContDiffAt ℝ i Y ((t • S) 0) from hV ▸ hY i le_rfl) hp' le_rfl,hV]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ p : OrderedFinpartition i, M*t^2*R p := by
      apply Finset.sum_le_sum; intro p _
      let v:= p.length; apply (ContinuousMultilinearMap.le_opNorm ..).trans
      by_cases hh : 1 < v
      · rw [mul_assoc]; refine mul_le_mul (he _ hh p.length_le) ?_ (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hm
        have hB j : ‖iteratedDeriv (p.partSize j) (t • S) 0‖ ≤ t* ‖iteratedDeriv (p.partSize j) S 0‖ := by
          rw [iteratedDeriv_const_smul (h.of_le (by exact_mod_cast p.partSize_le j)),norm_smul,Real.norm_of_nonneg ht.le]
        apply le_trans (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hB j))
        rw [Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht.le h₁ hh) (hl p)
      · have hv : slopeCap v Y 0=0 := by rcases show v=0∨v=1 by omega with h|h<;> simp only [h,ho,hA]
        rw [show ‖iteratedFDeriv ℝ p.length Y 0‖=0 from hv, zero_mul]; exact mul_nonneg (mul_nonneg hm (sq_nonneg _)) (hl p)
    _ ≤ _ := by rw [← Finset.mul_sum]; unfold C; nlinarith only [mul_nonneg (mul_nonneg hm hu) (sq_nonneg t)]
end

variable {G : Gauge} {b d n : ℕ} (H : Hol G)

-- Snap ray and Θ origin derivative. Input smoothed via plog and prices.
def flash (A : Snap G d) (r : ℝ) : Snap G d := Drops.trunk d (scaleJet (expand d A) r)
@[simp] lemma flashZ (A : Snap G d) : flash A 0=0 := by funext i; simp only [flash,Drops.trunk,scaleJet]; rw [zero_pow (by omega),zero_smul];rfl
lemma powers {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (i n : ℕ) (v : V) : ContDiff ℝ n (fun x : ℝ => x^i • v) := by fun_prop
lemma flashDiff (A : Snap G d) : ContDiff ℝ (↑n) (flash A) := by
  apply contDiff_pi.mpr; intro i; exact powers _ _ (expand d A i.val)
lemma flash_smul (A : Snap G d) (t r : ℝ) : flash (t • A) r=t • flash A r := by
  funext i; unfold flash Drops.trunk expand scaleJet; simp only [dif_pos i.isLt,Pi.smul_apply]; exact smul_comm ..

def domain (b : ℕ) (x : UsedEdges (box b)) (A : Snap G d) (t : ℝ) := t⁻¹ • (bore H d b x ∘ (t • flash A))
def probeLine (b : ℕ) (x : UsedEdges (box b)) (A : Snap G d) := (fderiv ℝ (bore H d b x) 0) ∘ flash A

lemma exact_turn (A : Snap G d) (m : ℕ) : ∃ C : ℝ, ∃ v : ℕ, 0≤C ∧ ∀ b t, 0 < t → t ≤ 1 → ∀ x : UsedEdges (box b),
    let P:=domain H b x A t
    let Q:=probeLine H b x A
    ContDiffAt ℝ m P 0 ∧ ContDiffAt ℝ m Q 0 ∧ P 0=0 ∧ Q 0=0 ∧ ‖iteratedDeriv m Q 0‖ ≤ C*(1+(b:ℝ))^v ∧ ‖iteratedDeriv m (P-Q) 0‖≤ C*(1+(b:ℝ))^v*t := by
  obtain ⟨C,hC,Hc⟩ := @shore G.Color (Snap G d) _ _ _ Drops.instNormedSpaceRealSnap (flash A) m (flashZ A) (show ContDiffAt ℝ m (flash A) 0 from (flashDiff A).contDiffAt)
  choose c v hc Hv using fun s => shots H d s
  obtain ⟨M,k,hM,Hs⟩ := artillery c v (max 1 m) hc
  refine ⟨M*C,k,mul_nonneg hM hC,fun b t ht h₁ x => ?_⟩
  let P:= bore H d b x; let F:= fderiv ℝ P 0; let s:= (1+(b:ℝ))^k
  have hs : 1≤1+(b:ℝ) := le_add_of_nonneg_right (by positivity)
  have hp : P 0=0 := by simp [P, bore]
  obtain ⟨hh,hA,ht'⟩ := Hc P (M*s) t (mul_nonneg hM (pow_nonneg (zero_le_one.trans hs) _)) hp ht h₁
    (fun i hi=> ((Hv i b x).2).trans (Hs _ hs _ hi)) (Hv (max 1 m) b x).1
  have h : (t • flash A) 0=0 := by simp
  have he : M*s*C=M*C*s := by ring
  rw [he] at hh ht'
  refine ⟨hA,?_,?_,?_ ,hh,ht'⟩
  · exact ContDiff.contDiffAt (F.contDiff.comp (flashDiff A))
  · change t⁻¹ • (P ((t • flash A) 0))=_; rw [h,hp,smul_zero]
  simp [probeLine]

lemma derivativeNorm {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : E →L[ℝ] V) (i : ℕ) (u : ℝ → E) (h : ContDiffAt ℝ i u 0) (hp : ∀ x,‖r x‖≤‖x‖) : slopeCap i (r∘u) 0≤ slopeCap i u 0 := by
  unfold slopeCap; rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,norm_iteratedFDeriv_eq_norm_iteratedDeriv, guiding _ u i 0 h]; exact hp _
lemma scanning (G : Gauge) (i : G.ColorIndex) : ∃ r : G.Color→L[ℝ] ℂ, r=(show G.Color→L[ℝ] ℂ from Complex.ofRealCLM.comp (EuclideanSpace.proj i)) ∧ (∀ x : G.Color,r x=(x i:ℂ)) ∧ ∀ x, ‖r x‖≤‖x‖ := by
  refine ⟨_,rfl,fun x => rfl,fun x => ?_⟩
  rw [ContinuousLinearMap.comp_apply]
  change ‖((x i:ℝ):ℂ)‖ ≤ _
  have hp := real_inner_comm x (EuclideanSpace.basisFun G.ColorIndex ℝ i)
  rw [Complex.norm_real,Real.norm_eq_abs,show x i = inner ℝ ((EuclideanSpace.basisFun G.ColorIndex ℝ) i) x from (EuclideanSpace.basisFun_inner ..).symm]; exact (abs_real_inner_le_norm ..).trans (by rw [OrthonormalBasis.norm_eq_one,one_mul])

lemma speech (A : Snap G d) (m : ℕ) : ∃ C : ℝ, ∃ v : ℕ,1 ≤ C ∧ ∀ b t,0<t → t ≤ 1 → ∀ x : UsedEdges (box b),∀ i : G.ColorIndex,
    let U:=fun p => ((domain H b x A t p i):ℂ)
    let V:=fun p => ((probeLine H b x A p i):ℂ)
    ContDiffAt ℝ m U 0 ∧ ContDiffAt ℝ m V 0 ∧ U 0=0 ∧ V 0=0 ∧ ∀ j,j ≤ m →
      slopeCap j U 0≤ C*(1+(b:ℝ))^v ∧ slopeCap j V 0≤C*(1+(b:ℝ))^v ∧ slopeCap j (U-V) 0 ≤ C*(1+(b:ℝ))^v*t := by
  choose C v hc Hc using fun i=>exact_turn H A i
  obtain ⟨L,p,hL,HU⟩ := artillery C v m hc
  refine ⟨max 1 (L+L),p,le_max_left ..,fun b t ht h₁ x i=>?_⟩
  obtain ⟨Q,u,Z,hs⟩ := scanning G i; obtain ⟨hp,hF,hY,hX,-⟩ := Hc m b t ht h₁ x
  dsimp only; let F:= probeLine H b x A
  let D:= domain H b x A t
  let B:= L*(1+(b:ℝ))^p
  let Y := max 1 (L+L)*(1+(b:ℝ))^p
  have hy : 0 ≤ B := by dsimp only [B]; positivity
  have hv : B+B≤Y := by unfold B Y; rw [← add_mul]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)
  simp_rw [← Z]; change ContDiffAt ℝ m (Q∘D) 0 ∧ ContDiffAt ℝ m (Q∘F) 0 ∧ Q (D 0)=_ ∧ Q (F 0)=_ ∧ _
  change D 0=0 at hY; change F 0=0 at hX
  refine ⟨Q.contDiff.contDiffAt.comp _ hp,Q.contDiff.contDiffAt.comp _ hF,hY ▸ map_zero _,hX ▸ map_zero _,fun j hj=>?_⟩
  obtain ⟨hS,hA,-,-,hw,hD⟩ := Hc j b t ht h₁ x
  let W := D-F
  let q:= C j*(1+(b:ℝ))^(v j)
  have hS' : ContDiffAt ℝ j W 0:=hS.sub hA
  change slopeCap j (Q∘D) 0 ≤ Y ∧ slopeCap j (Q∘F) 0 ≤ Y ∧ slopeCap j ((Q∘D)-(Q∘F)) 0 ≤ Y*t
  have h₁' : slopeCap j F 0≤q := norm_iteratedFDeriv_eq_norm_iteratedDeriv |>.trans_le hw
  have h₂ : slopeCap j W 0≤q*t := norm_iteratedFDeriv_eq_norm_iteratedDeriv |>.trans_le hD
  have he : q ≤ B:=HU _ (by simp) j hj
  have hk := (derivativeNorm Q j _ hS hs).trans (show slopeCap j D 0≤Y from ?_); rotate_left
  · have hh : ‖iteratedDeriv j W 0‖ ≤ B := (hD.trans (mul_le_mul_of_nonneg_right he ht.le)).trans (mul_le_of_le_one_right hy h₁)
    apply norm_iteratedFDeriv_eq_norm_iteratedDeriv.trans_le
    change ‖iteratedDeriv j D 0‖≤ _
    conv_lhs => rw [show D=F+W by unfold W; abel]
    rw [iteratedDeriv_add hA hS']; exact (norm_add_le ..).trans ((add_le_add (hw.trans he) hh).trans hv)
  refine ⟨hk,(derivativeNorm Q j _ hA hs).trans (h₁'.trans (he.trans ((le_add_of_nonneg_right hy).trans hv))),?_⟩
  rw [show (Q∘D)-(Q∘F)=Q∘W from funext fun i=> (map_sub Q _ _).symm]
  exact (derivativeNorm Q j _ hS' hs).trans (h₂.trans (mul_le_mul_of_nonneg_right (he.trans ((le_add_of_nonneg_right hy).trans hv)) ht.le))
end YM.Next.Rank.Spindle
