import YM.Pert.Rigid.Spin
/-!
Test all one-point functions and two-point functions along a single coordinate separation to fix remaining four-horizon basis variation. No contact equations imposed.
-/
set_option autoImplicit false
set_option maxHeartbeats 850000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Rigid
open Function Filter Maxwell Position UVNext.FreeStress Labels Work.A01 Next.UVStress
open scoped Topology BigOperators
variable {G : Gauge} (F : Frames G)
local notation "S" => E F 4
/-- common order of primary and companion fields at separation along axis zero. -/
def batch (v w : S) : Fin 2→S := Fin.cons v (fun _ : Fin 1 => w)
def joint (v w : S) : ℂ:= visible F 4 (camera 0) (batch F v w)
def second (v : S) : S→ₗ[ℂ] ℂ := (visible F 4 (camera 0)).toLinearMap (batch F v 0) 1
@[simp] theorem batch_zero (v w : S) : batch F v w 0=v := rfl
@[simp] theorem batch_end (v w : S) : batch F v w 1=w := rfl
lemma second_eq (v w : S) : second F v w = joint F v w := by
  unfold second joint; simpa only [MultilinearMap.toLinearMap_apply] using (congrArg (visible F 4 (camera 0)) (show Function.update (batch F v 0) 1 w = batch F v w from funext fun i=> by fin_cases i <;> simp only [Function.update_self,batch_end,batch_zero] <;> first | rfl | exact Function.update_noteq (by decide) _ _))
lemma negative_eq (c : Face) (v : S) : joint F v (star F (some c))= negative F 0 c.val.1 c.val.2 v := by
  rw [negative,listens]
  change (freeTable F).useAt (freeTable F) (camera 0) (fun j => (⟨4,(batch F v _ j)⟩ : (freeTable F).Tag)) = _
  congr 1
  funext i
  fin_cases i <;> exact rfl

def gaugeWeight (c : Face) : ℂ := ((G.lieDim:ℂ) * (coat 0 c.val.1 : ℂ) * (coat 0 c.val.2 : ℂ))
lemma big_weight (h : G.Simple) (c : Face) : gaugeWeight (G:=G) c ≠ 0 := by
  have hl : 0<G.lieDim := by
    rw [Gauge.lieDim,← G.colorIso.finrank_eq]
    haveI := h.nontrivial_color
    exact Module.finrank_pos
  have h1 : ∀ p : Plane, (coat 0 p : ℂ)≠0 := fun p=>by exact_mod_cast coat_ne 0 p
  unfold gaugeWeight; exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hl.ne') (h1 _)) (h1 _)
def rate (c : Face) := (modulator c *(gaugeWeight (G:=G) c)⁻¹)⁻¹
lemma modulator_ne (c) : modulator c ≠ 0 := by unfold modulator; split <;> norm_num
lemma rate_ne (h : G.Simple) (c : Face) : rate (G:=G) c ≠ 0 := by unfold rate; exact inv_ne_zero (mul_ne_zero (modulator_ne _) (inv_ne_zero (big_weight h _)))
lemma mask_scale (c : Face) : gaugeWeight (G:=G) c = (↑G.lieDim:ℂ) * (4*(normal:ℝ))^2 * flavor 0 (tape c) := by
  have hw (p : Plane) : coat 0 p = (badge 0 p.val)*(4*normal) := by simp only [badge,pop, coat]; split_ifs <;> simp at * <;> grind
  have he : (↑(badge 0 (tape c).1 * badge 0 (tape c).2) : ℂ) = flavor 0 (tape c) := by unfold badge flavor paint; cases pop (tape c).1 0 <;> cases pop (tape c).2 0 <;> norm_num
  rw [gaugeWeight,hw,hw,Complex.ofReal_mul,Complex.ofReal_mul,←he, Complex.ofReal_mul]; dsimp only [tape]; push_cast; ring
lemma common_mod {c e : Face} (h : camp c=camp e) : modulator c=modulator e := by
  unfold modulator; have hc : (tape c).1=(tape c).2 ↔ c.val.1=c.val.2 := by simp [tape,←Subtype.ext_iff]
  have he : (tape e).1=(tape e).2 ↔ e.val.1=e.val.2 := by simp [tape,←Subtype.ext_iff]
  unfold camp at h; split_ifs with h1 h2 <;> first | rfl | exfalso; simp_all
lemma common_rate {c e : Face} (h : paint (tape c)=paint (tape e)) : rate (G:=G) c=rate (G:=G) e := by
  rw [rate,common_mod (((havePath c e h).2)),mask_scale, show flavor 0 (tape c)=flavor 0 (tape e) from by rw [flavor,h,flavor], ←mask_scale,←rate]
lemma price_tag (h : G.Simple) (v : S) (c : Face) : joint F v (star F (some c)) = rate (G:=G) c * portLine F (some c) v := by
  have he : portLine F (some c) v = (modulator c *(gaugeWeight (G:=G) c)⁻¹) * (joint F v (star F (some c))) := by rw [negative_eq, portLine, reader]; dsimp only [gaugeWeight,LinearMap.smul_apply,smul_eq_mul]; simp only [mul_assoc]
  rw [he, rate,←mul_assoc, inv_mul_cancel₀ (mul_ne_zero (modulator_ne _) (inv_ne_zero (big_weight h _))), one_mul]

lemma portValue (h : G.Simple) (v : S) (e : Option Face) : portLine F e v = (stand F h).equivFun v e := by
  classical
  conv_lhs=>rw [←(stand F h).sum_equivFun v]
  simp_rw [map_sum,basis_eq,map_smul,separates F h]
  simp
lemma backwards (h : G.Simple) (v : S) (hv0 : portLine F none v=0) (c : Face) :joint F (star F (some c)) v = rate (G:=G) c * portLine F (some c) v := by
  classical
  rw [portValue F h] at hv0 ⊢
  rw [←second_eq]
  conv_lhs => rw [←(stand F h).sum_equivFun v]
  rw [map_sum];simp_rw [map_smul,basis_eq,second_eq]
  rw [Finset.sum_eq_single_of_mem (some c) (Finset.mem_univ _) (fun b _ hbc=>?_)]
  · rw [price_tag F h, separates F h,if_pos rfl,smul_eq_mul,mul_one,mul_comm]
  cases b with
  | none=> rw [hv0,zero_smul]
  | some k=> rw [price_tag F h, separates F h, if_neg hbc,mul_zero, smul_zero]

def stationery (B : Buffer F 4) :=
    ∀ r (p : Fin r→S) x, x∈ YM.conf r → ∑ j:Fin r, visible F 4 x (Function.update p j (B.val (p j)))=0
lemma alone (B : Buffer F 4) (h : stationery F B) (v : S) : portLine F none (B.val v) = 0 := by
  change expectation (freeTable F) 4 (B.val v)=0
  let p : Fin 1→S := fun _=>v
  have h' := h 1 p 0 conf1
  rw [Fin.sum_univ_succ, Fin.sum_univ_zero,add_zero] at h'
  rw [expectation,front_eval]
  change (freeTable F).useAt (freeTable F) _ _=0
  change (freeTable F).useAt (freeTable F) 0 (fun j=> (⟨4,Function.update p 0 _ j⟩:(freeTable F).Tag))=0 at h'
  rw [←h']; congr 1; funext i; rw [@Subsingleton.elim (Fin 1) _ i 0]; rfl
lemma cancel (B : Buffer F 4) (h : stationery F B) (v w : S) : joint F (B.val v) w + joint F v (B.val w) = 0 := by
  classical
  have he := h 2 (batch F v w) _ (shutter 0)
  rw [Fin.sum_univ_two] at he
  unfold joint
  rw [←he]
  congr 2 <;> try rfl
  all_goals ext1 i;fin_cases i <;> simp
lemma coeff_barren (hg : G.Simple) (B : Buffer F 4) (h : stationery F B) (c d : Option Face) : coeff F B c d=0 := by
  cases c with
  | none=> exact alone F B h _
  | some c=>
    cases d with
    | none=> change portLine F _ (B.val (embed F 4 (Labels.unit G 4)))=0; rw [pin_unit F 4,B.property.1,map_zero]
    | some d=>
      rcases eq_or_ne (paint (tape c)) (paint (tape d)) with hx|hx
      · have hr := common_rate (G:=G) hx
        have he := reflect_path F hg hx B
        have hcan := cancel F B h (star F (some c)) (star F (some d))
        rw [price_tag F hg,backwards F hg _ (alone F B h _),←hr] at hcan
        change rate (G:=G) c * coeff F B _ _ + rate (G:=G) c * coeff F B _ _ =0 at hcan
        rw [he,←two_mul,←mul_assoc] at hcan
        exact (mul_eq_zero.mp hcan).resolve_left (mul_ne_zero (by norm_num) (rate_ne hg c))
      exact unpaint F hg hx B

lemma frozen_four (hg : G.Simple) : Frozen F 4 := by
  intro B (h : stationery F B)
  have hz (c) : B.val (star F c)=0 := by rw [←(stand F hg).sum_equivFun (B.val _), Finset.sum_eq_zero]; intro i _; rw [←portValue F hg,basis_eq, ←coeff, coeff_barren F hg B h, zero_smul]
  ext1; ext1 v
  change B.val v=0
  rw [←(stand F hg).sum_equivFun v,map_sum]
  simp only [dispatch_cmul,basis_eq,hz, smul_zero,Finset.sum_const_zero]
lemma first_frozen (hg : G.Simple) {d : ℕ} (hw : d<4) : Frozen F d := fun b _=> Subtype.ext (ContinuousLinearMap.ext fun p=> by
  change b.val p=0
  obtain ⟨z,rfl⟩ := below F hg hw p
  rw [dispatch_cmul,b.property.1,smul_zero])
end YM.Pert.Rigid
