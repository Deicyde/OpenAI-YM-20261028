import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Words
import YM.Work.H03

/-!
# Uniform budget cost of turning a Coefficient's regular part

Bound in the **actual ordered derivative norm** of RG.BudgetPoint.
No size of stencil or side in the factor, no charge per area/number of
copies, no change of threshold. This is only the regular bound: exponent,
label/support movements, etc. for a full move of a Coefficient still need
proof. Cost stated (not optimal) even for affine translations. May want to
enlarge pre-stage bounds to pay it if moving big charged assemblies. Not
asserting the schedule purchases this or any other gate. Need no price at
all on sizes to apply, just the actual `Regular` and `supBounds`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Lattice Wilson RG Analysis Next.Foundations
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}

/-- On the target links, directions of a single parity only. -/
def oneSign (s : Signed) (b : Site n) (i : Instruction G n) :=
  ∀ e : Edge (Site n), s.flip e.2 ≠ i.1 → i.2 (bonds s b e) = 0

def dispatchBack (s : Signed) (b : Site n) (i : Instruction G n) : Instruction G n :=
  (i.1, fun e => if i.1 then -i.2 (bonds s b e) else i.2 (bonds s b e))

lemma one_glide (s : Signed) (b : Site n) (i : Instruction G n) (h : oneSign s b i)
    (U : Config G n) (t : ℝ) :
    pull s b (increment U (t • i.2)) = glide i.1 (pull s b U) (t • (dispatchBack s b i).2) := by
  funext e; rw [pull_formula]
  unfold glide increment
  split <;> rename_i he
  · rcases i with ⟨p,i⟩; cases p
    · have ht : i (sendEdge s b e) = 0 := h e (by simp [he]); simp [pull_formula,he,dispatchBack,ht]
    simp [pull_formula,he,dispatchBack,exp_opposite]
  rcases i with ⟨p,i⟩; cases p
  · simp [pull_formula,he,dispatchBack]
  have ht : i (sendEdge s b e) = 0 := h e he; simp [pull_formula,he,dispatchBack,ht]

lemma price_glide (s : Signed) (b : Site n) (o : Site n) (e : Edge (Site n)) :
    separation (bonds s b e).1 (affine s b o) ≤ separation e.1 o + 1 := by
  rw [send_formula]; split
  · let x := affine s b e.1
    let q : Site n := step (s.perm e.2)
    calc
      separation (x-q) (affine s b o) ≤ _ := separation_triangle _ x _
      _ ≤ 1+separation e.1 o := by
        have hh : separation (x-q) x ≤ 1 := by
          rw [separation, show x-q-x = -q by abel, pdist_neg]; exact pdist_step _
        unfold x; simp only [affine,separation_translate,separation_signed]; gcongr; exact hh
      _ = _ := Nat.add_comm ..
  simp [affine]

/-- Factor paid per insertion partner. -/
def orientationFee (P : BudgetPoint) : ℝ := (2 * (2:ℝ)^P.power)^P.order
lemma one_le_orientationFee (P : BudgetPoint) : 1 ≤ orientationFee P := by
  have he : 1 ≤ (2:ℝ)^P.power := one_le_pow₀ (by norm_num)
  exact one_le_pow₀ (by linarith)

lemma pricesBack (P : BudgetPoint) (s : Signed) (b o : Site n) (i : Instruction G n)
    (h : P.dirBound (affine s b o) i.2) : P.dirBound o (((2:ℝ)^P.power)⁻¹ • (dispatchBack s b i).2) := by
  let D := fun x y : Site n => 1+(separation x y : ℝ)
  intro e
  let x := (bonds s b e).1
  let y := affine s b o
  have he : D x y ≤ 2*D e.1 o := by
    have ht : separation x y ≤ separation e.1 o + 1 := price_glide ..
    have hh : (separation x y : ℝ) ≤ (separation e.1 o : ℝ) + 1 := by exact_mod_cast ht
    dsimp [D]; linarith [Nat.cast_nonneg (α:=ℝ) (separation e.1 o)]
  have hu : 0 ≤ D x y := by unfold D; positivity
  have hq : ‖(dispatchBack s b i).2 e‖ = ‖i.2 (bonds s b e)‖ := by unfold dispatchBack; split <;> simp
  rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg (by positivity),hq]
  calc
    _ ≤ ((2:ℝ)^P.power)⁻¹ * (P.threshold * D x y ^ P.power) := mul_le_mul_of_nonneg_left
      (h (bonds s b e)) (by positivity)
    _ ≤ ((2:ℝ)^P.power)⁻¹ * (P.threshold * (2 * D e.1 o) ^ P.power) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu he _) P.threshold_pos.le) (by positivity)
    _ = _ := by rw [mul_pow]; unfold D; field_simp

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
    {P : BudgetPoint} {B : Support n} {o b : Site n} {f : Config G n → Y} {c : ℝ}

omit [MeasurableSpace Y] in
lemma identified (s : Signed) (l : program G n) (h : ∀ i∈l, oneSign s b i) :
    leftDerivs (f ∘ pull s b) (l.map Prod.snd) = word (l.map (dispatchBack s b)) f ∘ pull s b := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext U
    simp only [leftDerivs,List.map_cons, ih fun j hj => h j (List.mem_cons_of_mem _ hj),comp_apply,
      one_glide s b i (h i (by simp))]; rfl

private lemma side_member (b : Bool) (l : program G n) {d : Directions G n} (hd : d ∈ partitionSide b l) : (b,d) ∈ l := by
  induction l with
  | nil => simp [partitionSide] at hd
  | cons i l ih =>
    unfold partitionSide at hd; split at hd
    · rename_i he
      obtain hh|hh := List.mem_cons.mp hd
      · rw [he,hh]; exact List.mem_cons_self
      exact List.mem_cons_of_mem _ (ih hh)
    exact List.mem_cons_of_mem _ (ih hd)

private lemma word_bound {U : Config G n} (h : P.supBounds o B f c) (hp : P.Regular B f)
    (hU : Healthy P.threshold B U) (l : program G n) (hk : l.length ≤ P.order)
    (z : ℝ) (hz : 0 < z) (hl : ∀ i∈l, P.dirBound o (z⁻¹ • i.2)) : ‖word l f U‖ ≤ z^l.length * c := by
  have he : HasOrderAt f U l.length := HasOrderAt.fewer hk (hp.smooth U hU)
  let L := (partitionSide true l).reverse.map (leftDir U) ++ partitionSide false l
  let Q : List (Directions G n) := L.map (z⁻¹ • ·)
  have hL : L.length = l.length := by simp [L,side_length]
  have hQ : Q.length = l.length := by simp [Q,hL]
  have hm : Q.map (z • ·) = L := by
    rw [show ((z • ·) : Directions G n → Directions G n) = (fun i => z • i) from rfl]
    unfold Q; simp only [List.map_map]; simp [Function.comp_def,hz.ne']
  have ht : ‖leftDerivs f Q U‖ ≤ c := by
    apply h.2 _ hU Q (hQ ▸ hk)
    intro A ha
    obtain ⟨a,hx,rfl⟩ := List.mem_map.mp ha
    have he (b : Bool) (d : Directions G n) (hd : d ∈ partitionSide b l) : (b,d) ∈ l := side_member b l hd
    obtain hx|hx := List.mem_append.mp hx
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hx
      rw [List.mem_reverse] at hd
      have hi := hl _ (he true d hd)
      intro e; rw [Pi.smul_apply,norm_smul]
      change ‖z⁻¹‖*‖G.adjoint (U e) (d e)‖ ≤ _
      have hi' := hi e; change ‖z⁻¹ • d e‖ ≤ _ at hi'
      rw [norm_smul] at hi'
      rw [G.norm_adjoint]; exact hi'
    exact hl (false,a) (he false a hx)
  rw [word_equation l he]; change ‖leftDerivs f L U‖ ≤ _
  rw [← hm, slot_scale Q z (by rwa [hQ]), norm_smul, hQ,Real.norm_of_nonneg (pow_nonneg hz.le _)]
  exact mul_le_mul_of_nonneg_left ht (pow_nonneg hz.le _)

/-- Keep just one target-link parity. -/
def restrictDir (s : Signed) (b : Site n) (r : Bool) (A : Directions G n) : Instruction G n :=
  (r, fun e => if r = s.flip ((bonds s b).symm e).2 then A e else 0)

lemma pickDir (s : Signed) (b : Site n) (r : Bool) (A : Directions G n) : oneSign s b (restrictDir s b r A) := by
  intro e he
  change s.flip e.2 ≠ r at he
  change (if r=s.flip ((bonds s b).symm _).2 then _ else _) = 0
  rw [Equiv.symm_apply_apply, if_neg (Ne.symm he)]

lemma restrict_bound (s : Signed) (b : Site n) (r : Bool) {A : Directions G n} (h : P.dirBound o A) :
    P.dirBound o (restrictDir s b r A).2 := by
  intro e; simp only [ restrictDir]; split
  · exact h e
  rw [norm_zero]; exact mul_nonneg P.threshold_pos.le (by positivity)

lemma restrict_combine (s : Signed) (b : Site n) (A : Directions G n) :
    (restrictDir s b true A).2 + (restrictDir s b false A).2 = A := by
  funext e
  simp only [Pi.add_apply, restrictDir]; cases s.flip (((bonds s b).symm e).2) <;> simp

omit [MeasurableSpace Y] in
lemma healthy_pull (s : Signed) (b : Site n) (B : Support n) (θ : ℝ) (U : Config G n) :
    Healthy θ B (pull s b U) ↔ Healthy θ (B.image (affine s b)) U := by
  unfold Healthy
  rw [← Work.H03.flags_send s b θ U, Finset.disjoint_image (show Injective (affine s b) from
    fun x y h => s.act_injective (add_right_cancel h))]

omit [MeasurableSpace Y] in
lemma hasOrder_pull (s : Signed) (b : Site n) {k : ℕ} (U : Config G n) (h : HasOrderAt f (pull s b U) k) :
    HasOrderAt (f ∘ pull s b) U k := by
  unfold HasOrderAt
  simp_rw [Function.comp_def,pull_increment]
  let L := (pulledDirection s b U).toContinuousLinearMap
  have he : ContDiffAt ℝ k (fun A => f (increment (pull s b U) A)) (L 0) := by rw [map_zero]; exact h
  exact he.comp 0 L.contDiff.contDiffAt

private lemma multiple (s : Signed) (b : Site n) (h : P.supBounds o B f c) (hp : P.Regular B f)
    (U : Config G n) (hU : Healthy P.threshold (B.image (affine s b)) U)
    (l : List (Directions G n)) (r : program G n) (hk : l.length+r.length ≤ P.order)
    (hl : ∀ i∈l,P.dirBound (affine s b o) i)
    (hr : ∀ i∈r,P.dirBound (affine s b o) i.2 ∧ oneSign s b i) :
    ‖leftDerivs (f ∘ pull s b) (l ++ r.map Prod.snd) U‖ ≤
      (2:ℝ)^l.length * ((2:ℝ)^P.power)^(l.length+r.length) * c := by
  let F := f ∘ pull s b
  have hv : Healthy P.threshold B (pull s b U) := (healthy_pull ..).2 hU
  have ht : HasOrderAt F U P.order := hasOrder_pull s b U (hp.smooth _ hv)
  induction l using List.reverseRecOn generalizing r with
  | nil =>
    let D := r.map (dispatchBack s b)
    simp only [List.length_nil, pow_zero,one_mul,Nat.zero_add,List.nil_append]
    rw [identified s r (fun i hi => (hr i hi).2)]
    have he : D.length = r.length := by simp [D]
    rw [← he]
    apply word_bound h hp hv D (by simpa [he] using hk) _ (by positivity)
    intro i hi; obtain ⟨i0,hi0,rfl⟩ := List.mem_map.mp hi
    exact pricesBack P s b o i0 ((hr i0 hi0).1)
  | append_singleton l i ih =>
    let z := ((2:ℝ)^l.length) * ((2:ℝ)^P.power)^(l.length + r.length + 1) * c
    let Y : Instruction G n := restrictDir s b true i
    let Z : Instruction G n := restrictDir s b false i
    have hi : P.dirBound (affine s b o) i := hl _ (by simp)
    have he (Q : Instruction G n) (hQ : P.dirBound (affine s b o) Q.2 ∧ oneSign s b Q) :
        ‖leftDerivs F (l ++ (Q.2 :: r.map Prod.snd)) U‖ ≤ z := by
      have hs : l.length+(Q::r).length = (l++[i]).length+r.length := by simp; omega
      have hb := ih (Q::r) (hs.symm ▸ hk) (fun i hi => hl i (by simp [hi])) (by
        intro a ha; obtain ha|ha := List.mem_cons.mp ha
        · exact ha.symm ▸ hQ
        exact hr a ha)
      simpa only [z, List.length_cons,Nat.add_assoc,List.map_cons] using hb
    have hy := he Y ⟨restrict_bound s b true hi,pickDir s b true i⟩
    have hz := he Z ⟨restrict_bound s b false hi,pickDir s b false i⟩
    have hs : HasOrderAt F U (l.length+(r.map Prod.snd).length+1) := ht.fewer (by simp at *; omega)
    have hx := slot_add l (r.map Prod.snd) Y.2 Z.2 hs
    rw [show Y.2+Z.2=i from restrict_combine s b i] at hx
    rw [List.append_assoc]
    change ‖leftDerivs F (l ++ (i :: r.map Prod.snd)) U‖ ≤ _
    rw [hx]
    apply ((norm_add_le ..).trans (add_le_add hy hz)).trans_eq
    have he : (l++[i]).length+r.length = l.length+r.length+1 := by simp; omega
    unfold z; rw [he]; simp only [List.length_append,List.length_singleton,pow_succ]; ring

/-- Cost on the new support at the affine-moved origin. -/
theorem turn_supBounds (s : Signed) (b : Site n) (h : P.supBounds o B f c) (hp : P.Regular B f) :
    P.supBounds (affine s b o) (B.image (affine s b)) (f ∘ pull s b) (orientationFee P * c) := by
  have he : 0 ≤ orientationFee P := zero_le_one.trans (one_le_orientationFee _)
  refine ⟨mul_nonneg he h.1, fun U hu l hk hl => ?_⟩
  have ht := multiple s b h hp U hu l [] (by simpa) hl (by simp)
  unfold orientationFee; simp only [List.map_nil,List.append_nil,List.length_nil,Nat.add_zero,← mul_pow] at ht
  have hb : 1 ≤ (2:ℝ)^P.power := one_le_pow₀ (by norm_num)
  exact ht.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hk) h.1)
/-- Optional tighter price -- use e.g. for moving anchors without
purchasing higher constants at every step. -/
def permission (P : BudgetPoint) (s : Signed) :=
  if ∀ i : Axis, s.flip i = false then (1:ℝ) else orientationFee P

lemma one_permission (P : BudgetPoint) (s : Signed) : 1 ≤ permission P s := by
  unfold permission; split
  · exact le_rfl
  exact one_le_orientationFee _



lemma paid_permission (s : Signed) (b : Site n) (h : P.supBounds o B f c) (hp : P.Regular B f) :
    P.supBounds (affine s b o) (B.image (affine s b)) (f ∘ pull s b) (permission P s * c) := by
  unfold permission; split
  · rename_i hh
    rw [one_mul]
    refine ⟨h.1, fun U hu l hk hl => ?_⟩
    let r : program G n := dispatch false l
    let T := r.map (dispatchBack s b)
    have hs : T.length = l.length := by simp [T,r,dispatch]
    have he : ∀ i ∈ r, oneSign s b i := by
      intro i hi; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hi
      intro e hy; exact False.elim (hy (hh _))
    have ht : leftDerivs (f ∘ pull s b) l U = word T f (pull s b U) := by
      have H : r.map Prod.snd = l := by simp [r,dispatch]
      nth_rw 1 [← H]; exact congr_fun (identified s r he) U
    have hp' := word_bound h hp ((healthy_pull ..).2 hu) T (hs.symm ▸ hk) 1 one_pos
    rw [ht]
    apply le_trans (hp' ?_) (by simp)
    intro i hi; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hj
    rw [inv_one,one_smul]
    intro e
    have hm := hl x hx (bonds s b e)
    rw [send_formula, hh] at hm
    simpa only [dispatchBack, Bool.false_eq_true, ↓reduceIte, send_formula, hh, affine,
      separation_translate,separation_signed] using hm
  exact turn_supBounds _ _ h hp
end YM.ProjectorNext.Equivariance
