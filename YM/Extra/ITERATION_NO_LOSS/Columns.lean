import YM.Extra.ITERATION_NO_LOSS.Patterns
import YM.Work.F08.Mixed


/-!
# Curvature column and its ordinary first differences in the residue convention

From Towers.T and the two **diagonal** metrics (E H, not H tilde).
Use `Deep` spatial differences, never pay volume at fixed row. Extra
harmonic input on T alone for the loop handoff (would follow e.g. from
alias estimates of the intended universal T).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration
open Lattice Wilson RG Exterior Precision Bloch Laurent Matrix Function Finset Work.F08
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {L c f n : Side} {α β : Type*} [Fintype β]

lemma carry_bound (r : Site L) (y : Cover) :
    (Laurent.size (carry r y) : ℝ) ≤ Laurent.size y / (L.val:ℝ) + 4 := by
  let z := carry r y
  let t := arrives r y
  have ht (i : Axis) : L.val * (z i).natAbs ≤ (y i).natAbs + L.val := by
    have he := congr_fun (carry_spec r y) i
    have hc := lift_centers r i; have hd := lift_centers t i
    change lift r i + y i = lift t i + L.val • z i at he
    have hh : |lift r i - lift t i| ≤ (L.val : ℤ) := by rw [abs_sub_le_iff]; omega
    rw [nsmul_eq_mul] at he
    have hl : ((L.val : ℤ) * z i).natAbs ≤ (y i).natAbs + L.val := by
      rw [show (L.val : ℤ)*z i = y i + (lift r i - lift t i) by omega]
      apply (Int.natAbs_add_le ..).trans; omega
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using hl
  have he := sum_le_sum (fun i (_:i∈univ) => ht i)
  rw [← mul_sum, sum_add_distrib,sum_const,card_univ, nsmul_eq_mul] at he
  change L.val * Laurent.size z ≤ Laurent.size y + 4*L.val at he
  calc
    _ ≤ ((Laurent.size y:ℝ)+4*L.val)/(L.val:ℝ) := (le_div_iff₀ (side_pos L)).2 (by
      rw [mul_comm]; exact_mod_cast he)
    _ = _ := by field_simp

lemma output_row (R : Row α β) (u : Co n β → ℝ) (h : R.safe) (b x) :
    (R.acts n *ᵥ u) (x,b) = ∑ j, ∑' z, R b j z * u (x+wrap n z,j) := by
  rw [mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_comm]
  exact sum_congr rfl fun j _ => sift_action ((h b j).of_norm) n x _

lemma output_cross (g : Ratio c f) (R : Cross g.count α β) (u : Co c β → ℝ) (h : R.safe) (b x) :
    (installed g R *ᵥ u) (x,b) = ∑ j, ∑' z, R (g.residue x,b) j z * u (g.parent x+wrap c z,j) := by
  simpa only [installed, mulVec, dotProduct, submatrix_apply, split_co, id_eq] using output_row R u h (g.residue x,b) (g.parent x)

lemma sums_mul_shift {α β : Type*} {R : Row α β} (hr : R.safe) {b : β} (u : Co n β → ℝ) (r x) :
    Summable (fun z => R r b z * u (x+wrap n z,b)) := by
  have he (z : Site n) : |u (z,b)| ≤ ∑ v : Site n, |u (v,b)| := single_le_sum (f:=fun i => |u (i,b)|) (fun _ _ => abs_nonneg _) (mem_univ z)
  exact Summable.of_norm_bounded ((hr r b).mul_right _) fun i => (norm_mul _ _).trans_le
    (mul_le_mul_of_nonneg_left (he _) (norm_nonneg _))

def moving (R : Cross L α β) (a : Option Axis) := a.elim R (forwardC L R)
omit [Fintype β] in
lemma crossing_add (g : Ratio c f) (x : Site f) (d : Axis) (hg : Odd g.count.val) :
    let Δ : Cover := if lift (g.residue x) d=↑(g.count.val/2 : ℕ) then step d else 0
    g.parent (x + step d) = g.parent x + wrap c Δ ∧
      g.residue (x+step d) = g.residue x + step d := by
  intro Δ
  rw [g.parents_hop hg,map_add, show g.residue (step d) = step d from ?_]
  · dsimp [Δ]; split <;> simp
  rw [← wrap_step f, Ratio.residue_wrap,wrap_step]

lemma forward_act (g : Ratio c f) (a : Option Axis) (R : Cross g.count α β) (u : Co c β → ℝ)
    (hr : R.safe) (hs : (moving R a).safe) (hg : Odd g.count.val) (x : Site f) (b : α) :
    (installed g (moving R a) *ᵥ u) (x,b) = Iteration.read a (fun z => (installed g R *ᵥ u) (z,b)) x := by
  cases a with
  | none => rfl
  | some d =>
    let r := g.residue x
    let Δ : Cover := if lift r d=↑(g.count.val/2 : ℕ) then step d else 0
    obtain ⟨hp,hq⟩ := crossing_add g x d hg
    change g.parent (x+step d) = _ + wrap c Δ at hp
    change _ = (installed g R *ᵥ u) (x+step d,b) - (installed g R *ᵥ u) (x,b)
    rw [output_cross _ _ _ hs,output_cross _ _ _ hr,output_cross _ _ _ hr,hp,hq,← sum_sub_distrib]; apply sum_congr rfl; intro j _
    let F (y : Cover) := R (r+step d,b) j y * u (g.parent x+wrap c Δ+wrap c y,j)
    have H (y : Cover) : F (y-Δ) = R (r+step d,b) j (y-Δ)*u (g.parent x+wrap c y,j) := by
      unfold F; congr 2; rw [map_sub]; abel_nf
    have he (y) : moving R (some d) (g.residue x,b) j y = R (r+step d,b) j (y-Δ)-R (r,b) j y := rfl
    simp_rw [he,sub_mul,← H]
    have hF : Summable F := sums_mul_shift hr u _ _
    have hv : Summable (fun y => F (y-Δ)) := by simpa [comp_def,sub_eq_add_neg] using ((Equiv.addRight (-Δ)).summable_iff (f:=F)).2 hF
    rw [hv.tsum_sub (sums_mul_shift hr ..)]; congr 1
    simpa [sub_eq_add_neg,F] using ((Equiv.addRight (-Δ)).tsum_eq F)

lemma read_row (P : Row α β) (a : Option Axis) (u : Co n β → ℝ) (hp : P.safe) (x b) :
    (P.acts n *ᵥ (fun v : Co n β => Iteration.read a (fun z : Site n => u (z,v.2)) v.1)) (x,b) =
    Iteration.read a (fun z : Site n => (P.acts n *ᵥ u) (z,b)) x := by
  cases a with
  | none => rfl
  | some d =>
    change _ = (P.acts n *ᵥ u) (x+step d,b) - (P.acts n *ᵥ u) (x,b)
    rw [output_row P _ hp,output_row P u hp,output_row P u hp,← sum_sub_distrib]; apply sum_congr rfl; intro j _
    simp only [Iteration.read,Option.elim,grad, mul_sub,add_right_comm x]
    exact (sums_mul_shift hp u b _).tsum_sub (sums_mul_shift hp u b x)

/-- Fine gradient columns need not be differential quotients. -/
def psi (P Q : Bed) (T : Towers L) (a : Option Axis) : Cross L (TypeFace 2) (TypeFace 2) :=
    composeRows (fineCompose P.dual_diag (moving T.T a)) Q.diagonal

def psiPrice (Ω Ω' : ℝ) :=
    (Fintype.card (TypeFace 2):ℝ) * (((Fintype.card (TypeFace 2):ℝ)*(Ω*Ω))*Ω')

def raised (a : Option Axis) : ℕ := a.elim 0 (fun _ => 1)

/-- A precise extra assumption about the unmodified linear-data column at
harmonic input. Swapping channels at nonzero field is not part of this. -/
def Harmonic (T : Towers L) := ∀ (r s : Site L) (b c : TypeFace 2),
    (∑' z, T.T (r,b) c z) = ∑' z, T.T (s,b) c z

def Cancels (ψ : Option Axis → Cross L (TypeFace 2) (TypeFace 2)) := ∀ i r b,
    HasSum (fun z => ψ (some i) r b z) 0

section curvature
variable {P Q : Bed} {η Ω Ω' : ℝ} (hη : 0 < η) (hp : P.dual_diag.strip η Ω) (hq : Q.diagonal.strip η Ω')
    {K : ℕ} {T : Towers L} (hk : 1 ≤ K) (ht : T.Deep η Ω K)

include hk ht in
private lemma moving_strip (a : Option Axis) :
    (moving T.T a).strip η (Ω/(L.val:ℝ)^(2+raised a)) := by
  cases a with
  | none => exact (ht.2.2.2 [] (Nat.zero_le _)).2
  | some d => exact (ht.2.2.2 [d] hk).2
include hη hp hq ht hk
lemma psi_strip (a : Option Axis) : (psi P Q T a).strip η (psiPrice Ω Ω' / (L.val:ℝ)^(2+raised a)) := by
  unfold psi
  convert strip_compose hη.le (strip_fine hη.le hp (moving_strip hk ht a)) hq using 1
  unfold psiPrice; ring

variable {c f : Side} (exactSize : f.val = c.val * L.val)
local notation "g" => (Ratio.mk (c:=c) (f:=f) L exactSize)
include exactSize
lemma psi_matrix (a : Option Axis) : installed g (psi P Q T a) =
    (P.dual_diag.acts f * installed g (moving T.T a)) * Q.diagonal.acts c := by
  unfold psi
  rw [installed_compose g hη.le (strip_fine hη.le hp (moving_strip hk ht a)) hq,
      installed_fine g hη.le hp (moving_strip hk ht a)]
lemma psi_read (hg : Odd L.val) (a : Option Axis) (v : Co c (TypeFace 2) → ℝ) (x b) :
    (installed g (psi P Q T a) *ᵥ v) (x,b) = Iteration.read a (fun z => (installed g (psi P Q T none) *ᵥ v) (z,b)) x := by
  simp_rw [psi_matrix hη hp hq hk ht exactSize, ← mulVec_mulVec]
  let u := Q.diagonal.acts c *ᵥ v
  have hr := fun a => Row.rights _ _ (moving_strip hk ht a) hη.le
  change (P.dual_diag.acts f *ᵥ (installed g (moving T.T a) *ᵥ u)) (x,b) = _
  rw [show installed g (moving T.T a) *ᵥ u = fun w => Iteration.read a (fun z => (installed g T.T *ᵥ u) (z,w.2)) w.1 from
    funext (fun w => forward_act g a T.T u (hr none) (hr a) hg w.1 w.2)]
  exact read_row _ a _ (Row.rights _ _ hp hη.le) x b

lemma psi_curl (hi : P.diagonal.acts f * P.dual_diag.acts f = 1)
    (hd : installed g T.T * Q.diagonal.acts c * d 1 c = P.diagonal.acts f * d 1 f * installed g T.A0) :
    installed g (psi P Q T none) * d 1 c = d 1 f * installed g T.A0 := by
  have he := congr_arg (P.dual_diag.acts f * ·) hd
  simpa only [psi_matrix hη hp hq hk ht exactSize, moving,Option.elim,← Matrix.mul_assoc,
    mul_eq_one_comm.mp hi, Matrix.one_mul] using he
omit exactSize
include ht hk hη hp hq
lemma psi_cancels (hg : Odd L.val) (hT : Harmonic T) : Cancels (psi P Q T) := by
  classical
  letI : Subsingleton (Site (1:Side)) := by change Subsingleton (Axis → ZMod 1); infer_instance
  have he : L.val = (1:Side).val * L.val := (one_mul _).symm
  let G0 := Ratio.mk (f:=L) (c:=1) L he
  rintro d ⟨r,b⟩ j
  let v : Co (1:Side) (TypeFace 2) → ℝ := fun x => if x.2=j then 1 else 0
  let u := Q.diagonal.acts (1:Side) *ᵥ v
  let x := G0.assemble (0,r)
  have hp' := psi_strip hη hp hq hk ht (some d)
  have h := (psi_read hη hp hq hk ht he hg (some d) v x b).symm
  change grad d (fun z => (installed G0 (psi P Q T none) *ᵥ v) (z,b)) x = (installed G0 (psi P Q T (some d)) *ᵥ v) (x,b) at h
  have hs : T.T.safe := Row.rights η _ (moving_strip hk ht none) hη.le
  have hc (z y : Site L) (p : TypeFace 2) : (installed G0 T.T *ᵥ u) (z,p)=(installed G0 T.T *ᵥ u) (y,p) := by
    rw [output_cross G0 T.T u hs,output_cross G0 T.T u hs]; apply sum_congr rfl; intro e _
    have he (x : Site L) (s : Cover) : G0.parent x + wrap _ s = 0 := Subsingleton.elim (α:=Site (1:Side)) ..
    simp_rw [he,tsum_mul_right]; rw [hT _ (G0.residue y)]
  have hx (z : Site L) : (installed G0 (psi P Q T none) *ᵥ v) (z,b) = (P.dual_diag.acts L *ᵥ (installed G0 T.T *ᵥ u)) (x,b) := by
    rw [psi_matrix hη hp hq hk ht he, ← mulVec_mulVec, ← mulVec_mulVec]
    have h' := Row.rights _ _ hp hη.le
    rw [output_row _ _ h',output_row _ _ h']; apply sum_congr rfl; intro k _
    exact tsum_congr fun z' => congr_arg (_ * ·) (hc _ _ _)
  dsimp only [grad] at h; simp only [hx,sub_self, output_cross G0 _ _ (Row.rights _ _ hp' hη.le), x,Ratio.assemble_res,
    v,mul_ite,mul_one,mul_zero] at h
  convert! ((hp' (r,b) j).summable hη.le).hasSum using 1
  have he (k : TypeFace 2) : (fun z => if k = j then psi P Q T (some d) (r,b) k z else 0) =
      (if k = j then psi P Q T (some d) (r,b) j else fun _ : Cover => (0:ℝ)) := by by_cases e : k=j <;> simp [e]
  simp_rw [he] at h
  simpa only [apply_ite (fun p : Cover → ℝ => ∑' i, p i), tsum_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] using h
end curvature
end YM.Extra.Iteration
