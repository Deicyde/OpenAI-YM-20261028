import YM.Extra.FREE_DETECTOR_ALGEBRA.Aim
import YM.Extra.FREE_DETECTOR_ALGEBRA.Incidence
import YM.Extra.FREE_DETECTOR_ALGEBRA.RanksTwo

set_option warningAsError false

/-! Quadratic insertion that reads out weights by radial/Laurent
probe. Defined with BOTH tensor indices transformed by the real
reflection normal to the separation. Here are its tensors/coefficient
identities. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD.OPE
open Function Filter Set Tensor Analysis Maxwell Wick Pair Labels SphereTest Residue
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

variable {G : Gauge} {j k d n : ℕ} {x y : E4}
local notation "W" => Sol G.Color

def whole (G : Gauge) (x : E4) : WickPol G := ∑ i : Fin (legDim G 0), digit (rCoeff (token 0 i)) * digit (solAct (face x) (frame G 0 i))

abbrev gem (P Q : Sol G.Color j) := dotF P.val Q.val
lemma reflected_gem (v : E4) (P Q : W j) : gem (solAct (face v) P) Q=gem P (solAct (face v) Q) := by
  have ht := carry_dot (face v) P.val (solAct (face v) Q).val
  change gem (solAct (face v) P) (solAct (face v) (solAct (face v) Q))=gem P (solAct (face v) Q) at ht
  have he : face v * face v=1 := by nth_rw 1 [← face_inv v]; exact inv_mul_cancel ..
  rwa [← solAct_mul,he,solAct_id] at ht

lemma resolves (P Q : Sol G.Color j) : ∑ i : Fin (legDim G j), gem (rCoeff (token j i)) P * gem (frame G j i) Q = gem P Q := by
  have h := congr_arg (fun P : Sol G.Color j => solProd G.Color j P Q) ((frame G j).sum_repr P)
  rw [map_sum,LinearMap.sum_apply] at h; refine Eq.trans ?_ h
  apply Finset.sum_congr rfl; intro i _
  rw [map_smul,LinearMap.smul_apply]
  have hh : gem (rCoeff (token j i)) P = (frame G j).repr P i := by
    change (dualSol G.Color j (rCoeff (token j i))) P = _; rw [rCoeff,LinearEquiv.apply_symm_apply]; rfl
  rw [hh]; rfl






-- Point on a tensor field, deposited at leg order zero.
def visit (p : W j) (v : E4) : Sol G.Color 0 := ⟨WaveOn.nth p.field 0 v, p.wave.jets isOpen_univ (mem_univ v)⟩

lemma visit_eval (p : W j) (v x : E4) (a b : Axis) : (visit p v).field a b x=p.field a b v := coeff_apply_zero ..

lemma gem0 (P Q : W 0) : gem P Q=∑ a : Axis, ∑ b : Axis, ⟪P.field a b 0,Q.field a b 0⟫ := by
  simp only [gem,dotF_eval,dotDir_eval]
  have he (q : W 0) (a b : Axis) (v : Dirs 0) : q.val a b (dir v)=q.field a b 0 := congr_arg (q.val a b) (Subsingleton.elim ..)
  simp_rw [he]; simp

lemma ether_aim (P : W j) (i : Slot G) (he : x∈away) (hf : y = -x) (hp : y∈away) :
    ether P i x = (gem P (aim (G:=G) (rCoeff i) j hp):ℂ) := by
  subst y
  have ht := exchange (G:=G) (dualSol _ _ P) (dualSol _ _ (rCoeff i)) he
  unfold ether
  rw [show coordinateLeg i = dualSol G.Color _ (rCoeff i) from (LinearEquiv.apply_symm_apply ..).symm]
  exact congr_arg Complex.ofReal (ht.trans (aim_read (rCoeff i) P hp).symm)

lemma field_aim (p : W j) (he : x∈away) (a b : Axis) :
    (aim (G:=G) p 0 he).field a b 0=reply (G:=G) p a b x := by
  change (-1:ℝ)^0 • coeff (reply (G:=G) p a b) 0 x _ = _; rw [pow_zero,one_smul, coeff_apply_zero]

lemma ether_reply (P : W 0) (i : Slot G) (he : x∈away) (hf : y = -x) (hp : y∈away) :
    ether P i x = ((∑ a : Axis, ∑ b : Axis, ⟪P.field a b 0, reply (G:=G) (rCoeff i) a b y⟫) : ℂ) := by
  rw [ether_aim P i he hf hp,gem0]
  simp_rw [field_aim,Complex.ofReal_sum]

def flare (j : ℕ) : ℝ := strength j * (-1)^j
lemma opposite (x : E4) : face (-x)=face x := by
  apply Subtype.ext; ext i j; simp [face,faceM,rr]

lemma reply_point (p : Sol G.Color j) (hv : x∈unitSet) : aim (G:=G) p 0 (show -x∈away from neg_ne_zero.mpr (nonzero_unit hv)) =
    flare j • solAct (face x) (visit p x) := by
  have hp : -x∈unitSet := by simpa using hv
  have he := reply_radial p (x:=-x) (nonzero_unit hp)
  rw [opposite,show inversePoint (-x) = - x by unfold inversePoint; rw [uq hp,one_smul],uq hp,one_pow,mul_one] at he
  have hh (p : W j) : (fun a b : Axis => p.field a b (-x))=(-1:ℝ)^j • fun a b => p.field a b x := by
    ext1 i; ext1 b; change diagonal (p.val i b) (-x)= _; rw [← neg_one_smul ℝ x, homogeneous]; rfl
  rw [hh,_root_.map_smul] at he
  apply Subtype.ext; ext1 a; ext1 b; ext1 w
  rw [show w= fun _ => (0:E4) from Subsingleton.elim ..]
  change (aim (G:=G) p 0 _).field a b 0=flare j • (solO (face x) (visit p x)).field a b 0
  rw [field_solO, reel, funext (fun i => funext (fun b => visit_eval p x (mov (face x)⁻¹ 0) i b)),field_aim]; unfold flare; rw [mul_smul]
  exact congr_fun (congr_fun he a) b

lemma at_edge (P : W 0) (i : Slot G) (hv : x∈unitSet) : ether P i x=
    (↑(flare i.1 * gem P (solAct (face x) (visit (rCoeff i) x))):ℂ) := by
  rw [ether_aim P i (nonzero_unit hv) rfl (neg_ne_zero.mpr (nonzero_unit hv)), reply_point (rCoeff i) hv]
  congr 1; exact map_smul (dotF P.val) _ _

-- other contraction Taylor along the line at an exterior point
lemma gradePath (P : W 0) (i : Slot G) (k : ℕ) (he : x≠y) (v : E4) :
    grade (fun t : ℝ => ether P i (x+t • v-y)) k =
      (↑(gem P (visit (aim (G:=G) (rCoeff i) k (show y-x∈away from sub_ne_zero.mpr he.symm)) v)):ℂ) := by
  let z := y-x; let hp : z∈away := sub_ne_zero.mpr he.symm
  let u := -v
  let f (a b : Axis) := reply (G:=G) (rCoeff i) a b
  let L (a b : Axis) := Complex.ofRealCLM.comp (innerSL ℝ (P.field a b 0))
  let g (x : E4) : ℂ := ∑ a : Axis, ∑ b : Axis, L a b (f a b x)
  have hC : ∀ a b, ContDiffAt ℝ (↑k) (f a b) z := fun a b => ((replied (rCoeff i)).smooth a b z hp).of_le (WithTop.coe_le_coe.mpr le_top)
  have hL a b : ContDiffAt ℝ (↑k) (fun x => L a b (f a b x)) z := (L a b).contDiff.contDiffAt.comp z (hC a b)
  have hF a : ContDiffAt ℝ (↑k) (fun x => ∑ b : Axis, L a b (f a b x)) z := ContDiffAt.sum fun b _ => hL a b
  have hg : ContDiffAt ℝ (↑k) g z := ContDiffAt.sum fun a _ => hF a
  have ht : (fun t : ℝ => ether P i (x+t • v-y))=ᶠ[𝓝 0] (fun t : ℝ => g (z + t • u)) := by
    have ht : ∀ᶠ t : ℝ in 𝓝 0,z+t • u∈away := (show ContinuousAt (fun t : ℝ => z+t • u) 0 from continuousAt_const.add (continuousAt_id.smul continuousAt_const)).preimage_mem_nhds (open_away.mem_nhds (by simpa using hp))
    filter_upwards [ht] with t ht
    have hx : z+t • u = -(x+t • v-y) := by unfold z u; rw [smul_neg]; abel
    rw [ether_reply P i (neg_ne_zero.mp (show -(x+t • v-y)∈away by rwa [← hx])) hx ht]
    rfl
  unfold grade; rw [ht.iteratedDeriv_eq,← along hg u]
  rw [gem0]
  simp_rw [visit_eval, Complex.ofReal_sum]
  have he := coeffFsum k z (fun a x => ∑ b : Axis, L a b (f a b x)) (s:=Finset.univ (α:=Axis)) (fun a _ => hF a)
  change coeff g k z (fun _ => u) = _; change coeff g k z = _ at he
  rw [he,sum_apply]; refine Finset.sum_congr rfl fun a _ => ?_
  rw [coeffFsum _ _ _ _ (fun b _ => hL a b),sum_apply]; refine Finset.sum_congr rfl fun b _ => ?_
  rw [show coeff (fun x => L a b (f a b x)) k z (fun _ => u) = L a b (diagonal (coeff (f a b) k z) u) from coeff_linear _ _ (hC a b)]
  rw [show u=(-1:ℝ) • v from (neg_one_smul ..).symm, homogeneous]; rfl
end YM.Extra.FD.OPE
