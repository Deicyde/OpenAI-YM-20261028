import YM.Extra.WEAK_SCALING_ACTLAW.Criteria

/-!
# Stress-type calculation for color-pair generators at weight four

Expose explicitly the required generation/covariance/real/mean properties
of a field array (intended entry ijkl = color-summed Wick F_ij F_kl on the
normalized free comparator). Verify the signed-coordinate basis reduction
of H-real mean-zero tensors (even without assuming independence of all the
pairing generators), including the 1/4 ordered-pair trace convention of E
`eq:Wstress`, on the actual Field 4. The generation and remaining divergence
certificate obligations on the colored Maxwell data are not claimed here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling.Cube
open Set Filter Function MeasureTheory Analysis Table Org Climb
open Work.A01 (eps)
open scoped Topology ContDiff
variable {G : Gauge} {L : Register G} {S : Table L}

private abbrev pairs := Fin 6
def left : pairs → Axis := ![0,0,0,1,1,2]
def right : pairs → Axis := ![1,2,3,2,3,3]

abbrev Pairs (S : Table L) := Axis → Axis → Axis → Axis → S.Field 4

def uv (v : Pairs S) (i j : pairs) := v (left i) (right i) (left j) (right j)

structure Types (H : S.RealSpin) (v : Pairs S) : Prop where
  exchange a b c d : v a b c d = v c d a b
  skew a b c d : v a b c d = -v b a c d
  real a b c d : S.conj H 4 (v a b c d)=v a b c d
  action g a b c d : S.mirror H 4 g (v a b c d) = (eps g a * eps g b * eps g c * eps g d) • v (g.perm a) (g.perm b) (g.perm c) (g.perm d)
  mean a b c d : (Work.A15.front (S:=S) (n:=0) 0 Fin.elim0 4) (v a b c d)=0
  generates (x : S.Field 4) : ∃ (z : ℂ) (b : pairs → pairs → ℂ), x=z • S.unit 4 + ∑ i, ∑ j, b i j • uv v i j

variable {H : S.RealSpin} {v : Pairs S}
namespace Types
variable (h : Types H v)
include h
lemma generate_real (hs : S.Hierarchy) (x : S.Field 4) (hx : S.conj H 4 x=x)
    (hm : (Work.A15.front (n:=0) 0 Fin.elim0 4) x=0) : ∃ b : pairs → pairs → ℝ, x=∑ i, ∑ j, b i j • uv v i j := by
  obtain ⟨z,b,hb⟩ := h.generates x
  rw [hb,map_add,map_sum,map_smul,unit_mean hs,smul_eq_mul,mul_one] at hm
  simp only [map_sum,map_smul,uv,h.mean,smul_zero,Finset.sum_const_zero,add_zero] at hm
  simp only [hm,zero_smul,zero_add] at hb
  refine ⟨fun i j => (b i j).re,smul_right_injective _ (two_ne_zero (α:=ℂ)) ?_⟩
  change (2:ℂ) • x = (2:ℂ) • _
  nth_rw 1 [two_smul,← hx,hb]
  rw [hb]
  simp only [_root_.map_sum,map_smulₛₗ,uv,h.real,← Finset.sum_add_distrib, Finset.smul_sum,
    ← add_smul, add_comm ((starRingEnd ℂ) _) (b _ _), Complex.add_conj,
    RCLike.real_smul_eq_coe_smul (K:=ℂ), smul_smul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => congrArg (fun z : ℂ => z • _) (Complex.ofReal_mul ..)

private def plain (s : Equiv.Perm Axis) : Signed := ⟨s,fun _ => false⟩
lemma move (s : Equiv.Perm Axis) (a b c d : Axis) : S.mirror H 4 (plain s) (v a b c d) = v (s a) (s b) (s c) (s d) := by
  simp [h.action,eps,plain,Signed.matrix_at]
lemma symmetry (a b : Axis) : v a b a b = v b a b a := by rw [h.skew a b a b,h.exchange,h.skew a b,neg_neg]
lemma self (a b c : Axis) : v a a b c = 0 := by
  apply smul_right_injective _ (two_ne_zero (α:=ℂ))
  change (2:ℂ) • v a a b c = (2:ℂ) • (0:S.Field 4)
  rw [two_smul]; nth_rw 1 [h.skew a a]; simp

private def χ (t i j : Axis) := eps (Signed.mirror t) i * eps (Signed.mirror t) j
private def signs (t : Axis) (i : pairs) := χ t (left i) (right i)
private def parity (t a b : Axis) : S.Field 4 →ₗ[ℝ] S.Field 4 :=
    (2:ℝ)⁻¹ • (LinearMap.id + χ t a b • (S.mirror H 4 (Signed.mirror t)).restrictScalars ℝ)
private def delta (t a b : Axis) (i j : pairs) :=
    (2:ℝ)⁻¹*(1+χ t a b * (signs t i * signs t j))

omit h in
private lemma preserves {J : S.Stress} (hw : RawTensor H J) (a b t : Axis) : parity (H:=H) t a b (J a b) = J a b := by
  have he := Work.A01.tensor_column hw (Signed.mirror t) a b
  change S.mirror H _ _ _= (↑(χ t a b):ℂ) • J a b at he
  rw [show (↑(χ t a b):ℂ) • J a b = χ t a b • J a b from (RCLike.real_smul_eq_coe_smul (K:=ℂ) ..).symm] at he
  change (2:ℝ)⁻¹ • (J a b + χ t a b • (S.mirror H 4 (Signed.mirror t) (J a b))) = _
  have hs j := Work.A01.eps_self (Signed.mirror t) j
  rw [he, smul_smul,show χ t a b * χ t a b=1 by rw [χ, mul_mul_mul_comm, hs, hs,one_mul], one_smul, ← two_smul ℝ, inv_smul_smul₀ two_ne_zero]

private lemma value (a b t : Axis) (i j : pairs) : parity (H:=H) t a b (uv v i j) = delta t a b i j • uv v i j := by
  change (2:ℝ)⁻¹ • (uv v i j + χ t a b • S.mirror H 4 (Signed.mirror t) (uv v i j)) = _
  unfold delta signs χ uv; rw [h.action]
  simp only [Signed.mirror,Equiv.refl_apply]; module

private def gate (a b : Axis) (i j : pairs) := delta 0 a b i j * delta 1 a b i j * delta 2 a b i j

private lemma tested {J : S.Stress} (hw : RawTensor H J) (a b : Axis) (p : pairs → pairs → ℝ)
    (he : J a b = ∑ i, ∑ j, p i j • uv v i j) : J a b = ∑ i, ∑ j, p i j • (gate a b i j • uv v i j) := by
  calc
    J a b = parity (H:=H) 2 a b (parity (H:=H) 1 a b (parity (H:=H) 0 a b (J a b))) := by rw [preserves hw, preserves hw, preserves hw]
    _ = _ := by
      rw [he]; simp only [map_sum,map_smul,h.value,smul_smul,gate,mul_assoc]

omit h in
private lemma even_gate (i j : pairs) : gate 0 0 i j = if i=j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff,gate,delta,signs,χ,eps,left,right,Signed.mirror,Signed.matrix_at]
omit h in
private lemma odd_gate (i j : pairs) : gate 0 1 i j =
    if (i=1 ∧ j=3) ∨ (i=2 ∧ j=4) ∨ (i=3 ∧ j=1) ∨ (i=4 ∧ j=2) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff,gate,delta,signs,χ,eps,left,right,Signed.mirror,Signed.matrix_at]

private abbrev sq (v : Pairs S) (i j : Axis) := v i j i j

private lemma even {J : S.Stress} (hw : RawTensor H J) (p : pairs → pairs → ℝ) (he : J 0 0 = ∑ i, ∑ j, p i j • uv v i j) :
    let f := fun i => p i i
    J 0 0 = (((((f 0 • sq v 0 1 + f 1 • sq v 0 2) + f 2 • sq v 0 3) + f 3 • sq v 1 2) + f 4 • sq v 1 3) + f 5 • sq v 2 3) := by
  have hp := h.tested hw 0 0 p he
  simp_rw [even_gate, ite_smul, one_smul,zero_smul,smul_ite,smul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true] at hp
  simpa [Fin.sum_univ_six, sq, uv,left,right] using hp

set_option maxHeartbeats 1000000 in
private lemma odd {J : S.Stress} (hw : RawTensor H J) (p : pairs → pairs → ℝ) (he : J 0 1 = ∑ i, ∑ j, p i j • uv v i j) :
    J 0 1 = (p 1 3 + p 3 1) • v 0 2 1 2 + (p 2 4 + p 4 2) • v 0 3 1 3 := by
  rw [h.tested hw 0 1 p he]
  simp_rw [odd_gate,Fin.sum_univ_six]; norm_num [Fin.ext_iff,uv,left,right]
  change p 1 3 • v 0 2 1 2 + p 2 4 • v 0 3 1 3 + p 3 1 • v 1 2 0 2 + p 4 2 • v 1 3 0 3 = _
  rw [h.exchange 1 2 0 2,h.exchange 1 3 0 3]; module

omit h in
private lemma invariance {J : S.Stress} (hw : RawTensor H J) (s : Equiv.Perm Axis) (a b : Axis) : S.mirror H 4 (plain s) (J a b) = J (s a) (s b) := by
  simp [Work.A01.tensor_column hw,plain,eps,Signed.matrix_at]

private def m (s : Equiv.Perm Axis) := (S.mirror H 4 (plain s)).restrictScalars ℝ
private def cycle := Equiv.swap (1:Axis) 2 * Equiv.swap (2:Axis) 3
private lemma symmetric' (i j) : sq v i j = sq v j i := h.symmetry i j
private lemma sq_move (s : Equiv.Perm Axis) (a b) : m (H:=H) s (sq v a b) = sq v (s a) (s b) := h.move ..

private lemma even_shape {J : S.Stress} (hw : RawTensor H J) (p : pairs → pairs → ℝ) (he : J 0 0 = ∑ i, ∑ j, p i j • uv v i j) :
    ∃ x y : ℝ, J 0 0 = x • (sq v 0 1 + sq v 0 2 + sq v 0 3) + y • (sq v 1 2 + sq v 1 3 + sq v 2 3) := by
  let f i := p i i
  let g := m (H:=H) cycle
  have h0 : cycle (0:Axis) = 0 := by decide
  have hg : g (J 0 0) = J 0 0 := (invariance hw cycle 0 0).trans (by rw [h0])
  have ht := h.even hw p he; dsimp only at ht
  refine ⟨(3:ℝ)⁻¹*(f 0+f 1+f 2), (3:ℝ)⁻¹*(f 3+f 4+f 5), ?_⟩
  have hJ : J 0 0 = (3:ℝ)⁻¹ • (J 0 0 + g (J 0 0) + g (g (J 0 0))) := by simp only [hg]; module
  rw [hJ,ht]
  simp_rw [map_add, map_smul,g, h.sq_move,h0,show cycle (1:Axis)=2 by decide,show cycle (2:Axis)=3 by decide,
    show cycle (3:Axis)=1 by decide,show cycle (1:Axis)=2 by decide, h.symmetric' (2:Axis) (1:Axis), h.symmetric' (3:Axis) (1:Axis),h.symmetric' (3:Axis) (2:Axis)]
  dsimp [f]; module

private lemma odd_shape {J : S.Stress} (hw : RawTensor H J) (p : pairs → pairs → ℝ) (he : J 0 1 = ∑ i, ∑ j, p i j • uv v i j) :
    ∃ z : ℝ, J 0 1 = z • (v 0 2 1 2 + v 0 3 1 3) := by
  let s := Equiv.swap (2:Axis) 3
  have h0 : s (0:Axis)=0 := by decide
  have h1 : s (1:Axis)=1 := by decide
  have hs : m (H:=H) s (J 0 1) = J 0 1 := (invariance hw _ _ _).trans (by rw [h0,h1])
  refine ⟨(2:ℝ)⁻¹*(p 1 3 + p 3 1 + (p 2 4 + p 4 2)), ?_⟩
  have hJ : J 0 1 = (2:ℝ)⁻¹ • (J 0 1 + m (H:=H) s (J 0 1)) := by rw [hs]; module
  rw [hJ,h.odd hw p he]; simp only [map_add,map_smul,m,LinearMap.restrictScalars_apply,h.move,h0,h1, show s (2:Axis)=3 by decide, show s (3:Axis)=2 by decide]
  module

/-- All diagonal squares (ordered pairs, as in Wstress). -/
def total (v : Pairs S) := ∑ i : Axis, ∑ j : Axis, sq v i j
/-- Sum with common leg i contracted, not antisymmetric partners in reverse order. -/
def contracted (v : Pairs S) (a b : Axis) := ∑ i : Axis, v a i b i

def A (v : Pairs S) : S.Stress := fun a b => if a=b then contracted v a b else 0
def C (v : Pairs S) : S.Stress := fun a b => if a=b then 0 else contracted v a b
/-- B: nonincident unordered squares once each on aa. -/
def B (v : Pairs S) : S.Stress := fun a b => if a=b then (2:ℝ)⁻¹ • total v - contracted v a b else 0
/-- canonical color-summed stress in terms of this field array, no floating
normalization here. -/
def stress (v : Pairs S) : S.Stress := fun a b => contracted v a b - (if a=b then (4:ℝ)⁻¹ • total v else 0)
omit h in
lemma stress_eq : stress v = (2:ℝ)⁻¹ • (A v - B v + (2:ℝ) • C v) := by
  ext1 i; ext1 j
  change contracted .. - _ = (2:ℝ)⁻¹ • (A v i j - B v i j + (2:ℝ) • C v i j)
  by_cases he : i=j <;> simp [he,A,B,C]; module

lemma contracts (s : Equiv.Perm Axis) (a b) : m (H:=H) s (contracted v a b) = contracted v (s a) (s b) := by
  simp only [contracted,map_sum,m,LinearMap.restrictScalars_apply,h.move]; exact Equiv.sum_comp s (fun i => v (s a) i (s b) i)
lemma total_invariant (s : Equiv.Perm Axis) : m (H:=H) s (total v) = total v := by
  simp only [total,map_sum,h.sq_move]; simp_rw [Equiv.sum_comp s (sq v _), Equiv.sum_comp s (fun i => ∑ j, sq v i j)]
lemma components_move (s : Equiv.Perm Axis) (a b : Axis) :
    m (H:=H) s (A v a b) = A v (s a) (s b) ∧ m (H:=H) s (B v a b)= B v (s a) (s b) ∧ m (H:=H) s (C v a b) = C v (s a) (s b) := by
  by_cases he : a=b <;> simp [A,B,C,s.injective.eq_iff,he,h.contracts,h.total_invariant]

lemma spans (hS : S.Hierarchy) {J : S.Stress} (hw : RawTensor H J) (hr : ∀ a b, S.conj H 4 (J a b) = J a b) (hz : Centered J) :
    ∃ x y z : ℝ, J = x • A v + y • B v + z • C v := by
  choose p hp using fun a b => h.generate_real hS (J a b) (hr a b) (hz a b)
  obtain ⟨x,y,hx⟩ := h.even_shape hw (p 0 0) (hp 0 0)
  obtain ⟨z,hz⟩ := h.odd_shape hw (p 0 1) (hp 0 1)
  have h₁ : J 0 0 = x • A v 0 0 + y • B v 0 0 + z • C v 0 0 := by
    rw [hx]; simp [A,B,C,contracted,total,Fin.sum_univ_four,h.self]
    rw [h.symmetric' 1 0,h.symmetric' 2 0,h.symmetric' 2 1,h.symmetric' 3 0,h.symmetric' 3 1,h.symmetric' 3 2]; unfold sq; module
  have h₂ : J 0 1 = x • A v 0 1 + y • B v 0 1 + z • C v 0 1 := by
    rw [hz]; norm_num [A,B,C,contracted,Fin.sum_univ_four,h.self, h.exchange 0 1 1 1]
  have hm (s : Equiv.Perm Axis) (a b : Axis) (ht : J a b=x • A v a b + y • B v a b + z • C v a b) :
      J (s a) (s b) = x • A v (s a) (s b) + y • B v (s a) (s b) + z • C v (s a) (s b) := by
    obtain ⟨ha,hb,hc⟩ := h.components_move s a b
    rw [← show m (H:=H) s (J a b) = _ from invariance hw s a b,ht,map_add,map_add,map_smul,map_smul,map_smul,ha,hb,hc]
  refine ⟨x,y,z,funext fun a => funext fun b => ?_⟩
  change J a b=x • _ + y • _ + z • _
  by_cases he : a=b
  · subst b; simpa using hm (Equiv.swap 0 a) 0 0 h₁
  let e := Equiv.swap 0 a
  let s := Equiv.swap (e 1) b * e
  have h' : s 1=b := by simp [s]
  have he' : e 0 = a := Equiv.swap_apply_left ..
  have hs : s 0=a := by
    dsimp only [s, Equiv.Perm.mul_apply]; rw [Equiv.swap_apply_of_ne_of_ne,he']
    · exact e.injective.ne (by decide)
    exact he' ▸ he
  simpa only [h',hs] using hm s 0 1 h₂

end Types

lemma certifies (T : Lighthouse L) {H : (Bel L).Hierarchy} {v : Pairs (Bel L)} (h : Types H.spin v)
    (a b : Axis → (Bel L).Field 5) (hA : div T.W (Types.A v) = (2:ℝ) • a) (hB : div T.W (Types.B v) = (2:ℝ) • b)
    (hC : div T.W (Types.C v) = b-a) (he : LinearIndependent ℝ ![a,b]) {τ : ℝ} (ht : τ ≠ 0)
    (hJ : T.J = τ • Types.stress v) : Line T H.spin := by
  rw [Types.stress_eq,smul_smul] at hJ
  exact matrix_line T _ _ _ _ (fun P _ hr ht hz => h.spans H ht hr hz) a b hA hB hC he (mul_ne_zero ht (by norm_num)) hJ
end YM.Extra.WeakScaling.Cube
