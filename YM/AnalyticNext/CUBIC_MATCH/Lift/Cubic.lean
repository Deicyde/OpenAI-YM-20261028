import YM.AnalyticNext.CUBIC_MATCH.Lift.Augment

set_option warningAsError false

/-!
# Lift with dependent contraction retained

 at EXACTLY n=3. This finishes the simultaneous lift in all three
legs -- *without* paying the estimates based on each intermediate period. We
state the multiplicative costs before incoming rows/caps. This is an actual
on-cover primitive with real signs. In particular we can then lift tensors
lying in an invariant COLOR subspace, act identically on color degrees, and
use paths without having any sorting/sign rule on that subspace's basis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch.Lift

open Filter Function Lattice RG Precision Work.F08 Laurent Bloch Exterior Next.Free
open scoped Topology BigOperators ContDiff

variable {η C D : ℝ}

/-- Stand up the z leg in rows closed in x,y. -/
lemma planted (hη : 0<η) : ∃ θ D : ℝ, 0<θ ∧ 0<D ∧ ∀ C : ℝ, 0≤C → ∀ U : Three ℝ 1 1 1,
    Pace η C U → δx U=0 → δy U=0 → δz U=0 → ∃ X : Three ℝ 1 1 2,
      Pace θ (D*C) X ∧ δz X=U ∧ δx X=0 ∧ δy X=0 := by
  obtain ⟨a,F,ha,hF,H⟩ := gainZ_cost 1 1 0 hη
  let V := stepFee a aheadY 0*F
  have hv : 0 ≤ V := mul_nonneg (stepFee_nonneg ..) hF.le
  obtain ⟨b,G,hb,hG,Q⟩ := gainZ_cost 1 0 1 ha
  let B := G*V
  let R := omitFee b*B
  have hB : 0 ≤ B := mul_nonneg hG.le hv
  have hR : 0 ≤ R := mul_nonneg (share_pos hb).le hB
  obtain ⟨d,J,hd,hJ,S⟩ := rear_price 1 2 hb
  let M := stepFee d behind 3*(J*R)
  let w := min b d; have hw : 0<w := lt_min hb hd
  have hM : 0≤M := mul_nonneg (stepFee_nonneg ..) (mul_nonneg hJ.le hR)
  obtain ⟨e,K,he,hK,L⟩ := restore_price 1 3 hw
  let N := K*(B+M)
  let T := stepFee e behind 2*N
  have hN : 0≤N := mul_nonneg hK.le (add_nonneg hB hM)
  have hT : 0≤T := mul_nonneg (stepFee_nonneg ..) hN
  refine ⟨min a e,F+T,lt_min ha he,add_pos_of_pos_of_nonneg hF hT,
    fun C hC U h hx hy hz => ?_⟩
  let A : Three ℝ 1 1 2 := gainZ U
  have pA : Pace a (F*C) A := H _ hC U h
  have az : δz A=U := gainZ_cross h hη hz
  have ax : δx A=0 := gainZ_kept h hη hx
  let Y := δy A
  have pY : Pace a (V*C) Y := mul_assoc (stepFee a aheadY 0) F C ▸ pA.y ha.le
  have yz' : δz Y=0 := by unfold Y; rw [← yz,az,hy]
  have yx : δx Y=0 := by unfold Y; rw [xy,ax,δy_zero]
  let W := gainZ (n:=1) Y
  have pW : Pace b (B*C) W := mul_assoc G V C ▸ Q (V*C) (mul_nonneg hv hC) Y pY
  have wx : δx W=0 := gainZ_kept pY ha yx
  have wz : δz W=Y := gainZ_cross pY ha yz'
  have p : paceTwo b (R*C) (omitY W) := mul_assoc (omitFee b) B C ▸ omit_price hb pW
  have ox : lowX (omitY W)=0 := by rw [← omit_x hb pW,wx,omit_silence]
  have oz : lowZ (s:=2) (omitY W)=0 := by rw [← omit_z hb pW,wz, show omitY Y=0 from omit_y ha pA]
  let K' := rear (s:=2) (omitY W)
  let Z : Three ℝ 1 0 4 := zeroY K'
  have pZ : Pace d ((J*R)*C) Z := mul_assoc J R C ▸ zero_price (S _ (mul_nonneg hR hC) _ p)
  have qZ : Pace d (M*C) (δz Z) := mul_assoc (stepFee d behind 3) (J*R) C ▸ pZ.z hd.le
  have zx : δx Z=0 := by unfold Z K'; rw [zero_x,rear_keeps hb p (mul_nonneg hR hC) oz ox,zeroY_silence]
  let I := W-δz Z
  have pi : Pace w ((B+M)*C) I := by
    rw [add_mul]
    exact (pW.mono (min_le_left ..) le_rfl (mul_nonneg hB hC)).sub (qZ.mono (min_le_right ..) le_rfl (mul_nonneg hM hC))
  have ix : δx I=0 := by unfold I; rw [δx_sub,wx,xz,zx,δz_zero,sub_self]
  have iz : δz I=Y := by unfold I; rw [δz_sub,wz,zz pZ hd,sub_zero]
  have io : omitY I=0 := by unfold I; rw [omit_add hb pW hd qZ,omit_z hd pZ,show omitY Z=K' from omit_zero _,rear_cross hb p oz,sub_self]
  let E := restore I
  have pe : Pace e (N*C) E := mul_assoc K (B+M) C ▸ L _ (mul_nonneg (add_nonneg hB hM) hC) _ pi
  have pt : Pace e (T*C) (δz E) := mul_assoc (stepFee _ _ _) N C ▸ pe.z he.le
  have ex : δx E=0 := restore_keep hw pi ix
  have ey : δy E=I := restore_cross hw pi io
  refine ⟨A-δz E,?_,?_,?_,?_⟩
  · rw [add_mul]; exact (pA.mono (min_le_left ..) le_rfl (mul_nonneg hF.le hC)).sub
      (pt.mono (min_le_right ..) le_rfl (mul_nonneg hT hC))
  · rw [δz_sub,az,zz pe he, sub_zero]
  · rw [δx_sub,ax,xz,ex,δz_zero,sub_self]
  rw [δy_sub,yz,ey,iz]; exact sub_self _

abbrev completely {E : Type*} [AddCommGroup E] [Module ℝ E] (T : Three E 2 2 2) :=
    δz (t:=1) (δy (s:=1) (δx (r:=1) T))

theorem carried (hη : 0<η) : ∃ θ B : ℝ, 0<θ ∧ 0<B ∧ ∀ C : ℝ, 0≤C → ∀ U : Three ℝ 1 1 1,
    Pace η C U → δx U=0 → δy U=0 → δz U=0 → ∃ X : Three ℝ 2 2 2,
      Pace θ (B*C) X ∧ completely X=U := by
  obtain ⟨a,F,ha,hF,H⟩ := planted hη
  obtain ⟨b,K,hb,hK,Q⟩ := gainX_cost 0 1 2 ha
  obtain ⟨θ,G,hθ,hG,P⟩ := gainY_cost 2 0 2 hb
  refine ⟨θ,G*(K*F),hθ,by positivity,fun C hC U h hx hy hz => ?_⟩
  obtain ⟨W,g,gz,gx,gy⟩ := H C hC U h hx hy hz
  let A := gainX (r:=0) W
  let B := gainY (s:=0) A
  have hA : Pace b ((K*F)*C) A := mul_assoc K F C ▸ Q _ (mul_nonneg hF.le hC) W g
  have hB : Pace θ (G*(K*F)*C) B := mul_assoc G (K*F) C ▸ P _ (mul_nonneg (mul_nonneg hK.le hF.le) hC) A hA
  have ax : δx A=W := gainX_cross g ha gx
  have ay : δy A=0 := gainX_kept g ha gy
  have hY : δy B=A := gainY_cross hA hb ay
  exact ⟨B,hB,by unfold completely; rw [← xy,hY,ax,gz]⟩

section color
variable {r s t : ℕ} {ι : Type*}
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]

def apply3 (L : E →ₗ[ℝ] D) (A : Three E r s t) : Three D r s t :=
  fun a b c x => L (A a b c x)

lemma apply3_x (L : E →ₗ[ℝ] D) (A : Three E (r+1) s t) :
    apply3 L (δx A)=δx (apply3 L A) := by funext i j a x; exact bite_map _ (fun i => A i j a) L i x
lemma apply3_y (L : E →ₗ[ℝ] D) (A : Three E r (s+1) t) :
    apply3 L (δy A)=δy (apply3 L A) := by funext i j a x; exact bite_map _ (fun k => A i k a) L j x
lemma apply3_z (L : E →ₗ[ℝ] D) (A : Three E r s (t+1)) :
    apply3 L (δz A)=δz (apply3 L A) := by funext i j a x; exact bite_map _ (A i j) L a x
@[simp] lemma apply3_zero (L : E →ₗ[ℝ] D) : apply3 L (0:Three E r s t)=0 := by
  funext i j a x; exact L.map_zero

lemma apply3_price (L : E →L[ℝ] D) (A : Three E r s t) {η K : ℝ} (p : Pace η K A) :
    Pace η (‖L‖*K) (apply3 L.toLinearMap A) := by
  intro i j b x; rw [mul_assoc]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (p i j b x) (norm_nonneg L))

omit [NormedSpace ℝ E] in
lemma sum_price {α : ι → Three E r s t} (w : Finset ι) (b : ι → ℝ) (θ : ℝ)
    (hw : ∀ i∈w,Pace θ (b i) (α i)) : Pace θ (∑ i∈w,b i) (∑ i∈w,α i) := by
  intro i j k; simp_rw [Finset.sum_apply]
  have hh : Decay length2 θ (∑ i∈w,b i) (fun x => ∑ a∈w,α a i j k x) := Decay.fin fun a p => hw a p i j k
  exact fun x => by simpa only [Finset.sum_apply] using hh x

lemma contracted_sum (a : ι → Three E 2 2 2) (k : Finset ι) :
    completely (∑ i∈k,a i)=∑ i∈k,completely (a i) := by rw [completely,δx_sum,δy_sum,δz_sum]

theorem colors (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hη : 0<η) : ∃ θ F : ℝ, 0<θ ∧ 0<F ∧ ∀ C : ℝ, 0≤C → ∀ U : Three E 1 1 1,
    Pace η C U → δx U=0 → δy U=0 → δz U=0 → ∃ X : Three E 2 2 2,
      Pace θ (F*C) X ∧ completely X=U := by
  classical
  let e := Module.finBasis ℝ E
  let a (i : Fin _) := LinearMap.toContinuousLinearMap (e.coord i)
  let r (i : Fin _) := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (e i)
  have he (x : E) : ∑ i, r i (a i x)=x := e.sum_repr x
  obtain ⟨θ,F,hp,hF,H⟩ := carried hη
  let G : ℝ := ∑ i : Fin (Module.finrank ℝ E), ‖r i‖*(F*‖a i‖)
  have hG : 0≤G := by unfold G; positivity
  refine ⟨θ,G+1,hp,by positivity,fun C hC U h hx hy hz => ?_⟩
  let A (i : Fin (Module.finrank ℝ E)) := apply3 (a i).toLinearMap U
  have hm i : ∃ X : Three ℝ 2 2 2,
      Pace θ (F*(‖a i‖*C)) X ∧ completely X=A i := H _ (by positivity) _ (apply3_price (a i) U h)
        (by unfold A; rw [← apply3_x, hx,apply3_zero])
        (by unfold A; rw [← apply3_y, hy,apply3_zero])
        (by unfold A; rw [← apply3_z, hz,apply3_zero])
  choose X p g using hm
  let B i := apply3 (r i).toLinearMap (X i)
  have Hk i : completely (B i)=apply3 (r i).toLinearMap (A i) := by
    unfold B completely; rw [← apply3_x, ← apply3_y, ← apply3_z,show δz _=_ from g i]
  refine ⟨∑ i,B i,?_,?_⟩
  · have hv := sum_price Finset.univ _ θ (α:=B) (fun i _ => apply3_price (r i) _ (p i))
    apply hv.mono le_rfl _ (by positivity)
    simp only [add_mul,G,Finset.sum_mul,one_mul,mul_assoc]; linarith
  rw [contracted_sum]; funext i j k x
  simp only [Hk,Finset.sum_apply]; exact he _
end color
end YM.CubicMatch.Lift
