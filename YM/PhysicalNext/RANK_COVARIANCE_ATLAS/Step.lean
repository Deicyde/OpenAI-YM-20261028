import YM.Next.FREE_KERNELS.Traffic
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Shutter


/-!
# Train for the actual arc

Pulses, runs and **optic**. Move the same difference along the physical
curvature column; otherwise a pre-L absolute row estimate on that column alone
doesn't prove the higher grades. All integer lifts, any color. No imposing
minimum-image support on ψ after sending to fin torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RankCovariance
open Function Lattice Laurent Bloch Exterior Matrix Precision Next.Free RG FreeResolvent Finset
open Next.Rank Next.Rank.Atlas Next.Rank.Perch Next.Rank.Beamer Next.Rank.CellsInt
open scoped Topology BigOperators

variable {G : Gauge} {n : Side} {A : Levels G} {j t N i p : ℕ}

private lemma travelling (v : Chamber G A.S i p → ℝ) :
    liftPAC (Radian.hopP (stamp A N p) i v) = passage A N i p *ᵥ liftPAC v := by
  funext x; obtain ⟨x,rfl⟩:=toPAC.surjective x
  unfold liftPAC; rw [Function.comp_apply, Equiv.symm_apply_apply]; unfold Radian.hopP; simp_rw [path_entry, Complex.ofReal_re]
  let f (z : FreeResolvent.Slot G (A.S.side i p) 2) := passage A N i p (toPAC x) z * v (toPAC.symm z)
  change _ = ∑ j,f j; rw [← Equiv.sum_comp toPAC]
  simp only [f,Equiv.symm_apply_apply]

-- Full Bianchi (also in the torus harmonic sector). Use `sale`, from the
-- same ψ formula; no claim that a closed cochain here is globally d-exact.
lemma crossing_preserves (v : Chamber G A.S i p → ℝ) (h : shutter (Radian.wall_chart (P:=A.S) (k:=i) (p:=p) v)) :
    shutter (Radian.wall_chart (P:=A.S) (k:=i+1) (p:=p) (Radian.hopP (stamp A N p) i v)) := by
  rw [← chart_eq, PhysicalNext.RankCovariance.shutters] at h ⊢
  let k:= A.clock.kernel; let f:=A.S.side (i+1) p; let c:= A.S.side i p; let L:= A.clock.op i p
  let P:=destination A N i; let C:= installed L.ratio (P.sale k.penalty)
  have hh := (A.S.oneStep i p).exact_size
  have ht:= A.clock.adm i; have hs := k.penalty_pos
  let J:= (pink k.penalty P.land).acts c
  let I:= (blue k.penalty P.land).acts c
  let U:= (blue k.penalty P.wing).acts f; let T:= installed L.ratio (P.duo k.penalty).T
  have he : Exterior.d 2 f * psiStep A N i p = C*Exterior.d 2 c := by
    have hh1 : I*J=1 := mul_eq_one_comm.mp (heart_inverse k.penalty hs ht P.land c).1
    have hh2 : C * Exterior.d 2 c * I = Exterior.d 2 f*U*T := P.intake ht k hh
    rw [show psiStep A N i p= U*T*J from P.psi_bridge _ hs ht hh,
      ← Matrix.mul_assoc,← Matrix.mul_assoc (Exterior.d 2 f) U,← hh2,Matrix.mul_assoc (C * Exterior.d 2 c),hh1,Matrix.mul_one]
  rw [travelling,Matrix.mulVec_mulVec]; unfold passage; rw [← promote_prod,he,promote_prod,← Matrix.mulVec_mulVec,h,Matrix.mulVec_zero]

-- `jumps` prints a right ordering; physical motion is a product. Verify
-- even at boundary: nearest neighbor on actual wrapped positions.
private lemma accounting (u : Fin j → Axis) (v : Body 2 n → ℝ) (x : Cover) (b : TypeFace 2) :
    jumps j u (fun z=> v (wrap n z,b)) x= (motion (TypeFace 2) n (List.ofFn u)*ᵥ v) (wrap n x,b) := by
  induction j generalizing x with
  | zero=> rw [List.ofFn_zero,motion_zero,Matrix.one_mulVec]; rfl
  | succ j ih =>
    rw [List.ofFn_succ, motion_walk,← Matrix.mulVec_mulVec, knock_entry, jumps,hopped]; unfold stepValue; rw [ih,ih,map_add,wrap_step]; rfl

lemma marked_motion (k : Degree G) (v : Incidence G n→ℝ) :
    gesture k (nativeChart v) = (motion (TypeFace 2) n (List.ofFn k.layout)*ᵥ component (liftPAC v) k.paint) (wrap n k.point,plaquette k.a) := by
  let b:=k.a; let t(z) := nativeChart v (z,b,k.paint)
  have he z : component (liftPAC v) k.paint (wrap n z,plaquette b) = t z := by
    change v (toPAC.symm (toPAC (wrap n z,b,k.paint))) = _; rw [Equiv.symm_apply_apply]; rfl
  rw [← accounting, show (fun z=> component (liftPAC v) k.paint (wrap n z,plaquette b))=t from funext he]; rfl

private lemma eases (a : ℕ) (u : Fin a→Axis) (v : Chamber G A.S i p→ℝ) (r : ℝ) (h : Radian.logic (P:=A.S) (k:=i) (p:=p) v a r) (j : G.ColorIndex) (b : Body 2 (A.S.side i p)) :
    let n := A.S.side i p
    ‖(motion (TypeFace 2) n (List.ofFn u)*ᵥ component (liftPAC v) j) b‖ ≤ r := by
  intro n; rcases b with ⟨x,b⟩; obtain ⟨b,rfl⟩:=plaqEquiv.surjective b
  let D : Degree G:= ⟨b,j,lift x,a,u⟩
  have hh := h D rfl; rw [← chart_eq, marked_motion,show wrap n D.point=x from wrap_lift x] at hh; exact hh

lemma optic_budget (k : Degree G) (v : Chamber G A.S i p → ℝ) {r C σ R : ℝ}
    (hr : 0 ≤ r) (hs : 0 < σ) (hv : k.degree ≤ A.clock.J (i+1) -2)
    (h : Radian.logic (P:=A.S) (k:=i) (p:=p) v k.degree r)
    (hk : Fintype.card (TypeFace 2)*C ≤ R)
    (hC : let P := destination A N i
          (P.groundPsi A.clock.kernel.penalty (List.ofFn k.layout)).strip σ (C/(A.S.a i/A.S.a (i+1))^(k.degree + 2))) :
    ‖gesture k (Radian.wall_chart (P:=A.S) (k:=i+1) (p:=p) (Radian.hopP (stamp A N p) i v))‖ ≤ r * R / (A.S.a i/A.S.a (i+1))^(k.degree + 2) := by
  let f:=A.S.side (i+1) p; let c:=A.S.side i p; let t:=List.ofFn k.layout; let P:=destination A N i; let p':=(A.clock.op i p).ratio
  let U:=P.groundPsi A.clock.kernel.penalty t; let L:=installed p' U
  let F:= wrap f k.point; let D:=plaquette k.a
  let v':= component (liftPAC v) k.paint; let M:= fun (f : Side)=> motion (TypeFace 2) f t
  rw [← chart_eq, marked_motion,travelling]; unfold passage; rw [component_mul]
  have hlen:t.length≤A.clock.J (i+1)-2:= by simp only [t,List.length_ofFn];exact hv
  have hh : M f * psiStep A N i p=L*M c:= P.refund_period _ A.clock.kernel.penalty_pos (A.clock.adm i) (A.S.oneStep i p).exact_size t hlen
  change ‖(M f *ᵥ _) (_,_)‖≤_;rw [Matrix.mulVec_mulVec,hh,← Matrix.mulVec_mulVec]; change ‖(L *ᵥ (M c *ᵥ v')) (F,D)‖ ≤ _
  let m:= (A.S.a i/A.S.a (i+1))^(k.degree+2)
  have hp : 0<m:=pow_pos (div_pos (A.S.a_pos i) (A.S.a_pos (i+1))) _
  have he : ∑ j : Body 2 c, ‖L (F,D) j‖ ≤ Fintype.card (TypeFace 2) * (C/m) := by
    let Z:= splitCo p' (TypeFace 2) (F,D)
    change U.strip σ (C/m) at hC
    have hx : ∑ j : Body 2 c, ‖U.acts c Z j‖ ≤ Fintype.card (TypeFace 2) * (C/m) := by simpa only [zero_mul,Real.exp_zero,one_mul] using row_sprawl (by rfl : (0:ℝ)≤0) (Work.F08.strip_mono hC hs.le le_rfl) c Z
    exact hx
  have hQ y : ‖(M c *ᵥ v') y‖ ≤ r:= eases _ _ _ _ h k.paint y
  unfold Matrix.mulVec dotProduct
  apply le_trans (norm_sum_le ..)
  calc
    _ ≤ ∑ j : Body 2 c, ‖L (F,D) j‖* r := Finset.sum_le_sum fun j _=> by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hQ j) (norm_nonneg _)
    _ ≤ Fintype.card (TypeFace 2) * (C/m)* r := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right he hr
    _ = r*(Fintype.card (TypeFace 2) * C)/m := by ring
    _ ≤ _:= div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk hr) hp.le

/-- Pre-L currency for the difference motion. UNIFORM over Flight, all
periods and orders in the tested range, after KernelChoices and current stage
indices. (No paying this by measuring each row after picking length.) -/
lemma train_issue (K : KernelChoices) (j t : ℕ) (hj : 4≤j) (ht : 4≤t): ∃ R : ℝ, 1 ≤ R ∧
    ∀ {G : Gauge} (A : Levels G), A.clock.kernel=K → ∀ N i p d, A.clock.J (i+1)=j → A.clock.J i=t → d-1 ≤ j-2 → Radian.Train (stamp A N p) i d R := by
  obtain ⟨σ,C,hσ,hC,h⟩:= Flight.stockroom K.penalty K.penalty_pos hj ht
  let M : ℝ:= Fintype.card (TypeFace 2)*C
  refine ⟨max 1 M,le_max_left ..,fun {G} A ha N i p d hy hz hd=> ?_⟩
  subst j;subst t
  refine ⟨fun i' j'=> path_real A N i p i' j',fun f hk=>crossing_preserves _ hk,fun k hk f v hv hl=> ?_⟩;intro u hu
  subst k; apply optic_budget _ _ hv hσ (le_trans hk hd) hl (le_max_right ..)
  intro P; rw [ha,(distances A i p).1]
  rw [show u.degree+2=2+(List.ofFn u.layout).length by simp only [List.length_ofFn];omega]; apply h P
  rw [List.length_ofFn]; exact le_trans hk hd
end YM.PhysicalNext.RankCovariance
