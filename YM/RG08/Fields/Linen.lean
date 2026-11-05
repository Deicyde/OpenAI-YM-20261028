import YM.RG08.Fields.Nimb

/-! # Exact conditional projection law tested on active polynomial legs
Finite periods. Tree forest unconstrained except on branches here. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Drift
open Function Filter Set Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary
open scoped Topology BigOperators
variable {G : Gauge} {c f : Side} {j n : ℕ}
-- matrix version using the RIGHT Schur law
lemma sprig_eq (S : StepData c f) (T : Forest S.ratio) (M : FreeResolvent.FaceRow) (hM : (treeMatrix G S T M).PosDef)
    (v : Vec G f 1) : FreeResolvent.covariance G S T M *ᵥ (fullMatrix G S M *ᵥ v)=representative S T v := by
  classical
  have hx : treeInverse G S T M 0 * treeMatrix G S T M=1 := by unfold treeInverse resolve; rw [zero_smul,add_zero]; exact nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hM.isUnit)
  let w:=representative S T v; let L:=insertion (plant (G:=G) T); let u:=reduce G S T *ᵥ w
  have hu : L *ᵥ u=w:=projects T w (onto_slice T v)
  calc
    _ = FreeResolvent.covariance G S T M *ᵥ (fullMatrix G S M *ᵥ (L*ᵥ u)) := by rw [hu]; unfold w; rw [FreeResolvent.invariant]
    _ = L *ᵥ u := by
      rw [FreeResolvent.covariance,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.mulVec_mulVec _ (reduce G S T), Matrix.mulVec_mulVec u,
        show reduce G S T * fullMatrix G S M * L=treeMatrix G S T M from insertion.compress _ _, Matrix.mulVec_mulVec u (treeInverse G S T M 0), hx, Matrix.one_mulVec]
    _ = _ := hu

lemma tensor_times (c f n : Side) (G : Gauge) {i j k : ℕ} (A : Matrix (Body i c) (Body j f) ℝ) (B : Matrix (Body j f) (Body k n) ℝ) :
    tensor G (A*B) = tensor G A*tensor G B := by rw [← tensor_same,← tensor_same, ← tensor_same]; exact patron_mul ..
lemma tint_fund (G : Gauge) (c : Side) (i : ℕ) : tensor G (1 : Matrix (Body i c) (Body i c) ℝ)=1 := by
    ext ⟨x,a,v⟩ ⟨y,b,w⟩; by_cases h:v=w
    · subst v; simp [tensor,Matrix.one_apply]
    simp [tensor,h,Matrix.one_apply]
lemma tensor_clear (G : Gauge) (c f : Side) (i j : ℕ) : tensor G (0 : Matrix (Body i c) (Body j f) ℝ)=0 := by ext i j; simp [tensor]

/-- Left,right *aggregate Hessians*, therefore through all finite polarized tensor tests
    horizontally supported; no p=0 removal expense on the Γ. -/
theorem dwell (G : Gauge) {S : StepData c f} (T : Forest S.ratio) {A : Train j} {D : Train n} {k : ℝ}
    (hk : 0<k) (hj : 4≤j) (hn : 4≤n) (H : (treeMatrix G S T (pink k A)).PosDef)
    {W : Matrix (Body 1 f) (Body 1 c) ℝ} (h : Inputs S W ((pink k A).acts f) ((pink k D).acts c)) :
    let F:= tensor G (bedtime k A f); let U:= tensor G (bedtime k D c); let P:=patron G (extracted S T W)
    let γ:= FreeResolvent.covariance G S T (pink k A); let K:= tensor G (Precision.K ((pink k A).acts f))
    K * (F - (P*U*Pᵀ + γ)) * K=0 := by
  classical
  intro F U P γ K
  let r:= S.kernel.penalty; let M:= (pink k A); let L:= tensor G (Precision.K ((pink k D).acts c)); let R:= patron G (Precision.probe S)
  have hu : K*F*K=K := by unfold K F; rw [← tensor_times,← tensor_times,snaps hk hj]
  have hv : L*U*L=L := by unfold L U; rw [← tensor_times,← tensor_times,snaps hk hn]
  have he : Kᵀ=K := by unfold K; rw [tensor_transpose,k_symmetric (heart_inverse _ hk hj A f).2.1]
  have hi : Lᵀ=L := by unfold L; rw [tensor_transpose,k_symmetric (heart_inverse _ hk hn D c).2.1]
  have hp : K*P=Rᵀ*L := by
    unfold K P R L; rw [tensor_same, tensor_same, tensor_transpose,← tensor_times,← tensor_times, (stationed T W _ _ h).2]
  have hP : Pᵀ*K=L*R := by rw [← he, ← Matrix.transpose_mul]; rw [hp,transpose_mul,hi,transpose_transpose]
  have ht : K*(P*U*Pᵀ)*K=Rᵀ*L*R:= calc
    _ = (K*P)*U*(Pᵀ*K) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hp,hP]; calc
                  _ = Rᵀ*(L*U*L)*R := by simp only [Matrix.mul_assoc]
                  _ = _ := by rw [hv]
  let N:= fullMatrix G S M
  have ha : N=K+r • (Rᵀ*R) := by
    unfold N fullMatrix baseMatrix; rw [← tensor_same,patron_add,patron_scale, patron_mul, patron_star, tensor_same G (Precision.K _)]
  have hx : K*γ*N=K := by
    apply matrix_eq; intro v
    rw [← mulVec_mulVec, ← mulVec_mulVec, show γ *ᵥ (N*ᵥ v) =_ from sprig_eq S T _ H v,representative,mulVec_add]
    rw [gradient,mulVec_mulVec]
    have hm : K*tensor G (d 0 f)=0 := by unfold K; rw [← tensor_times,K_kills,tensor_clear]
    rw [hm,zero_mulVec,add_zero]
  have hm : r • (γ*Rᵀ) = P := linear_mean S T H.isUnit h
  have hz : r • (K*γ*(Rᵀ*R))= Rᵀ*L*R := by
    calc
      _ = K*(r • (γ*Rᵀ))*R:= by simp only [Matrix.mul_assoc,Matrix.mul_smul,Matrix.smul_mul]
      _ = _ := by rw [hm,hp]
  rw [ha,Matrix.mul_add, Matrix.mul_smul,hz] at hx
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_add,Matrix.add_mul,ht,hu]
  exact sub_eq_zero.mpr (hx.symm.trans (add_comm ..))

/-- Exact form of harmonic column: constant on initial site. -/
lemma daytime (c : Side) (G : Gauge) (x y : Site c) (i j) :
    let F:= tensor G (haloMat c)
    F (x,i) j=F (y,i) j := by
  intro F; simp only [F,tensor,haloMat,Matrix.of_apply]; split
  · exact (halo_show c x _ _ _).trans (halo_show c y _ _ _).symm
  rfl
lemma eminence (G : Gauge) (c : Side) {k : ℝ} (v : Train j) (hk : 0<k) (hj : 4 ≤ j) :
    ∃ J, 1 - tensor G (bedtime k v c) * tensor G (Precision.K ((pink k v).acts c)) =
      tensor G (d 0 c)*J+tensor G (haloMat c) := by
  obtain ⟨J,H⟩:= shipped hk hj v c
  refine ⟨tensor G J,?_⟩
  rw [← tint_fund G c 1,← tensor_times,← tensor_less,H,← tensor_times]; rw [← tensor_same,patron_add]; rw [tensor_same, tensor_same]
end YM.RG08.Drift
