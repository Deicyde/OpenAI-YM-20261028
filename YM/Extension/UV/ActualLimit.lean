import YM.Extension.UV.ActualTree
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.Linear
open Set Function Filter Lattice Laurent Exterior Bloch Metric Matrix Precision RG Next.Free
open scoped Topology BigOperators
variable {G:Gauge} {A:Levels G}

lemma tendsto_matrix_mul {ι α κ ν S : Type*} [Fintype κ] [NonUnitalNonAssocSemiring S] [TopologicalSpace S] [ContinuousAdd S] [ContinuousMul S] {l : Filter ι}
    (F:ι→Matrix α κ S) (U:ι→Matrix κ ν S) {f u} (h:Tendsto F l (𝓝 f)) (h':Tendsto U l (𝓝 u)): Tendsto (fun i=>F i * U i) l (𝓝 (f*u)) := by
  apply tendsto_pi_nhds.mpr; intro a; apply tendsto_pi_nhds.mpr; intro b
  simp only [Matrix.mul_apply]; apply tendsto_finsetSum
  intro c _; apply Tendsto.mul
  · exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h a) c
  exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h' c) b

set_option maxHeartbeats 300000 in
lemma raw_tendsto (h:SizeFloor A.clock.kernel.penalty A) (m p : ℕ) : ∃ v, Tendsto (fun n=>rawH A n m p) atTop (𝓝 v) := by
  let k := A.clock.kernel.penalty
  let L := A.S.side m p
  let S := fun n=>record (pulse k (location A n m))
  let R := rotations L (TypeFace 2)
  choose x y hP hV using fun i : Site L=> pulse_vault_limits k A.clock.kernel.penalty_pos A h m (mon_mem L i)
  have hh n : approached ((S n).acts L) * R = R * fiber (fun i=>pulse k (location A n m) (mon i)) := by
     have hu := (heart_true k A.clock.kernel.penalty_pos (A.clock.adm m) (location A n m)).1
     rw [circulant _ _ hu.safe]
     congr! 3 with i
     exact hu.echo _ (mon_mem L _)
  have hf : Tendsto (fun n=>fiber (fun i : Site L=>pulse k (location A n m) (mon i))) atTop (𝓝 (fiber x)) := by
     unfold fiber
     apply tendsto_pi_nhds.mpr; rintro ⟨a,b⟩; apply tendsto_pi_nhds.mpr; rintro ⟨a',b'⟩
     simp only [Matrix.of_apply]
     split_ifs with he; exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (hP a) _) _
     exact tendsto_const_nhds
  have he := tendsto_matrix_mul _ (fun _ : ℕ=>star R) (tendsto_matrix_mul _ _ (tendsto_const_nhds (x:=R) (f:=atTop)) hf) (tendsto_const_nhds (x:=star R) (f:=atTop))
  have H n : (approached ((S n).acts L) * R) * star R =(L.val:ℂ)^4 • approached ((S n).acts L) := by change (_ * rotations L _) * star (rotations L _) = _; rw [Matrix.mul_assoc,rotations_gram,Matrix.mul_smul,Matrix.mul_one]
  simp_rw [← hh,H] at he
  let B := ((R * fiber x) * star R)
  have he' (a b) : Tendsto (fun n=>(L.val:ℂ)^4 * approached (rawH A n m p) a b) atTop (𝓝 (B a b)) := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp he _) _
  refine ⟨fun i j=> ((B i j)*((L.val:ℂ)^4)⁻¹).re,?_⟩
  apply tendsto_pi_nhds.mpr; intro a; apply tendsto_pi_nhds.mpr; intro b
  have hu n : rawH A n m p a b = Complex.re (((L.val:ℂ)^4 * approached (rawH A n m p) a b) * ((L.val:ℂ)^4)⁻¹) := by field_simp; rfl
  exact Tendsto.congr' (Eventually.of_forall (fun n=> (hu n).symm)) (Complex.continuous_re.continuousAt.tendsto.comp ((he' a b).mul_const _))
lemma K_tendsto (M:Horizon A) {P : MapPrices} (hp:M.Suffices P) (h:SizeFloor A.clock.kernel.penalty A) (m p : ℕ) : ∃ k, Tendsto (fun n=>Kactual M n m p) atTop (𝓝 k) := by
  obtain ⟨w,hw⟩ := raw_tendsto h m p
  refine ⟨Precision.K w,?_⟩
  have hh : (fun n=> Precision.K (rawH A n m p)) =ᶠ[atTop] (fun n=> Kactual M n m p) := by filter_upwards [eventually_ge_atTop m] with n hn; exact (K_formula hp n m p hn).symm
  exact Tendsto.congr' hh (tendsto_matrix_mul _ _ (tendsto_matrix_mul _ _ tendsto_const_nhds hw) tendsto_const_nhds)
end YM.Extension.UV.Linear
