import YM.Pert.Parity.Fields
import YM.Pert.Position.Crest
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 320000
noncomputable section
/-! Involution on ledgers and admissible frame generators (linearized, over the reals). -/
namespace YM.Pert.Parity
open Labels Position Full Maxwell RawLabels Function Set Filter Topology
open scoped Topology Classical
variable {G : Gauge} {d : ℕ} (F : Frames G)
def jL (F : Frames G) (d) : E F d →L[ℝ] E F d := (Coat F d |>.restrictScalars ℝ).toContinuousLinearMap
@[simp] lemma jL_eq (p) : jL F d p = Coat F d p := rfl
/-- On deviations from `1`. -/
lemma twice_mem (b : Buffer F d) : jL F d ∘L b.val ∘L jL F d ∈ buffers F d := by
  let Q := freeTable F
  refine ⟨?_,?_,?_,?_,?_⟩
  · change Coat F d (b.val (Coat F d ((freeTable F).unit d)))=0; rw [Coat_unit,b.property.1,map_zero]
  · have H (p : E F d) (i) : p∈lower F i d → Coat F d p∈lower F i d := fun hp=> by
      rw [← SetLike.mem_coe, ←stairs_eq,stair] at *; obtain ⟨q,rfl,hq⟩ := hp
      exact ⟨wash G d q,(Coat_inherit F q).symm, (wash G i ⟨q.val,hq⟩).property⟩
    intro e he x h; exact H (b.val (Coat F d x)) e (b.property.2.1 e he _ (H x e h))
  · intro p; simp only [ContinuousLinearMap.comp_apply,jL_eq,Coat_conj,b.property.2.2.1]
  · intro s p; simp only [ContinuousLinearMap.comp_apply,jL_eq,Coat_spin,b.property.2.2.2.1]
  intro p; simp only [ContinuousLinearMap.comp_apply,jL_eq,LinearMap.map_smul,b.property.2.2.2.2]

def twice (d): Buffer F d →ₗ[ℝ] Buffer F d where
  toFun b := ⟨_,twice_mem F b⟩
  map_add' x y := Subtype.ext (ContinuousLinearMap.ext fun p=> by simp [map_add])
  map_smul' r x := Subtype.ext (ContinuousLinearMap.ext fun p=> by simp [map_smul])
lemma twice_motor (b : Buffer F d) (v) : motor F (twice F d b) v= Coat F d (motor F b (Coat F d v)) := by simp only [motor,_root_.add_apply,map_add]; change v+_ = Coat F d (Coat F d v)+_;exact (congrArg₂ (·+·) (Coat_round F v) rfl).symm
lemma twice_twice (b : Buffer F d) : twice F d (twice F d b) = b := by
  apply Subtype.ext; apply ContinuousLinearMap.ext; intro p
  exact (by simp only [Coat_round] : Coat F d (Coat F d (b.val (Coat F d (Coat F d p))))=b.val p)
lemma twice_cont : Continuous (fun b : Buffer F d => twice F d b) := LinearMap.continuous_of_finiteDimensional (𝕜:=ℝ) (E:=Buffer F d) (F':=Buffer F d) (twice F d)

variable {F} {k : ℕ} (Q : Conditions F d k)
/-- Decode one row as a multilinear evaluation. -/
def menu (v : Ledger Q) (i : Fin Q.slots) : MultilinearMap ℂ (fun _ : Fin (Q.arity i)=>E F d) ℂ := ∑ z : inklet Q i, (MultilinearMap.mkPiRing ℂ _ (v i z) |>.compLinearMap (fun j=>(baring F d).coord (z j))) -- adjust scalar
lemma menu_def (v : Ledger Q) (i) (p) : menu Q v i p=decode Q v p := by simp [menu, decode, MultilinearMap.mkPiRing_apply]
lemma decode_map (i) (M : MultilinearMap ℂ (fun _ : Fin (Q.arity i)=> E F d) ℂ) (v : Ledger Q) (he : ∀ z, v i z=M (fun j=> baring F d (z j))) (u) : decode Q v (i:=i) u = M u := by
  conv_rhs=>rw [←funext (fun j=> (baring F d).sum_equivFun (u j))]
  rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ]; exact Finset.sum_congr rfl fun z _=> by rw [M.map_smul_univ]; rw [←he]; rfl
/-- Dual action on all rows, not assuming an eigenspace basis. -/
def pull : Ledger Q →ₗ[ℝ] Ledger Q where
  toFun v i z := decode Q v (i:=i) (fun j=> Coat F d (baring F d (z j)))
  map_add' a b := by ext i z; simp [decode,mul_add,Finset.sum_add_distrib]
  map_smul' r v := by ext i z; simp [decode, Complex.real_smul, mul_left_comm _ (↑r:ℂ),←Finset.mul_sum, RingHom.id_apply]

lemma pull_def (v : Ledger Q) (i : Fin Q.slots) (u) : decode Q (pull Q v) (i:=i) u = decode Q v (i:=i) (Coat F d ∘ u) := by
  rw [decode_map Q i ((menu Q v i).compLinearMap (fun _=>Coat F d)) _]; exacts [menu_def Q v i _, fun z=>(menu_def Q v i (fun j=>Coat F d _)).symm]
lemma pull_finite (L : Lattice.Side) (m j) : pull Q (finite Q L m j) = (-1:ℝ)^j • finite Q L m j := by
  ext i z
  change decode Q (finite Q L m j) (i:=i) (Coat F d ∘ (fun h=>baring F d (z h))) = (-1:ℝ)^j • PowerSeries.coeff j (Full.profile d (Q.arity i) F L m (Q.profiles i) (fun h=> baring F d (z h)))
  rw [decode_map Q i ((PowerSeries.coeff j).compMultilinearMap (Full.profile d (Q.arity i) F L m (Q.profiles i))) (finite Q L m j) (fun _=>rfl)]; change PowerSeries.coeff j (profile _ _ _ _ _ _ (_ ∘ _))= _; rw [profile_reflect F L (Q.profiles i) (fun h=> baring F d (z h)), PowerSeries.coeff_rescale, Complex.real_smul]; simp only [Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
lemma pull_curve (L m n t) : Position.curve (finite Q L m) n (-t) = pull Q (curve (finite Q L m) n t) := by
  unfold curve; simp only [map_sum,map_smul,pull_finite,smul_smul, ←mul_pow _ (-1:ℝ), mul_neg, mul_one]
end YM.Pert.Parity
