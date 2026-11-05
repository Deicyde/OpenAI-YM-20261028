import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Cincture
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Terminal

/-! # Dormant even outside manifest where matrix windows remain non-degenerate. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Corona
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a α β γ d η σ W s b μ : ℝ} {j : ℕ}
open Blaze Blaze.Vine
namespace Coat
variable (X : Coat T F)
def Noncrystal := ∀ i, IsUnit (X.shutter.principal X.plate i).det

variable (ha : X.Noncrystal) (hf : P.Funds S T)
include ha hf
lemma cold_pad_crys (i j : Tubular f G) (h : (¬ X.Hot i.1) ∨ (¬X.Hot j.1)) :
    X.kernelA i j=(1:Matrix ..) i j := by
  obtain ⟨Y,W,H,-⟩ := hf.feeds
  by_cases he : i∈X.shutter.take j
  swap
  · have hi : i≠j := fun hi => he (hi.symm ▸ X.shutter.here i)
    rw [kernelA,X.shutter.outside X.plate i j he]; simp [hi]
  let e : ↥(X.shutter.take j) ↪ Tubular f G := Embedding.subtype _
  let A := X.shutter.principal X.plate j
  have hz : ∀ x : ↥(X.shutter.take j), ¬ X.Hot (e x).1 → ∀ u : ↥(X.shutter.take j), A⁻¹ x u=(1:Matrix ..) x u := by
    intro x hn u
    have he' : A x = (1:Matrix ..) x := funext fun y => by
      change X.plate (e x) (e y)=(1:Matrix ..) _ _; rw [X.asleep (e x) hn H _]
      simp [Matrix.one_apply,e.injective.eq_iff]
    have ht : A*A⁻¹=1 := Matrix.mul_nonsing_inv _ (ha j)
    have hg : (A*A⁻¹) x u=((1:Matrix (↥(X.shutter.take j)) (↥(X.shutter.take j)) ℝ)*A⁻¹) x u := by rw [Matrix.mul_apply,Matrix.mul_apply]; simp_rw [he']
    rw [ht,one_mul] at hg; exact hg.symm
  let u : ↥(X.shutter.take j) := ⟨i,he⟩; let v : ↥(X.shutter.take j) := ⟨j,X.shutter.here j⟩
  change X.shutter.pad X.plate u.val j=_
  rw [X.shutter.inside]; change A⁻¹ u v=(1:Matrix ..) (e u) (e v)
  rcases h with h|h
  · rw [hz u h]; simp [Matrix.one_apply,e.injective.eq_iff]
  have hv : IsHermitian A⁻¹ := (X.balanced.submatrix _).inv
  rw [show A⁻¹ u v=A⁻¹ v u from by conv_lhs => rw [← hv.eq]; rw [conjTranspose_apply,star_trivial], hz v h]
  by_cases h : u=v
  · rw [h]; simp
  simp [Ne.symm h,e.injective.ne h]
lemma uniform_crys (i j : Tubular f G) (h : ¬ X.Hot i.1) : X.relating i j=(1:Matrix ..) i j := by
  unfold relating frameMean
  have hp := X.cold_pad_crys ha hf i j (Or.inl h); have hh := X.cold_pad_crys ha hf j i (Or.inr h)
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply]
  change _ • (X.kernelA i j+X.kernelA j i) = _
  rw [hp,hh, show (1:Matrix _ _ ℝ) j i=(1:Matrix ..) i j from by simp [Matrix.one_apply,eq_comm]]; simp only [smul_eq_mul]; ring
lemma colorless_crys (i j : Tubular f G) (h : ¬ X.Hot i.1 ∨ ¬ X.Hot j.1) :
    X.shreds i j=0 := by
  unfold shreds Window.flawed frameMean
  obtain ⟨u,v,H,-⟩ := hf.feeds
  let A := X.plate; let V := X.relating
  change (A*V-1) i j=0; rw [Matrix.sub_apply,Matrix.mul_apply]; apply sub_eq_zero.mpr
  rcases h with hi|hj
  · have he : A i=(1:Matrix ..) i := funext fun j => X.asleep i hi H j
    rw [show ∑ k,A i k*V k j=((1:Matrix (Tubular f G) (Tubular f G) ℝ)*V) i j by rw [Matrix.mul_apply]; simp_rw [he],one_mul]
    exact X.uniform_crys ha hf _ _ hi
  have he k : V k j=(1:Matrix ..) k j := by
    have ht : V.transpose=V := by rw [← show Vᴴ=V.transpose from by ext; simp]; exact Window.twin ..
    rw [show V k j=V j k from congr_fun (congr_fun ht j) k]; unfold V; rw [X.uniform_crys ha hf j k hj]
    simp only [Matrix.one_apply,eq_comm]
  rw [show ∑ k,A i k*V k j=(A*(1:Matrix (Tubular f G) (Tubular f G) ℝ)) i j by rw [Matrix.mul_apply]; simp_rw [he],mul_one]
  rw [show A i j=A j i from congr_fun (congr_fun X.toned _) _]; unfold A; rw [X.asleep j hj H]; simp only [Matrix.one_apply,eq_comm]

private lemma single_crys (k : ℕ) (v : Bond f) (p : Itinerary f (k+2))
    (h : combo v p (X.finale k) ≠ 0) : X.Hot v ∧ X.Hot (arrive v p) := by
  induction k generalizing v with
  | zero =>
    let j := Itinerary.next p
    let i := Itinerary.next (after p)
    have hx : combo v p (X.finale 0)= Pulse.Itinerary.restrict (-X.shreds) v j*(Pulse.Itinerary.restrict X.plate j i) := by
      rw [combo,combo,combo]; simp [finale,j,i]
    rw [hx] at h
    have hl := left_ne_zero_of_mul h; have hb := right_ne_zero_of_mul h
    have hi : X.Hot v ∧ X.Hot j := by
      have ht := not_or.mp (show ¬ (¬X.Hot v ∨ ¬X.Hot j) from by
        intro he; apply hl; ext x y
        change (-X.shreds) (v,x) (j,y)=0
        rw [Matrix.neg_apply, X.colorless_crys ha hf (v,x) (j,y) he, neg_zero])
      exact ⟨not_not.mp ht.1,not_not.mp ht.2⟩
    refine ⟨hi.1,?_⟩
    change X.Hot i
    by_contra ht
    apply hb
    obtain ⟨u,w,hp,-⟩ := hf.feeds
    ext x y
    change X.plate (j,x) (i,y)=0; rw [show X.plate (j,x) (i,y)=X.plate (i,y) (j,x) from congr_fun (congr_fun X.toned _) _,
      X.asleep (i,y) ht hp]
    simp [show i≠j from fun H => ht (H.symm ▸ hi.2)]
  | succ n ih =>
    rw [combo] at h
    have hl := left_ne_zero_of_mul h; have hb := right_ne_zero_of_mul h
    have he : (fun k : ℕ => X.finale (n+1) (k+1))=X.finale n := by funext k; simp [finale]
    rw [he] at hb
    refine ⟨?_, (ih _ (after p) hb).2⟩
    by_contra hx; apply hl; ext x y
    change X.finale (n+1) 0 (v,x) (_,y)=_
    rw [finale,if_pos (by omega), Matrix.neg_apply,X.colorless_crys ha hf (v,x) _ (Or.inl hx),neg_zero]; rfl

lemma emitting_crys (z : Air f G) (p : Ledger f 2) (h : X.qunique z p ≠ 0) :
    X.Hot p.2.1 ∧ X.Hot (arrive p.2.1 p.2.2) := by
  rcases p with ⟨n,v,l⟩; refine single_crys X ha hf n v l ?_; intro he
  apply h; unfold qunique circle; dsimp only; rw [he]; simp


lemma calm_crys (β : ℝ) (i : Tubular f G) (h : ¬ X.Hot i.1) : shimmer X β i=0 := by
  obtain ⟨u,v,H,-⟩:= hf.feeds
  have hz : leanB X i=0 := by simp [leanB,Matrix.mulVec,dotProduct,X.stays _ i h hf]
  have hh : well X i=0 := by simp [well,Matrix.mulVec,dotProduct,hz,fun j=> X.cold_pad_crys ha hf j i (Or.inr h), Matrix.one_apply]
  have he : (X.plate *ᵥ well X) i=0 := by
    rw [show (X.plate *ᵥ well X) i=((1:Matrix (Tubular f G) (Tubular f G) ℝ)*ᵥ well X) i by
        unfold Matrix.mulVec dotProduct; exact Finset.sum_congr rfl fun j _=> by dsimp only; rw [X.asleep i h H], Matrix.one_mulVec]; exact hh
  unfold shimmer; rw [Pi.smul_apply,Pi.add_apply, hz,he]; simp

omit ha hf in
lemma crystals {V : E→Config G c} {m : ℕ} (h : ∀ i j, ContDiffAt ℝ 0 (fun y=> (vary X (V y)).plate i j) x)
    (hr : Allow (vary X (V x)).plate (along S) m η β γ) : ∀ᶠ y in 𝓝 x,(vary X (V y)).Noncrystal := by
  apply eventually_all.mpr; intro i
  let A y:= X.shutter.principal (vary X (V y)).plate i
  have hv : ContinuousAt (fun y=> (A y).det) x := by
    apply (determinant (k:=0) (A:=A) ?_).continuousAt
    intro i j; exact h i.val j.val
  have hp : IsUnit (A x).det := isUnit_det_of_right_inverse ((hr.sub (Embedding.subtype (· ∈ X.shutter.take i))).initial.1)
  exact (hv.eventually_ne hp.ne_zero).mono fun y hy => IsUnit.mk0 _ hy
end Coat
end YM.ConnectedActivityE6
