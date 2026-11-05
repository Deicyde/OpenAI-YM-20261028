import YM.Next.FREE_KERNELS.Amend
import YM.Next.FREE_KERNELS.Pulled

/-! # Signed physical symmetry of metric evaluated on d₁-images -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid
open scoped Topology BigOperators ComplexConjugate
variable {j : ℕ}
variable (s : Signed) (k l : ℝ) (hk : 0<k) (hl : 0≤l) (hj : 4≤j) (v : Train j) (n : Side)

def address (n : Side) : Face (Per n) ≃ Body 2 n := Equiv.prodCongr (Equiv.refl _) plaqEquiv

def regime : Equiv.Perm (Face (Per n)) := Equiv.ofBijective (Face.send s 0) (Fintype.bijective_iff_injective_and_card _ |>.mpr ⟨Face.injective_send ..,rfl⟩)
include hk hj
lemma face_bill (x y : Face (Per n)) :
    let A := pink k v
    let E (x y) := A.acts n (address n x) (address n y)
    E x y * turned s x.2 * turned s y.2 = E (regime s n x) (regime s n y) := by
  intro A E; obtain ⟨x,p⟩ := x; obtain ⟨y,q⟩ := y
  by_cases h : p=q
  · subst q
    rw [mul_assoc,turned_sq,mul_one];
    obtain ⟨hv,-⟩ := pink_row s k hk hj v p p
    let a (x : Site n) := Face.lower (x,p) s 0
    let i := plaquette p; let m := plaquette (p.rotate s)
    change (∑' z, if y=x+wrap n z then A i i z else 0)=(∑' z, if a y=a x+wrap n z then A m m z else 0)
    rw [← (Signed.actEquiv (R:=ℤ) s).toEquiv.tsum_eq (fun z => if a y=a x+wrap n z then A m m z else 0)];
    refine tsum_congr fun z => ?_
    change _=if a y=a x + wrap n (s.act z) then A m m (s.act z) else 0
    have he : a y=a x + wrap n (s.act z) ↔ y=x+wrap n z := by
      have hf (v : Site n) : a v=s.act v+a 0 := by unfold a Face.lower atFace affine; simp [add_assoc]
      rw [hf,hf x,← wrap_signed,add_right_comm (s.act x),add_left_inj,← s.act_add]; exact s.act_injective.eq_iff
    rw [show A i i z=_ from hv z, if_congr he rfl rfl]
  have he (x y : Site n) (p q : PlaqAxes) (hp : p≠q) : E (x,p) (y,q)=0 := by
    obtain ⟨-,ha⟩ := pink_row s k hk hj v p q
    change (∑' z, if y=x+wrap n z then A (plaquette p) (plaquette q) z else 0)=_
    rw [show A (plaquette p) (plaquette q)=0 from ha fun hx => hp ((plaq_iff ..).mp hx)]; simp
  rw [he x y p q h]; change 0*_*_= E (_,p.rotate s) (_,q.rotate s)
  rw [he _ _ (p.rotate s) (q.rotate s) (fun hx => h ((PlaqAxes.transform s).injective hx))]; ring
lemma apply_bill (a b : form 1 n) :
    let H := Precision.K ((pink k v).acts n)
    dotProduct (reorient s a) (H*ᵥ(reorient s b))=dotProduct a (H*ᵥb) := by
  intro H; let K := (pink k v).acts n
  let d := d 1 n
  let r := regime s n
  let f (x y : form 1 n) (i j : Face (Per n)) := (d*ᵥx) (address n i) * K (address n i) (address n j) * (d*ᵥy) (address n j)
  have h (x y : form 1 n) : dotProduct x (H*ᵥy)=∑ i, ∑ j, f x y i j := by
    have hx : dotProduct x (H*ᵥy)=dotProduct (d *ᵥ x) (K *ᵥ (d*ᵥ y)) := by
      unfold H K Precision.K d; rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, dotProduct_mulVec,vecMul_transpose]
    rw [hx]; unfold dotProduct Matrix.mulVec; rw [← (address n).sum_comp]; apply Finset.sum_congr rfl; intro i _
    change (d*ᵥx) ((address n) i) * (∑ j, K (address n i) j * (d*ᵥy) j)=_
    rw [Finset.mul_sum,← (address n).sum_comp (fun j => (d*ᵥx) (address n i) * (K (address n i) j *(d*ᵥy) j))]; exact Finset.sum_congr rfl fun j _ => (mul_assoc ..).symm
  rw [h,h,← Equiv.sum_comp r (fun i => ∑ j, f a b i j)]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp r (f a b (r i))]; refine Finset.sum_congr rfl fun j _ => ?_
  have ht (i : Face (Per n)) (a : form 1 n) : (d*ᵥ reorient s a) (address n i)=turned s i.2 * (d*ᵥa) (address n (r i)) := rotations_d a s i.1 i.2
  have hh : K (address n i) (address n j)*turned s i.2*turned s j.2=K (address n (r i)) (address n (r j)) := face_bill s k hk hj v n _ _
  unfold f; rw [ht,ht,← hh]; ring

omit hj hk in
lemma pigment (G : Gauge) (a : Dir G n) (i : G.ColorIndex) : parts G 1 (pulled a s) i=reorient s (parts G 1 a i) := by
  funext b; unfold parts pulled reorient; dsimp only; split <;> simp

include hl in
lemma sworn_metric (B : Bed) (h : B.metric=amend k l v) (G : Gauge) : Sworn B n G := by
  intro s a b; unfold gaugeFiscal
  have hx : Precision.K (B.metric.acts n)=Precision.K ((pink k v).acts n) := by
    unfold Precision.K; rw [h,Matrix.mul_assoc,Matrix.mul_assoc]; rw [(obligations k l hk hl hj v n).2.2.1] -- projection structure
  rw [hx]; refine Finset.sum_congr rfl fun i _ => ?_; rw [pigment,pigment]; exact apply_bill s k hk hj v n (parts G 1 a i) (parts G 1 b i)
end YM.Next.Free
