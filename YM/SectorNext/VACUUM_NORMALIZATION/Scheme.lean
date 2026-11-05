import YM.SectorNext.VACUUM_NORMALIZATION.ForestLine


/-!
# Legal rows for the (not yet produced) no-hole affine Gram

Probe and d1 are the library's actual kinetic rows. Works with any
further linear combinations including the prescribed cutoff ell^U
matrix multiplication at flat, provided with true real coefficients &
all physical keys (cuts/tag invariance of *choosing* these inputs still
a sector producer). Doesn't give any nonlinear/legal model for varying
backgrounds. Besides this reusable test for , apply true hessian
receipts from F05 on the actual Kin compatible with the SAME chart &
compute also that no-tree-cost equality. Keep two determinants SEPARATE.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum.FlatTree
open Lattice Tree RG Wilson Precision Matrix Filter Function Exterior Bloch
open scoped Matrix.Norms.Frobenius BigOperators Topology Classical ContDiff
variable {c f : Side} (S : StepData c f) (F H : Forest S.ratio)
variable (I : Type*) [DecidableEq I] [Fintype I] {X Y : Type*}
  {G : Gauge} {n : Side}

/-- Tensor with identity on colors. (Kronecker convention, edge index
instead of exterior Body) -/
def lined (D : Matrix X (Body 1 n) ℝ) : Matrix (X×I) (AllKeys I n) ℝ := of fun a b => if b.2 = a.2 then D a.1 (b.1.1,coord b.1.2) else 0

def wheel (n : Side) : Edge (Site n) ≃ Body 1 n := Equiv.prodCongr (Equiv.refl _) axisEquiv

@[simp] lemma wheel_app (n : Side) (e : Edge (Site n)) : wheel n e=(e.1,coord e.2) := rfl

def below (D : Matrix X (Body 1 f) ℝ) := ∀ j (v : Site f → ℝ), (∀ i : Site c,v (S.ratio.embed i)=0) →
    (D *ᵥ (Exterior.d 0 f *ᵥ fun x : Body 0 f=>v x.1)) j=0

omit [Fintype I] in
lemma native_below (D : Matrix X (Body 1 f) ℝ) (hv : below S D) : negatives (lined I D) S.ratio := by
  intro j k v hi
  unfold lined; by_cases h : k=j.2; swap; simp [h]
  simp only [Matrix.of_apply, h, if_true]
  have he := hv j.1 v hi
  unfold mulVec dotProduct at he
  rw [← Equiv.sum_comp (wheel f) _] at he
  have ht (i : Edge (Site f)) : (fun j_1 => d 0 f (wheel f i) j_1) ⬝ᵥ (fun x => v x.1) = -climb v i := by
    rw [wheel_app]
    change (d 0 f *ᵥ fun (i : Body 0 f) => v i.1) _ = _
    rw [d_sites]; unfold climb; ring
  change ∑ x : Edge (Site f), D j.1 (wheel f x)*((d 0 f (wheel f x)) ⬝ᵥ (fun i : Body 0 f=>v i.1))=0 at he
  simp_rw [ht,wheel_app,mul_neg,Finset.sum_neg_distrib,neg_eq_zero] at he
  exact he

-- Arbitrary flat linear combinations (including truncated row stacks
-- without all-period metric identification).




-- In channels that have not been expressed back in primary Body coords
-- as that same form, pull the ROOT ADDITIVE potentials instead. -
def swing (s : Signed) (v : form 1 f) (i : Body 1 f) :=
    let p := posDir (axisEquiv.symm i.2); let w := p.rotate s
    beam (K:=ℝ) (fun e : Edge (Site f)=> v (e.1,coord e.2)) w (affine s 0 i.1)

lemma swing_climb (s : Signed) (v : Site f → ℝ) : swing s (d 0 f *ᵥ (fun x=> v x.1)) =
    d 0 f *ᵥ (fun x=> v (s.act x.1)) := by
  funext i; obtain ⟨x,i⟩ := i
  obtain ⟨j,rfl⟩ := axisEquiv.surjective i
  let p := (posDir j).rotate s
  have he : s.act ((x+step j) : Site f) = s.act x + (p.vec : Site f) := by rw [Signed.act_add,Step.vec_rotate,Step.vec_pos]
  simp only [swing,coord_map,d_sites,beam,affine,add_zero]
  rw [he]; simp only [show axisEquiv.symm (coord j)=j from axisEquiv.symm_apply_apply _]
  generalize pL : (posDir j).rotate s = q; unfold p; rw [pL]
  cases q with | mk k b=> cases b <;> simp [Step.used, Step.vec,sub_eq_add_neg]

/-- In particular signed versions of the allowed rows. Root disposition
explicit; doesn't claim .S.recipe is symmetric nor paid from Floors only. -/
lemma turns (D : Matrix X (Body 1 f) ℝ) (s : Signed) (Q : Matrix X (Body 1 f) ℝ)
    (h : ∀ v : form 1 f, Q*ᵥ v = D *ᵥ swing s v) (hD : below S D)
    (hR : ∀ i : Site c, ∃ j,s.act (S.ratio.embed i) = S.ratio.embed j) : below S Q := by
  intro i v hr; rw [h,swing_climb]; exact hD i (fun i=>v (s.act i)) fun k=> by obtain ⟨j,hj⟩ := hR k; exact hj.symm ▸ hr j


/-! A different determinant, from Kin.Planned at identity. Do not
convert self-energy by identifying it with scatter.
-/


end YM.SectorNext.Vacuum.FlatTree
