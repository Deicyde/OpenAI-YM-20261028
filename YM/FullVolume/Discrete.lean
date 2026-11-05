import YM.FullVolume.Skein
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Set Filter MeasureTheory Lattice Wilson Cells Extraction Extraction.Lease Gaps Difference
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{n d:ℕ}

-- Positional difference: slot times axis
abbrev MotionIndex (n:ℕ) := Fin n × Axis

def drive (b:MotionIndex n): Positions n:= Pi.single b.1 (Lattice.step b.2)

/-- literal lattice kernel propagated on already chosen Family -/
def gKernel (C : Family G) (v : Fin n→ C.book.Token) (l:List (MotionIndex n))
    (N p:ℕ) : Positions n → ℂ := deltas (C.S.a N) (l.map drive) (lifted C N p v)

section increment
variable (F: Fin n→ Trial C) (i:Push.RelayDifference.Cutoffs)

def expose : Positions n→ℂ:=fun x=> word F i (wrap (C.side i.1 i.2)∘x)
private lemma reflects (j:Fin n)(f:Trial C)(x:Positions n) :
    expose (update F j f) i x = moment (C.beta i.1 i.2) (fun U => f i.1 i.2 (wrap _ (x j)) U *
      ∏ k∈Finset.univ.erase j,F k i.1 i.2 (wrap _ (x k)) U):=by
   unfold expose word; congr 1; funext U; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
   simp only [Function.update_self,Function.comp_apply]; congr 1; exact Finset.prod_congr rfl fun k hk=>by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
lemma actuate (H:∀ k x,Continuous (F k i.1 i.2 x)) (a:MotionIndex n):
    expose (update F a.1 (farther (F a.1) a.2)) i=delta (drive a) (C.S.a i.1) (expose F i):=by
  let t:= C.S.a i.1
  let j:=a.1; let k:=a.2
  ext x : 1
  let y:= x+drive a; let L:= Finset.univ.erase j
  let T U:= ∏ k∈L, F k i.1 i.2 (wrap _ (x k)) U; have hT:Continuous T:= continuous_finsetProd _ (fun k _=> H ..)
  let w:= wrap (C.side i.1 i.2) ∘ x; let P o := F j i.1 i.2 o; let I:=law G (C.side i.1 i.2) (C.beta i.1 i.2)
  rw [reflects,delta_at]; change _= (t:ℂ)⁻¹ * (expose F i y-expose F i x)
  have he' z: expose F i z=moment (C.beta i.1 i.2) (fun U=> (P (wrap _ (z j))) U * ∏ k∈L,F k i.1 i.2 (wrap _ (z k)) U):=by
    simpa only [Function.update_eq_self] using reflects F i j (F j) z
  rw [he',he']; unfold moment
  let A:= P (w j+step k); let B:=P (w j)
  have hy U:(∏ k∈L,F k i.1 i.2 (wrap _ (y k)) U)=T U:= Finset.prod_congr rfl fun u hu=>by
      have he:u≠a.1:= Finset.ne_of_mem_erase hu; simp only [y,Pi.add_apply,drive,Pi.single_eq_of_ne he,add_zero]
  simp_rw [hy]; rw [show wrap (C.side i.1 i.2) (y j)= w j+step k by simp [y,j,k,w,drive,wrap_step]]
  change (∫ U, (_* (A U-B U)) * T U ∂ I)= _ * ((∫ U,A U * T U ∂I)- (∫ U, B U*T U ∂I))
  simp_rw [mul_assoc,sub_mul]
  rw [integral_const_mul]; congr 1; exact integral_sub (continuous_integrable _ ((H ..).mul hT)) (continuous_integrable _ ((H ..).mul hT))
end increment

/-- Full assertion of unextracted *bounds*, all p, any finite list of physical
fields and finite differences requested beforehand. No loss at ties. -/
structure FixedBounds (C : Family G) : Prop where
    bounds (n : ℕ) (v : Fin n→ C.book.Token)(l:List (MotionIndex n))(r:ℝ) : 0<r→ ∃ B:ℝ, 0≤B ∧
      ∀ᶠ N in atTop, ∀ p:ℕ,∀ x:Positions n, spaceout C r (N,p) (wrap (C.side N p) ∘ x) → ‖gKernel C v l N p x‖ ≤ B

end YM.FullVolume
