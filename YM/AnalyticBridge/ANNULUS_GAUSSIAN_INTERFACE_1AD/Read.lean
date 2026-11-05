import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Jets

/-!
# Local broad protects the actual tilted input

Prove Window.charts for the selected Gaussian slots near these seeds,
from only the retained halo's Wide and regular broad doors. Compare
in oriented V stencils. Even *frozen* inputs agree there (not everywhere):
Cleans_at buys the true relative logs once the profiles/tests held
actually pass. Thus can use on an intact sector or when dropping other
defaults in a formal sector with the same A. . d is
a post-L sufficiently broad choice (must reprice if using some previously
purchased Cosmos; do not infer our d lower bound from those).
-/
set_option autoImplicit false
-- Only stylistic lint disabled. All holes/axioms/declaration safety audited at entry.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.AnalyticBridge.Annulus1AD
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube MeasureTheory Tree
   Axial YM.Push.SectorMeasure Next.Fluctuations Metric Oriented Presented Exterior Bloch
open YM.Next.SectorChange YM.SectorNext.Remainder
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
open Finset Affine

variable {G : Gauge} {c f n : Side} {S : StepData c f}

/-- Both-endpoint halo location rule (meaning: min endpoint distance). -/
def witnesses (O : Stores S) (R : ℕ) (i : Bond f) :=
    S.ratio.parent i.1∈O.dome R ∨ S.ratio.parent (i.1 + step i.2)∈O.dome R

def locals (A O : Stores S) (x : ℝ) (F : Forest S.ratio) (R : ℕ) : Finset (Active A x F) :=
  univ.filter fun i => witnesses O R i.val.val

def admitsHere (A O : Stores S) (x : ℝ) (F : Forest S.ratio) (q : Chi) (d : ℝ)
    (y : LogArray G (Active A x F)) (R : ℕ) := ∏ i∈locals A O x F R, broad q d (y i)

lemma doors_here {A O : Stores S} {x : ℝ} {F : Forest S.ratio} {q : Chi} {d : ℝ} {y : LogArray G (Active A x F)} {R : ℕ}
    (h : admitsHere A O x F q d y R ≠ 0) {i : Active A x F} (hi : S.ratio.parent i.val.val.1∈O.dome R) :
    broad q d (y i) ≠ 0 := by
  intro he
  have hi : i∈locals A O x F R := mem_filter.mpr ⟨mem_univ _,Or.inl hi⟩
  exact h (Finset.prod_eq_zero hi he)

section held

variable (x : ℝ) (A : Stores S) (F : Forest S.ratio) (q : Chi) (d : ℝ) (V : Config G c)
    (Y : LinkArray G (Frozen A x F)) (a : Prices G (Active A x F))

/-- Keep the full physical evaluation through the same tree (even after
packet extraction-- don't change the Gaussian integration variables). -/
-- avoid Remainder.physical
abbrev landed := Next.SectorChange.physical A F V Y (tape a)

lemma wood (i : Bond f) (h : i∈F.trunks) : basisArray x A F q d V Y a i=0 := by
  simp [basisArray,Rows.input,Rows.fresh,h]

lemma held_physical (i : Frozen A x F) : landed x A F V Y a i.val.val=Y i := by
  refine Eq.trans (F.off_tree (thaw F (chill A x F) (replica S.ratio V) Y (tape a)) i.val) ?_
  exact freeze_held ..
lemma held_basis (i : Frozen A x F) : basisArray x A F q d V Y a i.val.val=
    patched q d (Y i*(replica S.ratio V i.val.val)⁻¹) := by
  obtain ⟨⟨i,hi⟩,he⟩ := i; simp [basisArray,Rows.input,Rows.fresh,autoShell,hi,he]

lemma clear_physical (i : Active A x F) : landed x A F V Y a i.val.val=
    G.lieExp (tape a i)*replica S.ratio V i.val.val := by
  refine Eq.trans (F.off_tree (thaw F (chill A x F) (replica S.ratio V) Y (tape a)) i.val) ?_
  exact freeze_regular ..
lemma clear_basis (i : Active A x F) : basisArray x A F q d V Y a i.val.val=tape a i := by
  obtain ⟨⟨i,he⟩,hi⟩ := i; simp [basisArray,Rows.input,Rows.fresh,he,hi]

variable (s : Signed)

lemma pass_link {U U' : Config G n} {i : Bond n} {s : Signed} (h : U (sendEdge s 0 i)=U' (sendEdge s 0 i)) :
    pull s 0 U i=pull s 0 U' i := by rw [Motion.turn_read,Motion.turn_read,h]

lemma pass_array {U : Config G n} {b l : Directions G n} {i : Bond n} {s : Signed} (h : b (sendEdge s 0 i)=l (sendEdge s 0 i)) :
    Motion.inChannel s U b i= Motion.inChannel s U l i := by rw [Motion.in_eval,Motion.in_eval,h]

lemma shell_flip (s : Signed) (V U : Config G n) (i : Bond n) :
    patched q d ((pull s 0 U i)*(pull s 0 V i)⁻¹) = Motion.inChannel s V (fun j => patched q d (U j*(V j)⁻¹)) i := by
  rw [Motion.turn_read,Motion.turn_read,Motion.in_eval]; split
  next he =>
    let u := U (sendEdge s 0 i); let v := V (sendEdge s 0 i)
    change patched q d (u⁻¹*(v⁻¹)⁻¹) = (-G.adjoint v⁻¹) (patched q d (u*v⁻¹))
    rw [show u⁻¹*(v⁻¹)⁻¹=v⁻¹*(u*v⁻¹)⁻¹*(v⁻¹)⁻¹ by group,patched_covary,patched_inv,LinearMap.neg_apply,map_neg]
  rfl

lemma held_flow (i : Bond f) (e : Frozen A x F) (h : sendEdge s 0 i=e.val.val) :
    let U := pull s 0 (landed x A F V Y a)
    signedArray x A F q d V Y a s i = patched q d (U i*(replica S.ratio (pull s 0 V) i)⁻¹) := by
  intro U
  unfold signedArray U; rw [replica_turn _ S.patch.odd_side,shell_flip q d s]
  apply pass_array; rw [h]; rw [held_basis x A F q d V Y a e,held_physical x A F V Y a e]

end held

section read
variable {x K L : ℝ} {A O : Stores S} {N r : ℕ} {F : Forest S.ratio}

lemma far_locate {s : Signed} (i : Bond f) {p : Site c} (hB : 1≤radiusB x) (he : separation p (S.ratio.parent i.1) ≤ thin x)
    (hp : p∈(turnStore s O).dome (N*radiusB x)) : S.ratio.parent (sendEdge s 0 i).1∈O.dome ((N+2)*radiusB x) := by
  obtain ⟨z,hz,hz'⟩ := halo_spec.mp ((dome_turn s O _ _).1 hp)
  refine halo_spec.mpr ⟨z,hz,(separation_triangle _ (s.act p) _).trans ?_⟩
  apply (Nat.add_le_add hz' (spin_separation (S:=S) i s p)).trans
  unfold thin at he
  rw [Nat.add_mul]; omega

set_option maxHeartbeats 400000 in
/-- Read on a single inSweep row's whole local stencil using the
actual input array passed to the Gaussian jet, not just the existence of
some small displacement. In this statement d=L*t, K≤L. Even if the
frozen input is large elsewhere, no assumption that the shell logarithm
continues a true log there (use actual Cleans facts only here).
-/
lemma preview (q : Chi) (V : Config G c) (Y : LinkArray G (Frozen A x F)) (a : Prices G (Active A x F))
    (h : 0<L*fiery G x S.patch.L) (hL : K≤L) (hr : L*fiery G x S.patch.L<firstRadius G)
    (hd : 1≤radiusB x) (hs : 1≤K) (hN : (N+2)*radiusB x≤r)
    (hv : admitsHere A O x F q (L*fiery G x S.patch.L) (tape a) r≠0) (s : Signed)
    (p : Site c) (hi : inSweep (turnStore s O) (turnStore s A) N (radiusB x) p)
    (u : Directions G f) (he : Cleans (S:=S) K x (pull s 0 (landed x A F V Y a)) (pull s 0 V) p u) :
    let U := landed x A F V Y a
    PatchInputs (S:=S) (pull s 0 U) (pull s 0 V) (signedArray x A F q (L*fiery G x S.patch.L) V Y a s) (2*L) x p := by
  let t:=fiery G x S.patch.L; let d:=L*t
  intro U i hl; let Wf:=replica S.ratio (pull s 0 V)
  let j:=sendEdge s (0:Site f) i; let b:=replica S.ratio V
  let wet:=signedArray x A F q d V Y a s; let dry:=basisArray x A F q d V Y a
  have h1 : 0≤t := temp_nonneg _
  have h2 : 0≤L := by linarith
  have hm : replica S.ratio (pull s 0 V)=pull s 0 b := replica_turn _ S.patch.odd_side ..
  have pass (eq : U j = increment b dry j) : pull s 0 U i = increment Wf wet i := by
    unfold Wf; rw [hm]
    change _=increment (pull s 0 b) (Motion.inChannel s b dry) i
    rw [← Motion.mount]; exact pass_link eq
  change pull s 0 U i = increment Wf wet i ∧ ‖wet i‖ ≤ (2*L)*t
  by_cases hx : j∈F.trunks
  · have hy : dry j=0 := wood x A F q d V Y a _ hx
    have he : b j=1 := if_pos (F.trunk_internal hx)
    have hq : U j=1 := F.on_tree (thaw F (chill A x F) b Y (tape a)) ⟨j,hx⟩
    refine ⟨pass ?_,?_⟩
    · unfold increment; rw [hy,he,hq,G.mat_lieExp_zero,one_mul]
    change ‖Motion.inChannel _ _ dry _‖ ≤ _
    rw [Motion.in_size]
    change ‖dry j‖ ≤ _; rw [hy,norm_zero]; positivity
  let e : F.Free := ⟨j,hx⟩
  by_cases ht : chill A x F e
  · let v : Frozen A x F := ⟨e,ht⟩
    have hh := he.chart i hl
    obtain ⟨hU,ha,hb⟩ := hh
    have hh : ‖u i‖ ≤ d := ha.trans (mul_le_mul_of_nonneg_right hL h1)
    have hw : wet i=u i := by
      have he := held_flow x A F q d V Y a s i v (show sendEdge s 0 i=v.val.val from rfl)
      dsimp only at he
      rw [hU] at he
      simp only [increment, mul_inv_cancel_right] at he
      exact he.trans (patched_agrees _ h hr hh)
    constructor
    · unfold increment at hU ⊢; rw [hw]; exact hU
    rw [hw]; apply ha.trans; exact mul_le_mul_of_nonneg_right (by linarith) h1
  let v : Active A x F := ⟨e,ht⟩
  have hb : S.ratio.parent j.1∈O.dome r := farther hN (far_locate i hd hl hi.2)
  obtain hw := doors_here hv (i:=v) hb
  refine ⟨pass ?_,?_⟩
  · unfold increment; have he : dry j=tape a v := clear_basis x A F q d V Y a v
    rw [he]; exact clear_physical x A F V Y a v
  change ‖Motion.inChannel _ _ dry _‖ ≤ _
  rw [Motion.in_size]; change ‖dry v.val.val‖ ≤ _; unfold dry
  rw [clear_basis x A F q d V Y a v,mul_assoc]; exact (broad_span q h _ hw).le

end read
end YM.AnalyticBridge.Annulus1AD
