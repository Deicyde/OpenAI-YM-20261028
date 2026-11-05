import YM.FullVolume.Rent

/-! Pack an arbitrary word with literal rootTest estimates across all slots.
Only separation in ONE direction required for any pair. No cumulative-order
restrictions at ties. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Filter Set MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Cells
open Push Push.RelayDifference
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {C : Family G} {n : Side} {d m k N p : ℕ}

lemma turned (F : Config G n→ℂ)(q:Signed)(b:Bool) : literal (fun x=> oriented F b q x):=by
  intro o x; funext U; change _= oriented F b q o (translate x U); simp [RelayDifference.oriented,←pull_one,pull_pull,affine]

lemma staff {h : k ≤ N} (T : Tiling (C.side N p)) (X : Trial C) {u : ℝ} (hm:C.Makes)
    (ht : Cells.span C.S h p ∣ T.side.val) (hs : literal (X N p)) (v:T.Cell) (y)
    (he : y∈ T.margin v (3* Cells.span C.S h p))
    (hF : Interior ((center C.S p h 0).chamber 0) (X N p 0)) (hh : (center C.S p h 0).rootTest (C.beta N p) (X N p 0) ≤ u):
    ∃ F : Config G (C.side N p) → ℂ,T.copy v F=X N p y ∧ Interior (T.chamber 0) F∧ T.rootTest (C.beta N p) F ≤ u:=by
  classical
  obtain ⟨x,hx⟩:= T.pointed v y
  let b:= decide (T.hand v); let q:= (T.omega v)⁻¹; let P:=X N p 0; let Y (x : Site (C.side N p)):= oriented P b q x
  have hz : diag q:=diag_inv (show diag (T.omega v) from rfl)
  have hY : Interior ((center C.S p h 0).chamber 0) (Y 0):= center_interior h q hz b _ hF
  have hk: (center C.S p h 0).rootTest (C.beta N p) (Y 0) ≤ u := (center_price h 0 P b q hz hF _).trans_le hh
  have hj := RelayDifference.offset h T _ _ ht (turned P q b) (seamless hm N p) hY hk ((T.reflected_margin x ..).2 (hx.symm ▸ he))
  refine ⟨Y x,?_,hj⟩; unfold Y; rw [RelayDifference.copied]
  simpa only [b,Bool.xor_self,hx,q,mul_inv_cancel] using!
    (show oriented P false 1 y=X N p y from (unorient hs y).symm)

/-- Include the SAME-law measure in every slot. -/
def word (F : Fin m→Trial C) (i : Cutoffs) (x : Fin m→Site (C.side i.1 i.2)) :=
    moment (C.beta i.1 i.2) (fun U => ∏ j, F j i.1 i.2 (x j) U)

def spaceout (C : Family G)(r : ℝ)(i:Cutoffs)(x : Fin m→ Site (C.side i.1 i.2)) := ∀ u v:Fin m, u≠v → r ≤ C.S.a i.1 * separation (x u) (x v)

lemma cohort (h : C.Makes) (F : Fin m→Trial C) {u : Fin m→ ℕ → Cutoffs → ℝ} (hu: ∀ i, Affords (F i) (u i)) {r:ℝ} (hr:0<r):
    ∀ᶠ k in atTop, ∀ᶠ i in mesh, ∀ z, spaceout C r i z → ‖word F i z‖ ≤ ∏ j,u j k i:=by
  obtain ⟨l,hl⟩:= (C.S.shrinks.eventually (gt_mem_nhds hr)).exists
  have hv:∀ᶠ k in atTop,(m:ℝ)*(2*(3*C.S.a k)) < C.S.a l := by
    refine ((C.S.shrinks.const_mul (3:ℝ)|>.const_mul (2:ℝ)|>.const_mul (m:ℝ)).eventually (gt_mem_nhds (lt_of_eq_of_lt ?_ (C.S.a_pos _))))
    simp
  have hX j:∀ᶠ i in mesh, literal (F j i.1 i.2):= by
    obtain ⟨X,hX⟩:= (hu j).1; exact hX.mono (fun _ h=> h.translates)
  filter_upwards [hv, eventually_all.mpr (fun j=> (hu j).2), eventually_ge_atTop l] with k hk hi ht
  filter_upwards [eventually_all.mpr hi,eventually_all.mpr hX,deepen.eventually_ge_atTop k] with i hg hx he z hZ
  let N:=i.1; let p:=i.2; let T:= center C.S i.2 (ht.trans he) 0; let t:= Cells.span C.S he i.2
  have hs : C.S.a N * t = C.S.a k := C.S.embeds_scale (C.S.toDepth he p)
  have hv' : C.S.a N * ↑T.side.val = C.S.a l := C.S.embeds_scale T.units
  have hp : m * (2*(3*t)) < T.side.val := by
    apply (Nat.cast_lt (α:=ℝ)).mp; apply lt_of_mul_lt_mul_left _ (C.S.a_pos N).le
    rw [hv']; rw [←hs] at hk; push_cast; linarith only [hk]
  obtain ⟨o,ho⟩:= T.fits_together z (3*t) (by exact Nat.mul_pos (by decide) (C.S.toDepth he i.2).count.property) hp
  let X:= T.newly o; let P (j:Fin m):= X.which (z j)
  have hQ(j:Fin m): z j∈ X.margin (P j) (3*t):=ho j
  have hP: Injective P:=by
    intro j j' hh; by_contra H
    have hf:=X.extent (v:=P j) (x:=z j) (y:=z j') ((hQ j).1) (hh.symm ▸ (hQ j').1)
    have ht: r≤ C.S.a l:= (hZ j j' H).trans (le_trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hf) (C.S.a_pos N).le) hv'.le)
    exact hl.not_ge ht
  choose f hf H h' using fun j:Fin m=> staff X (F j) h (Around.inherits ht he) (hx j) (P j) (z j) (hQ j)
    ((hg j).choose_spec.1) ((hg j).choose_spec.2)
  have hu:= X.planted (seamless h ..) P hP f H; simp_rw [hf] at hu
  exact hu.trans (Finset.prod_le_prod (fun j _ => X.root_nonneg _ _) (fun i _=>h' i))

theorem financed (h:C.Makes) (F:Fin m→ Trial C)(hp:∀ j,Funded (F j)){r:ℝ}(hr:0<r):∃ v:ℝ,
    ∀ᶠ i in mesh, ∀ x, spaceout C r i x → ‖word F i x‖ ≤ v:=by
  choose u hu using hp
  obtain ⟨k,hk⟩:= (cohort h F hu hr).exists; exact ⟨_,hk⟩
end YM.FullVolume
