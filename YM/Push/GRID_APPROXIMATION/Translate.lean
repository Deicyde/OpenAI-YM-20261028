import YM.Push.GRID_APPROXIMATION.Geometry
import YM.Work.B15

/-!
# Charge literal translates on the fixed h grid

Use reflected-oriented copies internally for the rooted chess estimates.
Both orientation and conjugation necessary. Does not force changing the
approximants at translated positions. Permutations of axes included. Link
seams only in centered-tiling assertions. No need for equivariance of the
label bases/candidate choices used to *get* the root estimates.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open Lattice Wilson Cells Filter Set MeasureTheory Function
open scoped Topology BigOperators

variable {G : Gauge} {n : Side}

private lemma tile_flip (T : Tiling n) (i : T.Cell) (s : Signed) (a : Axis) :
    (T.omega (s.act i)).flip (s.perm a)=(T.omega i).flip a := by
  simp only [Tiling.omega,Signed.act_at]
  split <;> simp

private lemma tile_cross (T : Tiling n) (i : T.Cell) (s : Signed) :
    T.omega (s.act i) * s = s*T.omega i := by
  refine Signed.ext ?_ ?_
  · rfl
  ext1 a; rw [Signed.mul_flip,Signed.mul_flip,tile_flip T i s]
  exact Bool.xor_comm ..

private lemma tile_hand (T : Tiling n) (i : T.Cell) (s : Signed) : T.hand (s.act i) ↔ T.hand i := by
  let A := ({a : Axis | (T.omega (s.act i)).flip a} : Finset _)
  let B := ({a : Axis | (T.omega i).flip a} : Finset _)
  have he : A=B.image s.perm := by
    ext a
    obtain ⟨b,rfl⟩ := s.perm.surjective a
    simp [A,B,tile_flip]
  change Odd A.card ↔ Odd B.card
  rw [he, Finset.card_image_of_injective _ s.perm.injective]

variable (S : Schedule) {h N p : ℕ} (hh : h≤N)

lemma copy_oriented (i : Site (S.side h p)) (s : Signed) (F : Config G (S.side N p) → ℂ) :
    (tilesAt S p hh).copy (s.act i) (F ∘ pull s 0) = (tilesAt S p hh).copy i F ∘ pull s 0 := by
  classical
  let T := tilesAt S p hh
  funext U
  change T.copy (s.act i) (F ∘ pull s 0) U=T.copy i F (pull s 0 U)
  simp only [Tiling.copy,Function.comp_apply]
  rw [pull_pull,pull_pull,tile_cross T i s]
  have he : T.translateBy (s.act i) = s.act (T.translateBy i) := by
    unfold T
    rw [tile_translate,tile_translate]; exact (S.toDepth hh p).signed i s
  simp [tile_hand,affine,he]

lemma root_oriented (β : ℝ) (s : Signed) (F : Config G (S.side N p) → ℂ)
    (he : Interior ((tilesAt S p hh).chamber 0) F) :
    (tilesAt S p hh).rootTest β (F ∘ pull s 0) = (tilesAt S p hh).rootTest β F := by
  let T := tilesAt S p hh
  have hv := moment_pull β s 0 (T.fullAt fun _ => F) (T.manyIntegral β _ fun _ => he)
  have ht (U : Config G (S.side N p)) :
      T.fullAt (fun _ => F ∘ pull s 0) U=T.fullAt (fun _ => F) (pull s 0 U) := by
    let e : T.Cell ≃ T.Cell := (s.actEquiv (R:=Per T.period)).toEquiv
    unfold Tiling.fullAt
    rw [← Equiv.prod_comp e (fun i => T.copy i _ U)]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact congr_fun (copy_oriented S hh i s F) U
  change ‖moment β (T.fullAt _)‖^_ = ‖moment β (T.fullAt _)‖^_
  rw [show T.fullAt (fun _ => F ∘ pull s 0)=T.fullAt (fun _ => F) ∘ pull s 0 from funext ht,hv]

private lemma hub_affine (s : Signed) : Set.MapsTo (affine (R:=Per (S.side N p)) s 0) ((tilesAt S p hh).chamber 0) ((tilesAt S p hh).chamber 0) := by
  rw [tiling_window]
  change MapsTo _ (window (anchor S p hh (0:Site (S.side h p))) ((S.toDepth hh p).count.val/2)) (window (anchor S p hh (0:Site (S.side h p))) ((S.toDepth hh p).count.val/2))
  rw [show anchor S p hh 0 = 0 from (S.toDepth hh p).root.map_zero]
  have he := window_affine (n:=S.side N p) (r:= (S.toDepth hh p).count.val/2) 0 0 s
  simpa only [affine,Signed.act_zero,zero_add] using he

lemma source_for_translate (i : Site (S.side h p)) (F : Config G (S.side N p) → ℂ)
    (he : Interior ((tilesAt S p hh).chamber 0) F) (β : ℝ) :
    ∃ W, (tilesAt S p hh).copy i W = F ∘ translate (anchor S p hh i) ∧
      Interior ((tilesAt S p hh).chamber 0) W ∧
      (tilesAt S p hh).rootTest β W = (tilesAt S p hh).rootTest β F := by
  let T := tilesAt S p hh
  let s := T.omega i
  let Z := F ∘ pull s⁻¹ 0
  have hm : Interior (T.chamber 0) Z := he.unchanged s⁻¹ 0 (hub_affine S hh _)
  have hr : T.rootTest β Z=T.rootTest β F := root_oriented S hh β _ F he
  have hz (U) : Z (pull s (T.translateBy i) U) = F (translate (anchor S p hh i) U) := by
    unfold Z T
    rw [Function.comp_apply,pull_pull,tile_translate]
    simp only [mul_inv_cancel,affine,Signed.act_zero,zero_add,pull_one]
  classical
  by_cases ht : T.hand i
  · refine ⟨fun x => star (Z x), funext fun x => ?_, hm.real,
      (Work.B15.rootTest_star T β Z).trans hr⟩
    change T.copy i _ _ = _
    unfold Tiling.copy; rw [if_pos ht,star_star]; exact hz x
  refine ⟨Z,funext fun x => ?_,hm,hr⟩; change T.copy i _ _ = _
  unfold Tiling.copy; rw [if_neg ht]; exact hz x

lemma rooted_translates (β : ℝ) (H : Seam G (S.side N p) β) {ι : Type*} [Fintype ι]
    (a : ι → Site (S.side h p)) (hc : Injective a)
    (F : ι → Config G (S.side N p) → ℂ) (hf : ∀ i, Interior ((tilesAt S p hh).chamber 0) (F i)) :
    ‖moment β (fun U => ∏ i, F i (translate (anchor S p hh (a i)) U))‖ ≤ ∏ i, (tilesAt S p hh).rootTest β (F i) := by
  choose W hw he hx using fun i => source_for_translate S hh (a i) (F i) (hf i) β
  simpa only [hw,hx,Function.comp_apply] using (tilesAt S p hh).planted H a hc W he
end YM.Push.GridApprox
